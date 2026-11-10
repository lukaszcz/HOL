structure SmtReplayOwnedZ3GroundDefinition :>
    SmtReplayOwnedZ3GroundDefinition =
struct
  structure G = SmtReplayGraph
  structure W = SmtReplayInvocationWork
  structure Q = SmtLib_GraphProof
  structure Z = Z3_GraphProofParser
  structure Scope = SmtReplayOwnedScopeReceipt
  structure P = SmtReplayProof
  structure R = SmtReplayRules
  val _ = Z3_GraphProofParser.create_packet
  val _ = SmtReplayRules.equality
  val _ = SmtReplayInvocationWork.validate
  val _ = SmtReplayOwnedScopeReceipt.description_for
  val _ = SmtLib_GraphProof.proof
  val _ = SmtReplayProof.record_closed
  val _ = SmtReplayGraph.closure_root
  val ERR = Feedback.mk_HOL_ERR "SmtReplayOwnedZ3GroundDefinition"
  datatype owner = Owner of
    {work : W.portfolio,marker : unit ref,
     packet : Z.proof Q.packet,frame : Scope.receipt,
     graph : G.graph,root : G.scope,scope : G.scope,
     sources : SmtReplaySource.sources,limits : W.limits,
     epoch : int,symbols : int,check_type : Type.hol_type -> unit}
  datatype plan = Plan of
    {owner : owner,marker : unit ref,id : Z.proof_id,
     definition : G.node,name : G.node,residue : G.node,
     target : G.node,law : G.node,reverse : bool,
     definition_term : Term.term,target_term : Term.term,
     law_term : Term.term,private_dependencies : G.node list,
     guard : unit -> unit,spent : bool ref}
  datatype receipt = Receipt of
    {owner : owner,marker : unit ref,id : Z.proof_id,
     definition : G.node,name : G.node,residue : G.node,target : G.node,
     law : P.closed_fact,private_dependencies : G.node list,
     guard : unit -> unit}
  fun protected expected action = action ()
    handle error => (W.close expected;raise error)
  fun owner_for expected (owner as Owner
      {work,packet,frame,graph,root,scope,sources,limits,epoch,symbols,...}) =
    protected expected (fn () =>
      let
        (* Expected portfolio precedes held frame/graph activation. *)
        val _ = if Portable.pointer_eq (expected,work) then () else
          raise ERR "owner_for" "different original Work"
        val _ = if Portable.pointer_eq (Q.graph packet,graph) andalso
            Q.scope packet = root then () else
          raise ERR "owner_for" "different parser owner"
        val data = Scope.description_for expected frame
        val _ = if Portable.pointer_eq (#graph data,graph) andalso
            #root data = root andalso #scope data = scope andalso
            Portable.pointer_eq (#sources data,sources) then () else
          raise ERR "owner_for" "different original parser frame"
        val _ = W.validate expected graph root sources limits
        val _ = if Type.type_epoch () = epoch andalso
            Term.term_epoch () = symbols then () else
          raise ERR "owner_for" "retirement epoch changed"
      in owner end)
  fun same_owner expected owner held marker =
    let val Owner {marker = wanted,...} = owner in
      if Portable.pointer_eq (owner,held) andalso
          Portable.pointer_eq (wanted,marker) then () else
        (W.close expected;raise ERR "owner" "different retained producer")
    end
  fun begin work {packet,frame,check_type} = protected work (fn () =>
    let
      val original = W.original_sources work
      val graph = SmtReplaySource.owning_graph original
      val root = SmtReplaySource.owning_scope original
      val _ = if Portable.pointer_eq (Q.graph packet,graph) andalso
          Q.scope packet = root andalso Q.solver packet = "Z3" then () else
        raise ERR "begin" "different original parser packet"
      val data = Scope.description_for work frame
      val _ = if Portable.pointer_eq (#graph data,graph) andalso
          #root data = root andalso
          Portable.pointer_eq (#sources data,original) then () else
        raise ERR "begin" "different original Scope receipt"
      val limits = W.semantic_limits work
      val _ = W.validate work graph root original limits
    in Owner {work = work,marker = ref (),packet = packet,frame = frame,
      graph = graph,root = root,scope = #scope data,sources = original,
      limits = limits,epoch = Type.type_epoch (),
      symbols = Term.term_epoch (),check_type = check_type} end)
  fun equality graph scope (left,right) =
    let
      val marker = Term.genvar (G.type_of graph left)
      val head = Term.rator (Term.rator (boolSyntax.mk_eq (marker,marker)))
    in G.application graph scope
      (G.application graph scope (G.constant graph scope head,left),right) end
  fun implication graph scope left right = G.application graph scope
    (G.application graph scope
      (G.constant graph scope boolSyntax.implication,left),right)
  fun prepare_equation allow_dependencies expected owner id =
    protected expected (fn () =>
    let
      val Owner {graph,scope,packet,limits,marker,check_type,...} =
        owner_for expected owner
      val proof = Q.proof packet
      val selected = Redblackmap.peek (#steps proof,id)
      fun applicable (Z.Rule {rule,premises,conclusion,arguments,
              metadata,accepts_bind}) =
            #replay_handler rule = "intro_def" andalso
            null premises andalso null arguments andalso
            not (Option.isSome metadata) andalso not accepts_bind andalso
            #scope conclusion = scope andalso
            (case Z3_Proof.lookup_rule (#z3_version proof) (#name rule) of
               SOME actual => actual = rule | NONE => false)
        | applicable _ = false
      fun ready target = W.with_step expected (fn () =>
        let
          fun valid () = ignore (owner_for expected owner)
          fun pay () = (valid ();W.spend expected 1)
          val _ = pay ()
          val pair = R.equality graph target
          fun allocated node =
            (pay ();
             List.exists (fn current => (pay ();current = node)) (#vars proof)
             andalso List.exists
               (fn value : SmtLib_GraphFrontend.solver_variable =>
                 (pay ();#node value = node andalso
                  G.node_scope graph node = #scope value))
               (Q.variables packet) andalso
             (case G.view graph node of
                G.Variable (G.SolverFlexible,_) => true | _ => false))
          val private_dependencies = ref ([] : G.node list)
          fun public_residue node =
            let
              val seen = ref (Redblackset.empty Int.compare)
              fun visit node =
                let val _ = pay ()
                    val incoming = G.view graph node
                    val _ = if G.scope_visible graph scope
                        (G.node_scope graph node) then () else
                      raise ERR "prepare" "residue escapes actual frame"
                in if Redblackset.member (!seen,G.node_id node) then true
                   else
                     let val _ = seen := Redblackset.add
                           (!seen,G.node_id node)
                     in case incoming of
                         G.Variable (G.SolverFlexible,_) =>
                           if allow_dependencies andalso allocated node then
                             (private_dependencies :=
                                node :: !private_dependencies;true)
                           else false
                       | G.Variable (G.Bound,_) => false
                       | G.Variable _ => true
                       | G.Constant _ => true
                       | G.Application (operator,operand) =>
                           visit operator andalso visit operand
                       | _ => false
                     end
                end
            in visit node end
          val endpoints = case pair of NONE => NONE
            | SOME (left,right) =>
                if allocated left andalso public_residue right then
                  (* Exact Library.is_def_oriented private-variable case.
                     The stored smaller variable is the established name. *)
                  if allow_dependencies andalso allocated right andalso
                      (pay ();Term.var_compare
                        (G.representative graph right,
                         G.representative graph left) = LESS) then
                    SOME (right,left,true)
                  else SOME (left,right,false)
                else if allocated right andalso public_residue left then
                  SOME (right,left,true) else NONE
          val endpoints = if not allow_dependencies then endpoints else
            case endpoints of NONE => NONE
            | SOME (name,residue,reverse) =>
              let val _ = private_dependencies := []
                  val ready = public_residue residue
              in if ready andalso not (List.exists (fn dependency =>
                    dependency = name) (!private_dependencies)) then
                  SOME (name,residue,reverse) else NONE end
        in case endpoints of NONE => NONE
          | SOME (name,residue,reverse) =>
            let
              (* Public-ground orientation remains exact. The separate
                 private mode applies the actual legacy variable order. *)
              val definition = equality graph scope (name,residue)
              val law = implication graph scope definition target
              val alignment = equality graph scope (law,law)
              val cap = #template_limit limits
              fun bound node =
                (pay ();
                 List.app (fn metric =>
                   (pay ();
                    case G.unfolded_nodes graph metric cap node of
                      SOME count => if count <= cap then () else
                        raise ERR "prepare" "actual proof shape exceeds cap"
                    | NONE => raise ERR "prepare"
                        "actual proof shape has an unadmitted binder"))
                   [G.RawNodes,G.BinderInclusiveNodes])
              (* Actual fixed ASSUME, optional SYM, then DISCH portfolios.
                 Conclusions and surviving hypotheses stay independently
                 bounded, with repeated type traversal charged to SAME W. *)
              val portfolio = [definition,definition,definition] @
                (if reverse then [definition,target,definition] else []) @
                [definition,target,definition,law,law,alignment,law]
              val _ = List.app bound portfolio
              (* P.record_closed retains this ORIGINAL independent record
                 contract. Reproduce its exact existing type-shape gate
                 prospectively; this is not a new raw traversal quota. *)
              val closed_types = List.map (G.type_of graph)
                (G.reachable graph [law])
              val remaining = ref cap
              fun record_shapes [] = ()
                | record_shapes (ty::rest) =
                    (pay ();
                     if !remaining = 0 then raise ERR "prepare"
                       "existing closed-record type portfolio exceeds cap"
                     else remaining := !remaining-1;
                     record_shapes ((if Type.is_vartype ty then []
                       else #2 (Type.dest_type ty)) @ rest))
              val _ = record_shapes closed_types
              val paths = List.map (G.closure_root graph scope)
                ([target,definition,name,residue,law,alignment] @
                 List.rev (!private_dependencies))
              fun guard () =
                (valid ();
                 List.app (fn path => ignore
                   (G.closure_child_node graph scope path)) paths)
              val definition_term = G.representative graph definition
              val target_term = G.representative graph target
              val law_term = G.representative graph law
              (* All terms above are fully realized binder-free operands.
                 No total annotation quota is derived from a syntax cap. *)
              val types = ref ([] : Type.hol_type list)
              fun type_shape ty =
                (pay ();
                 if Type.is_vartype ty then () else
                   List.app type_shape (#2 (Type.dest_type ty)))
              fun term_types term =
                (pay ();
                 let val ty = Term.type_of term
                     val _ = type_shape ty
                     val _ = types := ty :: !types
                 in if Term.is_comb term then
                      let val (operator,operand) = Term.dest_comb term
                      in term_types operator;term_types operand end
                    else if Term.is_abs term then
                      raise ERR "prepare" "fixed equation contains a binder"
                    else () end)
              val _ = List.app (term_types o G.representative graph) portfolio
              val _ = List.app (fn ty =>
                (guard ();check_type ty;guard ())) (List.rev (!types))
              val _ = guard ()
            in SOME (Plan {owner = owner,marker = marker,id = id,
              definition = definition,name = name,residue = residue,
              target = target,law = law,reverse = reverse,
              definition_term = definition_term,target_term = target_term,
              law_term = law_term,
              private_dependencies = List.rev (!private_dependencies),
              guard = guard,spent = ref false}) end
        end)
    in case selected of SOME (step as Z.Rule {conclusion,...}) =>
         if applicable step then ready (#node conclusion) else NONE
       | _ => NONE end)
  fun prepare expected owner id = prepare_equation false expected owner id
  fun prepare_dependent_equation expected owner id =
    prepare_equation true expected owner id
  fun execute expected owner (Plan
      {owner = held,marker,id,definition,name,residue,target,law,reverse,
       definition_term,target_term,law_term,private_dependencies,
       guard,spent}) =
    protected expected (fn () =>
      let
        val _ = same_owner expected owner held marker
        val Owner {graph,scope,check_type,limits,...} =
          owner_for expected owner
        val _ = guard ()
      in W.with_step expected (fn () =>
        let
          val _ = guard ()
          val _ = if !spent then raise ERR "execute" "plan already executed"
            else spent := true
          val _ = W.spend expected 1
          val assumed = Thm.ASSUME definition_term
          val result = if reverse then Thm.SYM assumed else assumed
          val _ = if Portable.pointer_eq (Thm.concl result,target_term) then ()
            else if Term.aconv (Thm.concl result) target_term then () else
              raise ERR "execute" "actual fixed rule target differs"
          val conditional = Thm.DISCH definition_term result
          val exact = Thm.EQ_MP
            (Thm.ALPHA (Thm.concl conditional) law_term) conditional
          val _ = guard ()
          val closed = P.record_closed graph scope
            {node = law,theorem = exact,
             template_limit = #template_limit limits,
             check_type = fn ty => (guard ();check_type ty;guard ())}
          val _ = guard ()
          (* This receipt is minted ONLY after this actual definition proof;
             spelling/packet metadata alone never promotes a Source slot. *)
        in Receipt {owner = owner,marker = marker,id = id,
          definition = definition,name = name,residue = residue,
          target = target,law = closed,
          private_dependencies = private_dependencies,guard = guard} end)
      end)
  fun description_for expected owner (Receipt
      {owner = held,marker,id,definition,name,residue,target,law,guard,...}) =
    protected expected (fn () =>
      let val _ = same_owner expected owner held marker
          val Owner {frame,...} = owner_for expected owner
          val _ = guard ()
          val _ = ignore (P.closed_node law)
      in {frame = frame,proof_id = id,definition = definition,name = name,
        residue = residue,target = target,law = law} end)
  fun private_dependencies_for expected owner (Receipt
      {owner = held,marker,private_dependencies,guard,law,...}) =
    protected expected (fn () =>
      let val _ = same_owner expected owner held marker
          val _ = ignore (owner_for expected owner)
          val _ = guard ()
          val _ = ignore (P.closed_node law)
      in private_dependencies end)

end
