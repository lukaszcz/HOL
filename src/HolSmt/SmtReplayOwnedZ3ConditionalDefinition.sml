structure SmtReplayOwnedZ3ConditionalDefinition :>
    SmtReplayOwnedZ3ConditionalDefinition =
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
  val ERR = Feedback.mk_HOL_ERR "SmtReplayOwnedZ3ConditionalDefinition"
  datatype owner = Owner of
    {work : W.portfolio,marker : unit ref,
     packet : Z.proof Q.packet,frame : Scope.receipt,
     graph : G.graph,root : G.scope,scope : G.scope,
     sources : SmtReplaySource.sources,limits : W.limits,
     epoch : int,symbols : int,check_type : Type.hol_type -> unit}
  structure K = SmtReplayCanonGraph
  val _ = SmtReplayCanonGraph.checked_graph_schema
  datatype plan = Plan of
    {owner : owner,marker : unit ref,id : Z.proof_id,
     definition : G.node,name : G.node,residue : G.node,target : G.node,
     condition : G.node,yes : G.node,no : G.node,
     reverse_yes : bool,reverse_no : bool,ordinary_self : bool,law : G.node,
     guard_dependencies : G.node list,private_dependencies : G.node list,
     guard : unit -> unit,
     spent : bool ref}
  datatype receipt = Receipt of
    {owner : owner,marker : unit ref,id : Z.proof_id,
     definition : G.node,name : G.node,residue : G.node,target : G.node,
     law : G.node,conversion : K.graph_conversion,
     guard_dependencies : G.node list,private_dependencies : G.node list,
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
  fun prepare expected owner id = protected expected (fn () =>
    let
      val Owner {graph,scope,packet,limits,marker,check_type,...} =
        owner_for expected owner
      val proof = Q.proof packet
      fun applicable (Z.Rule {rule,premises,conclusion,arguments,
              metadata,accepts_bind}) =
            #replay_handler rule = "intro_def" andalso null premises andalso
            null arguments andalso not (Option.isSome metadata) andalso
            not accepts_bind andalso #scope conclusion = scope andalso
            (case Z3_Proof.lookup_rule (#z3_version proof) (#name rule) of
               SOME actual => actual = rule | NONE => false)
        | applicable _ = false
      fun ready target = W.with_step expected (fn () =>
        let
          fun valid () = ignore (owner_for expected owner)
          fun pay () = (valid ();W.spend expected 1)
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
          fun operands operator count node =
            (pay ();R.operands graph operator count node)
          val shape = case operands boolSyntax.conjunction 2 target of
              SOME [first,second] =>
                (case (operands boolSyntax.disjunction 2 first,
                       operands boolSyntax.disjunction 2 second) of
                   (SOME [negative,yes],SOME [condition,no]) =>
                     (case (operands boolSyntax.negation 1 negative,
                            R.equality graph yes,R.equality graph no) of
                        (SOME [guard],SOME yes,SOME no) =>
                          if guard = condition then
                            SOME (condition,yes,no) else NONE
                      | _ => NONE)
                 | _ => NONE)
            | _ => NONE
          fun choice ((a,b),(x,y)) =
            let
              fun next [] = NONE
                | next ((name,yes,reverse_yes)::rest) =
                    if not (allocated name) then next rest
                    else if name = x then
                      SOME (name,yes,y,reverse_yes,false)
                    else if name = y then
                      SOME (name,yes,x,reverse_yes,true)
                    else next rest
            in next [(a,b,false),(b,a,true)] end
          fun stage (condition,yes_pair,no_pair) =
            case choice (yes_pair,no_pair) of NONE => NONE
            | SOME (name,yes,no,reverse_yes,reverse_no) =>
              let
                val dependencies = ref ([] : G.node list)
                fun scan node =
                  let
                    val seen = ref (Redblackset.empty Int.compare)
                    val contains = ref false
                    fun visit node =
                      let val _ = pay ()
                          val incoming = G.view graph node
                          val _ = if G.scope_visible graph scope
                              (G.node_scope graph node) then () else
                            raise ERR "prepare" "operand escapes actual frame"
                          val _ = if node = name then contains := true else ()
                      in if Redblackset.member (!seen,G.node_id node) then true
                         else
                           let val _ = seen := Redblackset.add
                                 (!seen,G.node_id node)
                           in case incoming of
                               G.Variable (G.SolverFlexible,_) =>
                                 if allocated node then
                                   (dependencies := node :: !dependencies;
                                    true) else false
                             | G.Variable (G.Bound,_) => false
                             | G.Variable _ => true
                             | G.Constant _ => true
                             | G.Application (operator,operand) =>
                                 visit operator andalso visit operand
                             | _ => false
                           end
                      end
                  in (visit node,!contains) end
                (* The conditional candidate forbids name in either branch.
                   Retain condition dependencies as proof guards separately
                   from the selected executed definition dependencies. *)
                val (condition_ok,_) = scan condition
                val (yes_ok,yes_contains) = scan yes
                val (no_ok,no_contains) = scan no
                val guard_dependencies = List.rev (!dependencies)
              in if not (condition_ok andalso yes_ok andalso no_ok) orelse
                    yes_contains orelse no_contains then NONE
                 else
                   let
                     val ty = G.type_of graph name
                     val _ = if G.type_id graph name = G.type_id graph yes
                         andalso G.type_id graph name = G.type_id graph no
                         andalso Type.compare (G.type_of graph condition,
                           Type.bool) = EQUAL then () else
                       raise ERR "prepare" "conditional operand types differ"
                     val ordinary_self = condition = name andalso
                       Type.compare (ty,Type.bool) = EQUAL andalso
                       (case G.view graph no of G.Constant _ =>
                         Term.same_const (G.representative graph no)
                           boolSyntax.F | _ => false) andalso
                       (case G.view graph yes of
                          G.Variable (G.RigidSource,_) => true | _ => false)
                     val private_dependencies = if ordinary_self then []
                       else List.rev (!dependencies)
                     val cap = #template_limit limits
                     fun bound node =
                       List.app (fn metric =>
                         (pay ();case G.unfolded_nodes graph metric cap node of
                            SOME count => W.spend expected count
                          | NONE => raise ERR "prepare"
                              "actual conditional operand exceeds cap"))
                         [G.RawNodes,G.BinderInclusiveNodes]
                     val _ = List.app bound [target,name,condition,yes,no]
                     fun dimensions node =
                       let fun size metric =
                         (pay ();case G.unfolded_nodes graph metric cap node of
                            SOME count => count
                          | NONE => raise ERR "prepare"
                              "actual conditional operand exceeds cap")
                       in (size G.RawNodes,size G.BinderInclusiveNodes) end
                     val (cr,ci) = dimensions condition
                     val (yr,yi) = dimensions yes
                     val (nr,ni) = dimensions no
                     val future_raw = if ordinary_self then 4 + yr
                       else 8 + cr + yr + nr
                     val future_inclusive = if ordinary_self then 4 + yi
                       else 8 + ci + yi + ni
                     val _ = if future_raw <= cap andalso
                         future_inclusive <= cap then () else
                       raise ERR "prepare"
                         "prospective definition exceeds original cap"
                     val _ = W.spend expected future_raw
                     val _ = W.spend expected future_inclusive
                     fun type_work ty =
                       (pay ();if Type.is_vartype ty then () else
                         List.app type_work (#2 (Type.dest_type ty)))
                     fun funty a b = Type.mk_type ("fun",[a,b])
                     val generated_types =
                       (if ordinary_self then [] else
                         [funty Type.bool (funty ty (funty ty ty)),
                          funty ty (funty ty ty),funty ty ty,ty]) @
                       [funty ty (funty ty Type.bool),
                        funty ty Type.bool,Type.bool]
                     val types = generated_types @ List.map (G.type_of graph)
                       (G.reachable graph [target,name,condition,yes,no])
                     val input_paths = List.map
                       (G.closure_root graph scope)
                       ([target,name,condition,yes,no] @ !dependencies)
                     fun input_guard () =
                       (valid ();List.app (fn path => ignore
                         (G.closure_child_node graph scope path)) input_paths)
                     val _ = List.app type_work types
                     val _ = List.app (fn ty =>
                       (input_guard ();check_type ty;input_guard ())) types
                     val residue = if ordinary_self then yes else
                       let val conditional = Term.inst
                             [{redex = Type.alpha,residue = ty}]
                             boolSyntax.conditional
                       in G.application graph scope
                         (G.application graph scope
                           (G.application graph scope
                             (G.constant graph scope conditional,condition),
                            yes),no) end
                     val definition = equality graph scope (name,residue)
                     val (tr,ti) = dimensions target
                     val law_raw = 3 + future_raw + tr
                     val law_inclusive = 3 + future_inclusive + ti
                     val _ = if law_raw + 4 <= cap andalso
                         law_inclusive + 4 <= cap
                         then () else raise ERR "prepare"
                           "prospective implication exceeds original cap"
                     val _ = W.spend expected (law_raw + 4)
                     val _ = W.spend expected (law_inclusive + 4)
                     val law = implication graph scope definition target
                     val _ = List.app bound [residue,definition,law]
                     val paths = List.map (G.closure_root graph scope)
                       ([target,definition,law,name,residue,condition,yes,no] @
                        !dependencies)
                     fun guard () =
                       (valid ();List.app (fn path => ignore
                         (G.closure_child_node graph scope path)) paths)
                     val _ = guard ()
                   in SOME (Plan {owner = owner,marker = marker,id = id,
                     definition = definition,name = name,residue = residue,
                     target = target,condition = condition,yes = yes,no = no,
                     reverse_yes = reverse_yes,reverse_no = reverse_no,
                     ordinary_self = ordinary_self,law = law,
                     guard_dependencies = guard_dependencies,
                     private_dependencies = private_dependencies,
                     guard = guard,spent = ref false}) end
              end
        in case shape of NONE => NONE | SOME value => stage value end)
    in case Redblackmap.peek (#steps proof,id) of
         SOME (step as Z.Rule {conclusion,...}) =>
           if applicable step then ready (#node conclusion) else NONE
       | _ => NONE end)
  fun execute expected owner (Plan
      {owner = held,marker,id,definition,name,residue,target,condition,yes,no,
       reverse_yes,reverse_no,ordinary_self,law,guard_dependencies,
       private_dependencies,guard,spent}) =
    protected expected (fn () =>
      let
        val _ = same_owner expected owner held marker
        val Owner {graph,scope,limits,check_type,...} =
          owner_for expected owner
        val _ = guard ()
      in W.with_step expected (fn () =>
        let
          val _ = guard ()
          val _ = if !spent then raise ERR "execute" "plan already executed"
            else spent := true
          val cap = #template_limit limits
          val ty = G.type_of graph name
          fun funty a b = Type.mk_type ("fun",[a,b])
          datatype shape = Typed of Type.hol_type * shape list
          fun atom ty = Typed (ty,[])
          fun apply result operator operand =
            Typed (result,[operator,operand])
          fun binary operator left_ty right_ty result left right =
            apply result
              (apply (funty right_ty result) (atom operator) left) right
          val a = atom ty
          val c = atom Type.bool
          fun eq x y = binary (funty ty (funty ty Type.bool))
            ty ty Type.bool x y
          fun boolean x y = binary
            (funty Type.bool (funty Type.bool Type.bool))
            Type.bool Type.bool Type.bool x y
          fun neg x = apply Type.bool
            (atom (funty Type.bool Type.bool)) x
          fun cond result x y = apply result
            (apply (funty result result)
              (apply (funty result (funty result result))
                (atom (funty Type.bool
                  (funty result (funty result result)))) c) x) y
          fun closed_eq x y = boolean x y
          val source_shape = eq a (cond ty a a)
          val rand_shape = cond Type.bool (eq a a) (eq a a)
          val expanded_shape = boolean
            (boolean c (eq a a)) (boolean (neg c) (eq a a))
          val intermediate_shape = boolean
            (boolean (neg c) (eq a a))
            (boolean (neg (neg c)) (eq a a))
          val result_shape = boolean
            (boolean (neg c) (eq a a)) (boolean c (eq a a))
          (* Fixed rewrite contexts include the double-negation intermediate,
             before any public conversion. Each individual syntax portfolio
             uses the existing template cap. Repeated annotations are paid
             to original Work, with no syntax-derived total type quota. *)
          val conditional_portfolios =
            [closed_eq source_shape rand_shape,
             closed_eq rand_shape expanded_shape,
             closed_eq expanded_shape intermediate_shape,
             closed_eq intermediate_shape intermediate_shape,
             closed_eq intermediate_shape result_shape,
             closed_eq result_shape result_shape,
             closed_eq source_shape result_shape,
             source_shape,result_shape,boolean source_shape result_shape,
             closed_eq (boolean source_shape result_shape) c]
          val ordinary_definition = eq a a
          val ordinary_first = boolean (neg c) ordinary_definition
          val ordinary_second = boolean c (eq a c)
          val excluded_shape = boolean c (neg c)
          val ordinary_target = boolean ordinary_first ordinary_second
          val ordinary_law = boolean ordinary_definition ordinary_target
          val portfolios = if ordinary_self then
            [ordinary_definition,ordinary_first,ordinary_second,
             closed_eq (eq a c) (neg c),excluded_shape,
             closed_eq ordinary_second excluded_shape,ordinary_target,
             ordinary_law,closed_eq ordinary_law c]
            else conditional_portfolios
          val types = ref ([] : Type.hol_type list)
          fun type_work ty =
            (guard ();W.spend expected 1;
             if Type.is_vartype ty then () else
               List.app type_work (#2 (Type.dest_type ty)))
          fun quote (Typed (ty,children)) =
            let val _ = guard ()
                val _ = W.spend expected 2
                val _ = type_work ty
                val _ = types := ty :: !types
            in 1 + List.foldl (fn (child,total) => quote child + total)
              0 children end
          val _ = List.app (fn tree => if quote tree <= cap then () else
            raise ERR "execute" "prospective fixed proof exceeds cap")
            portfolios
          val _ = List.app (fn ty =>
            (guard ();check_type ty;guard ())) (List.rev (!types))
          val n = Term.genvar ty
          val c = Term.genvar Type.bool
          val x = Term.genvar ty
          val y = Term.genvar ty
          fun right theorem = #2 (boolSyntax.dest_eq (Thm.concl theorem))
          val (theorem,holes,operands) = if ordinary_self then
            let
              val definition_term = boolSyntax.mk_eq (n,x)
              val assumed = Thm.ASSUME definition_term
              val branch = if reverse_yes then Thm.SYM assumed else assumed
              val first = Thm.DISJ2 (boolSyntax.mk_neg n) branch
              val false_branch = if reverse_no then
                  boolSyntax.mk_eq (boolSyntax.F,n)
                else boolSyntax.mk_eq (n,boolSyntax.F)
              val second_term = boolSyntax.mk_disj (n,false_branch)
              val second_bridge = Conv.RAND_CONV
                (Rewrite.PURE_REWRITE_CONV [boolTheory.EQ_CLAUSES])
                second_term
              val excluded = Thm.SPEC n boolTheory.EXCLUDED_MIDDLE
              val second = Thm.EQ_MP (Thm.SYM second_bridge) excluded
              val closed = Thm.DISCH definition_term (Thm.CONJ first second)
            in (Drule.EQT_INTRO closed,[n,x],[name,yes]) end
            else
            let
              val input = boolSyntax.mk_eq (n,boolSyntax.mk_cond (c,x,y))
              val first = Conv.REWR_CONV boolTheory.COND_RAND input
              val second = Conv.REWR_CONV boolTheory.COND_EXPAND_IMP
                (right first)
              val third = Rewrite.PURE_REWRITE_CONV
                [boolTheory.IMP_DISJ_THM,boolTheory.NOT_CLAUSES] (right second)
              val base = Thm.TRANS first (Thm.TRANS second third)
              val yes_orientation = if reverse_yes then
                  Conv.LAND_CONV (Conv.RAND_CONV
                    (Conv.REWR_CONV boolTheory.EQ_SYM_EQ)) (right base)
                else Thm.REFL (right base)
              val no_orientation = if reverse_no then
                  Conv.RAND_CONV (Conv.RAND_CONV
                    (Conv.REWR_CONV boolTheory.EQ_SYM_EQ))
                    (right yes_orientation)
                else Thm.REFL (right yes_orientation)
              val equality = Thm.TRANS base
                (Thm.TRANS yes_orientation no_orientation)
              val closed = Thm.DISCH input
                (Thm.EQ_MP equality (Thm.ASSUME input))
            in (Drule.EQT_INTRO closed,[n,c,x,y],
                [name,condition,yes,no]) end
          val _ = guard ()
          val schema = K.checked_graph_schema graph scope
            {theorem = theorem,holes = holes,operands = operands,
             template_limit = cap}
          val _ = if K.graph_schema_source schema = law andalso
              Term.same_const
                (G.representative graph (K.graph_schema_result schema))
                boolSyntax.T then () else
            raise ERR "execute" "fixed conditional schema endpoints differ"
          val conversion = K.graph_conversion graph scope false
            (fn node => if node = law then SOME schema else NONE)
            law
          val _ = K.validate_conversion_for expected conversion
          val _ = if K.graph_source conversion = law andalso
              Term.same_const (G.representative graph
                (K.graph_result conversion)) boolSyntax.T then () else
            raise ERR "execute" "conditional conversion endpoints differ"
          val _ = guard ()
        in Receipt {owner = owner,marker = marker,id = id,
          definition = definition,name = name,residue = residue,
          target = target,law = law,
          conversion = conversion,guard_dependencies = guard_dependencies,
          private_dependencies = private_dependencies,
          guard = guard} end)
      end)
  fun describe_for expected owner (Receipt
      {owner = held,marker,id,definition,name,residue,target,law,conversion,
       guard_dependencies,private_dependencies,guard}) =
    protected expected (fn () =>
    let
      val _ = same_owner expected owner held marker
      val Owner {frame,...} = owner_for expected owner
      val _ = guard ()
      val _ = K.validate_conversion_for expected conversion
    in {frame = frame,proof_id = id,definition = definition,name = name,
      residue = residue,target = target,law = law,conversion = conversion,
      guard_dependencies = guard_dependencies,
      private_dependencies = private_dependencies} end)
end
