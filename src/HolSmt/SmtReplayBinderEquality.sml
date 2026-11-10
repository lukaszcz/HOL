(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayBinderEquality :> SmtReplayBinderEquality =
struct
  open SmtReplayGraph SmtReplayProof SmtReplayBinder
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure H = SmtReplaySourceHypAdmission
  val ERR = Feedback.mk_HOL_ERR "SmtReplayBinderEquality"
  type arguments =
    {scope : G.scope,parent_scope : G.scope,variables : G.node list,
     body : G.node,target : G.node,block : P.block,edge : P.edge,
     witnesses : (int * G.node -> Thm.thm option) option,
     canonical_sources : G.node list,admission : SmtReplayBinder.admission,
     close : unit -> unit}
  datatype kind = datatype SmtReplayBinderClose.kind
  fun clean theorem =
    let val (tags,_) = Tag.dest_tag (Thm.tag theorem) in
      List.all (fn tag => tag = "DISK_THM") tags andalso
      List.null (Tag.axioms_of (Thm.tag theorem)) end
  fun indexed action values = ListPair.map action
    (List.tabulate (List.length values,fn index => index),values)

  fun operands graph constant count node =
    let
      fun spine node arguments = case G.view graph node of
          G.Application (operator,operand) =>
            spine operator (operand :: arguments)
        | G.Constant _ =>
            if Term.same_const (G.representative graph node) constant andalso
                List.length arguments = count then SOME arguments else NONE
        | _ => NONE
    in spine node [] end
  fun equality graph node = case operands graph boolSyntax.equality 2 node of
      SOME [left,right] => SOME (left,right) | _ => NONE

  fun close_equality_core graph source_admissions
      {scope,parent_scope,variables,body,target,block,edge,witnesses,
       canonical_sources,
       admission = {metric,input_limit,output_limit,check_type,refuse},close} =
    let
      val _ = G.validate_scope graph scope
      val _ = G.validate_scope graph parent_scope
      val _ = if P.scope block = scope andalso not (List.null variables)
        then () else raise ERR "close_equality" "wrong or empty binder frame"
      val _ = if input_limit >= 0 andalso output_limit >= 0 then () else
        raise ERR "close_equality" "invalid binder admission limits"
      fun refusal reason = (refuse reason;
        raise ERR "close_equality" ("binder admission refused: " ^ reason))
      fun admitted label limit node =
        case G.unfolded_nodes graph metric limit node of
          SOME size => if size <= limit then size else
            (refusal label;raise Fail "unreachable binder refusal")
        | NONE => (refusal label;raise Fail "unreachable binder refusal")
      val _ = ignore (P.name block body)
      val _ = ignore (admitted "binder input" input_limit body)
      val _ = ignore (admitted "binder output" output_limit target)
      val _ = if G.scope_visible graph parent_scope
          (G.node_scope graph target) then () else
        raise ERR "close_equality" "target escapes parent scope"
      val variable_ids = Redblackset.addList (Redblackset.empty Int.compare,
        List.map G.node_id variables)
      val _ = if Redblackset.numItems variable_ids = List.length variables
        then () else raise ERR "close_equality" "duplicate binder annotation"
      val _ = List.app (fn variable =>
        case G.view graph variable of G.Variable (G.Bound,_) =>
            if G.scope_visible graph scope (G.node_scope graph variable)
            then () else raise ERR "close_equality" "foreign binder variable"
          | _ => raise ERR "close_equality" "annotation is not a Bound node")
        variables
      val parents = parent_scope :: List.map (G.node_scope graph)
        (List.take (variables,List.length variables-1))
      val _ = List.app (fn (variable,parent) =>
        if G.scope_visible graph (G.node_scope graph variable) parent then ()
        else raise ERR "close_equality" "binder frames are out of order")
        (ListPair.zip (variables,parents))
      val (left,right) = case equality graph target of SOME pair => pair
        | NONE => raise ERR "close_equality" "target is not an equality"
      val _ = case equality graph body of SOME _ => ()
        | NONE => raise ERR "close_equality" "body is not an equality"
      fun abstraction node = case G.view graph node of
          G.AdmittedBinder {binder,body,...} => SOME (binder,body)
        | _ => NONE
      fun quantified constant node =
        case operands graph constant 1 node of
          SOME [node] => abstraction node | _ => NONE
      fun peel_node node = case quantified boolSyntax.universal node of
          SOME pair => SOME (Forall,pair)
        | NONE => (case quantified boolSyntax.existential node of
            SOME pair => SOME (Exists,pair)
          | NONE => Option.map (fn pair => (Lambda,pair)) (abstraction node))
      fun peel [] node = ([],node)
        | peel (annotated :: rest) node =
            (case peel_node node of NONE => raise ERR "close_equality"
                 "target has fewer binders than its annotation"
             | SOME (kind,(variable,body)) =>
                 if G.type_id graph annotated = G.type_id graph variable then
                   let val (entries,residue) = peel rest body in
                     ((kind,variable) :: entries,residue) end
                 else raise ERR "close_equality" "binder type mismatch")
      val (left_entries,left_body) = peel variables left
      val (right_entries,right_body) = peel variables right
      val _ = List.app (fn ((left,_),(right,_)) =>
        if left = right then () else raise ERR "close_equality"
          "target binder kinds differ") (ListPair.zip
            (left_entries,right_entries))

      (* Source witnesses are inspected while all their endpoints remain
         graph metadata. Unknown dependencies never certify absence. *)
      val sources = P.sources block
      val buckets = 4093
      val hint = SmtReplayImport.pointer_bucket 4 buckets
      val source_index = Array.array (buckets,[])
      val _ = List.app (fn node =>
        let val term = G.representative graph node val bucket = hint term in
          Array.update (source_index,bucket,
            (term,node) :: Array.sub (source_index,bucket)) end) sources
      fun canonical hypothesis =
        case List.find (fn (term,_) => Portable.pointer_eq (term,hypothesis))
            (Array.sub (source_index,hint hypothesis)) of
          SOME (_,node) => node
        | NONE => raise ERR "close_equality" "noncanonical source hypothesis"
      val chosen = Vector.fromList (indexed (fn (index,node) =>
        case witnesses of NONE => NONE | SOME supply =>
          case supply (index,node) of NONE => NONE | SOME theorem =>
            if Portable.pointer_eq (Thm.concl theorem,
                G.representative graph node) andalso clean theorem then
              SOME theorem else raise ERR "close_equality"
                "invalid source witness") sources)
      val hypotheses = List.concat (indexed (fn (index,node) =>
        case Vector.sub (chosen,index) of NONE => [node]
          | SOME theorem => List.map canonical (Thm.hyp theorem)) sources)
      val seen_hypotheses = ref (Redblackset.empty Int.compare)
      val captures = ref ([] :
        (G.node * G.node list * G.node * H.certificate option) list)
      val overhead = case metric of G.RawNodes => 3
        | G.BinderInclusiveNodes => 4
      fun local_admission output : SmtReplayBinder.admission =
        {metric = metric,input_limit = input_limit,output_limit = output,
         check_type = check_type,refuse = refuse}
      fun certified node certificate output = H.check certificate
        {source = node,scope = scope,variables = variables,
         admission = local_admission output}
      fun hypothesis_metadata node =
        let
          fun unknown () = case source_admissions of NONE =>
              (ignore (admitted "binder hypothesis" input_limit node);
               refusal "unknown binder hypothesis dependency";
               raise Fail "unreachable binder refusal")
            | SOME supply =>
                let
                  (* Membership precedes the certificate callback, even
                     for an unwitnessed occurrence. Never add a Source. *)
                  val exact = canonical (G.representative graph node)
                  val _ = if exact = node then () else
                    raise ERR "close_equality" "ambiguous canonical Source"
                  val certificate = case supply node of SOME value => value
                    | NONE => (refusal "missing hypothesis certificate";
                        raise Fail "unreachable binder refusal")
                  val view = certified node certificate output_limit
                in (#admitted view,#free_variables view,SOME certificate) end
        in case G.unfolded_nodes graph metric input_limit node of
            NONE => unknown ()
          | SOME _ =>
              (ignore (admitted "binder hypothesis" input_limit node);
               case G.free_variable_nodes graph node of
                 SOME free => (node,free,NONE) | NONE => unknown ()) end
      fun hypothesis node =
        if Redblackset.member (!seen_hypotheses,G.node_id node) then () else
          let
            val _ = seen_hypotheses := Redblackset.add
              (!seen_hypotheses,G.node_id node)
            val (metadata,free,certificate) = hypothesis_metadata node
            val _ = ignore (admitted "binder hypothesis" input_limit metadata)
            val _ = List.app (fn variable =>
              if Redblackset.member (variable_ids,G.node_id variable) orelse
                  G.scope_visible graph parent_scope
                    (G.node_scope graph variable) then () else
                raise ERR "close_equality"
                  "hypothesis contains an unannotated local variable") free
            val captured = List.filter (fn variable =>
              List.exists (fn node => node = variable) free) variables
            val _ = if List.length captured <= output_limit div overhead
              then () else refusal "binder hypothesis closure"
            val _ = ignore (admitted "binder hypothesis closure"
              (output_limit-overhead*List.length captured) metadata)
            val _ = case certificate of NONE => ()
              | SOME evidence =>
                  let
                    val count = List.length captured
                    val _ = if count <= output_limit div (2*overhead)
                      then () else refusal "whole hypothesis closure bridge"
                    val _ = ignore (certified node evidence
                      (output_limit-2*overhead*count))
                    val _ = if null captured andalso not
                        (G.scope_visible graph parent_scope
                          (G.node_scope graph node)) then
                      refusal "uncaptured opaque Source escapes parent"
                      else ()
                  in () end
          in captures := (node,captured,metadata,certificate) :: !captures end
      val _ = List.app hypothesis hypotheses
      val _ = case G.free_variable_nodes graph body of NONE =>
          refusal "unknown binder body dependency"
        | SOME free => List.app (fn variable =>
            if Redblackset.member (variable_ids,G.node_id variable) orelse
                G.scope_visible graph parent_scope
                  (G.node_scope graph variable) then () else
              raise ERR "close_equality"
                "body contains an unannotated local variable") free
      val types = ref (Redblackset.empty Int.compare)
      val _ = List.app (fn node =>
        let val id = G.type_id graph node in
          if Redblackset.member (!types,id) then () else
            (types := Redblackset.add (!types,id);
             check_type (G.type_of graph node))
        end) (G.reachable graph (body :: target :: variables @ hypotheses))
      val _ = List.app (fn variable => check_type
        (Type.mk_type ("fun",[Type.mk_type ("fun",
          [G.type_of graph variable,Type.bool]),Type.bool]))) variables
      val annotation = List.map (G.representative graph) variables
      fun renamed entries residue = Term.subst
        (ListPair.map (fn ((_,variable),annotation) =>
          {redex = G.representative graph variable,residue = annotation})
          (entries,annotation)) (G.representative graph residue)
      val expected = boolSyntax.mk_eq
        (renamed left_entries left_body,renamed right_entries right_body)
      val _ = ignore (Thm.ALPHA (G.representative graph body) expected)

      (* These are bounded local source closures, not scans of an original
         large root. Candidate equality is attempted only after admission. *)
      fun candidate node =
        if G.scope_visible graph parent_scope (G.node_scope graph node) then
          let val term = G.representative graph node in
            case G.unfolded_nodes graph metric output_limit node of
              SOME size => if size <= output_limit then SOME (node,term)
                else NONE
            | NONE => (case (case metric of G.RawNodes =>
                  SmtReplayImport.bounded_raw_size output_limit term
                | G.BinderInclusiveNodes =>
                  SmtReplayImport.bounded_binder_size output_limit term) of
                SOME _ => SOME (node,term) | NONE => NONE)
          end else NONE
      val candidates = List.mapPartial candidate canonical_sources
      fun candidate_types [] = ()
        | candidate_types (term :: rest) =
            (check_type (Term.type_of term);
             if Term.is_comb term then
               let val (operator,operand) = Term.dest_comb term in
                 candidate_types (operator :: operand :: rest) end
             else if Term.is_abs term then
               let val (variable,body) = Term.dest_abs term in
                 candidate_types (variable :: body :: rest) end
             else candidate_types rest)
      val _ = case source_admissions of NONE =>
          List.app (fn (_,term) => candidate_types [term]) candidates
        | SOME _ => ()
      fun align_term node closed =
        let fun search [] = NONE
              | search ((candidate,term) :: rest) =
                  (let
                     val _ = case source_admissions of NONE => ()
                       | SOME _ =>
                           let
                             val equation = boolSyntax.mk_eq (closed,term)
                             val bounded = case metric of G.RawNodes =>
                                 SmtReplayImport.bounded_raw_size
                                   output_limit equation
                               | G.BinderInclusiveNodes =>
                                 SmtReplayImport.bounded_binder_size
                                   output_limit equation
                             val _ = case bounded of SOME _ => ()
                               | NONE => raise ERR "close_equality"
                                   "whole candidate bridge exceeds quota"
                             val _ = candidate_types [equation]
                             val free = case
                                 G.free_variable_nodes graph node of
                                   SOME free => free
                                 | NONE => raise ERR "close_equality"
                                     "unknown closed hypothesis free IDs"
                             val expected = case
                                 G.free_variable_nodes graph candidate of
                                   SOME expected => expected
                                 | NONE => if null free andalso
                                     null (Term.free_vars term) then [] else
                                     let
                                       val exact = canonical term
                                       val _ = if exact = candidate then ()
                                         else raise ERR "close_equality"
                                           "ambiguous canonical candidate"
                                       val evidence = case source_admissions
                                           of SOME supply => supply candidate
                                            | NONE => NONE
                                       val evidence = case evidence of
                                           SOME evidence => evidence
                                         | NONE => raise ERR "close_equality"
                                             "uncertified scoped candidate"
                                       val view = certified candidate evidence
                                         output_limit
                                     in #free_variables view end
                             val _ = if List.length expected =
                                 List.length free andalso
                                 List.all (fn variable =>
                                   List.exists (fn other =>
                                     other = variable) expected) free
                               then () else raise ERR "close_equality"
                                 "candidate free IDs differ"
                           in () end
                   in SOME (candidate,Thm.ALPHA closed term) end)
                  handle Feedback.HOL_ERR _ => search rest
        in search candidates end
      fun align node =
        case align_term node (G.representative graph node) of
            SOME result => result
          | NONE => (node,Thm.REFL (G.representative graph node))
      fun closure_node node variables =
        let
          fun close (index,variable,result) =
            let
              val outer = if index = 0 then parent_scope
                else G.node_scope graph (List.nth (variables,index-1))
              val abstraction = G.abstraction graph outer output_limit
                (variable,result)
              val operator = Term.rator (boolSyntax.mk_forall
                (G.representative graph variable,boolSyntax.T))
            in G.application graph outer
              (G.constant graph outer operator,abstraction) end
          val entries = indexed (fn (index,variable) => (index,variable))
            variables
        in if null variables then #node (G.rehome graph parent_scope node)
          else List.foldr (fn ((index,variable),result) =>
            close (index,variable,result)) node entries end
      fun whole_bridge original canonical =
        let
          val law = boolSyntax.mk_eq (original,
            G.representative graph canonical)
          val bounded = case metric of G.RawNodes =>
              SmtReplayImport.bounded_raw_size output_limit law
            | G.BinderInclusiveNodes =>
              SmtReplayImport.bounded_binder_size output_limit law
        in case bounded of SOME _ => ()
          | NONE => refusal "whole hypothesis closure bridge" end
      val closures = List.map (fn (node,captured,metadata,certificate) =>
        let
          val annotation = List.map (G.representative graph) captured
          val original = boolSyntax.list_mk_forall
            (annotation,G.representative graph node)
          val (canonical,bridge) = case certificate of
              SOME evidence => if null captured then
                (whole_bridge (G.representative graph node) node;
                 (node,Thm.REFL (G.representative graph node)))
                else
                  let
                    val view = certified node evidence
                      (output_limit-2*overhead*List.length captured)
                    val owned = closure_node metadata captured
                    val prospective_admitted = boolSyntax.list_mk_forall
                      (annotation,G.representative graph metadata)
                    val _ = whole_bridge prospective_admitted owned
                    (* Original Source syntax may be logically normalized
                       by the certificate's admitted endpoint. Its owned
                       free-ID set authorizes local original alignment,
                       rather than promoting normalization to ALPHA. *)
                    val original_candidate = align_term owned original
                    val (canonical,back) =
                      case original_candidate of
                          SOME (canonical,source_bridge) =>
                            (canonical,fn normalization =>
                              Thm.TRANS (Thm.SYM normalization) source_bridge)
                        | NONE =>
                            let val (canonical,bridge) = align owned in
                              (canonical,fn _ => bridge) end
                    val _ = whole_bridge original canonical
                    val _ = whole_bridge (G.representative graph owned)
                      canonical
                    (* All whole-law, type, ID and scope checks above
                       precede the first universal theorem transport. *)
                    val lifted = List.foldr
                      (fn (variable,theorem) =>
                        Drule.FORALL_EQ variable theorem)
                      (#bridge view) annotation
                    val (_,admitted_closure) =
                      Term.dest_eq (Thm.concl lifted)
                    val exact = Thm.ALPHA admitted_closure
                      (G.representative graph owned)
                    val normalization = Thm.TRANS lifted exact
                    val bridge = Thm.TRANS normalization (back normalization)
                  in (canonical,bridge) end
            | NONE =>
                let
                  val owned = closure_node node captured
                  val (canonical,bridge) = if null captured then
                      (owned,#bridge (G.rehome graph parent_scope node))
                    else
                      let val (canonical,bridge) = align owned
                          val _ = case source_admissions of NONE => ()
                            | SOME _ => whole_bridge original canonical
                      in (canonical,Thm.TRANS
                        (Thm.ALPHA original (G.representative graph owned))
                          bridge) end
                in (canonical,bridge) end
        in (node,annotation,
          canonical,bridge) end) (!captures)
      fun supplied (index,node) = if List.nth (sources,index) = node then
          Vector.sub (chosen,index) else raise ERR "close_equality"
            "source occurrence changed"
      val theorem = P.realize_with_sources block body edge supplied
      fun close_hypothesis ((node,variables,closure,bridge),theorem) =
        let
          val source = Thm.EQ_MP (Thm.SYM bridge)
            (Thm.ASSUME (G.representative graph closure))
          val instance = if null variables then source
            else Drule.SPECL variables source
        in Drule.PROVE_HYP instance theorem end
      val theorem = List.foldl close_hypothesis theorem closures
      val exact = SmtReplayBinderClose.run
        (G.representative graph)
        {entries=ListPair.map
           (fn ((kind,_),variable) => (kind,variable))
           (left_entries,variables),
         theorem=theorem,target=fn()=>G.representative graph target}
      val _ = if clean exact then () else raise ERR "close_equality"
        "binder closure changed theorem tags"
      val _ = close ()
    in {theorem = exact,
        hypotheses = List.map (fn (_,_,node,_) => node) closures} end

  fun close_equality_with_sources graph args =
    close_equality_core graph NONE args
  fun close_equality_with_source_admissions graph
      {arguments,source_admissions} =
    close_equality_core graph (SOME source_admissions) arguments
  fun close_equality graph args =
    #theorem (close_equality_with_sources graph args)
end
