(* Checked numeric transfer and theorem dependency stage; Source proposal. *)
structure SmtLib_GraphNumTheoremStage :> SmtLib_GraphNumTheoremStage =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure F = SmtLib_GraphSourcePortfolio
  structure GP = SmtLib_GraphPreprocess
  structure C = SmtReplayCanonGraph
  structure R = SmtReplayRules
  structure N = SmtLib_GraphNumComparison
  structure A = SmtLib_GraphNumArithmetic
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphNumTheoremStage"
  type law_row = {head : G.node option,ordinal : int,original : Thm.thm,
    normalized : G.node,filtered : bool}
  type law_gap = {head : G.node option,ordinal : int,original : Thm.thm,
    reason : string}
  datatype plan = Plan of {graph : G.graph,scope : G.scope,
    validation : GP.validation,laws : law_row list,
    gaps : law_gap list,charged : int,template_limit : int}
  fun active (Plan {graph,scope,...}) = G.validate_scope graph scope
  fun validation (p as Plan {validation,...}) = (active p;validation)
  fun laws (p as Plan {laws,...}) = (active p;laws)
  fun gaps (p as Plan {gaps,...}) = (active p;gaps)
  fun charged (p as Plan {charged,...}) = (active p;charged)
  fun template_limit (p as Plan {template_limit,...}) =
    (active p;template_limit)
  exception BinderLaw

  fun prepare_with_closed_laws graph scope sources
      {input_limit,template_limit,check_type,laws = supplied} =
    let
      val _ = G.validate_scope graph scope
      val _ = if Portable.pointer_eq (graph,S.owning_graph sources) andalso
          scope = S.owning_scope sources then () else
        raise ERR "prepare" "not the exact original Source owner"
      val _ = if input_limit > 0 andalso template_limit > 0 then () else
        raise ERR "prepare" "nonpositive original contract"
      val include_theorems = !SmtLib.include_theorems
      val assumptions = S.assumption_nodes sources
      val denied = S.denied_goal_node sources
      val original_goal = case R.operands graph boolSyntax.negation 1 denied of
          SOME [goal] => goal
        | _ => raise ERR "prepare" "original denied Source lost its constructor"
      val inputs = original_goal :: denied :: assumptions
      (* Original known graph metrics precede numeric schema/type work. *)
      val _ = List.app (fn node => List.app (fn metric =>
        case G.unfolded_nodes graph metric input_limit node of
          SOME n => if n <= input_limit then () else
            raise ERR "prepare" "original input exceeds admitted contract"
        | NONE => raise ERR "prepare" "unknown original graph metric")
        [G.RawNodes,G.BinderInclusiveNodes]) inputs
      val used = ref 0
      fun charge n =
        if n < 0 orelse n > template_limit - !used then
          raise ERR "prepare" "joint stage template contract exhausted"
        else used := !used + n
      (* Reserve original fact rows, transports, and query incidences before
         any stage proof/type callback. Duplicate occurrences still count. *)
      val _ = charge (2 * List.length assumptions + 4)
      fun checked_type ty =
        (G.validate_scope graph scope;check_type ty;
         G.validate_scope graph scope)
      fun admit_law term =
        let fun walk [] = ()
              | walk (node :: rest) =
                  (charge 1;
                   if Term.is_comb node then
                     let val (f,x) = Term.dest_comb node in
                       walk (f :: x :: rest) end
                   else if Term.is_var node orelse Term.is_const node then
                     walk rest
                   else raise BinderLaw)
        in walk [term] end
      val _ = charge (List.length supplied)
      val _ = List.app (fn theorem =>
        let val (tags,_) = Tag.dest_tag (Thm.tag theorem)
            val _ = if HOLset.isEmpty (Thm.hypset theorem) andalso
                null (Tag.axioms_of (Thm.tag theorem)) andalso
                List.all (fn tag => tag = "DISK_THM") tags then () else
              raise ERR "prepare" "supplied auxiliary law is not closed/clean"
        in admit_law (Thm.concl theorem) handle BinderLaw =>
          raise ERR "prepare" "supplied law needs checked recorded binder"
        end) supplied
      val visited = ref (Redblackset.empty Int.compare)
      fun admit_node node =
        if Redblackset.member (!visited,G.node_id node) then () else
          let
            val _ = if G.scope_visible graph scope (G.node_scope graph node)
              then () else raise ERR "prepare" "foreign stage node"
            val _ = List.app (fn metric =>
              case G.unfolded_nodes graph metric input_limit node of
                SOME n => if n <= input_limit then () else
                  raise ERR "prepare" "stage graph exceeds original input contract"
              | NONE => raise ERR "prepare" "unknown stage graph metric")
              [G.RawNodes,G.BinderInclusiveNodes]
            val _ = charge 1
            val _ = visited := Redblackset.add (!visited,G.node_id node)
            val _ = checked_type (G.type_of graph node)
          in () end
      val input_nodes = G.block_reachable graph inputs
      val _ = if List.length input_nodes <= template_limit - !used then () else
        raise ERR "prepare" "joint original input portfolio exceeds contract"
      val _ = List.app admit_node input_nodes
      (* Only these fixed small stock laws use pure full term_size. They are
         charged before the existing producers specialize/type their schemas. *)
      fun fixed laws = List.app
        (fn theorem => charge (Term.term_size (Thm.concl theorem))) laws
      val comparison = ref NONE
      fun compare node =
        let val propose = case !comparison of SOME cached => cached
          | NONE =>
              let val _ = fixed [integerTheory.INT_LT,integerTheory.INT_LE,
                                 integerTheory.INT_INJ]
                  val proposal = SmtLib_GraphNumComparison.propose graph scope
                    {template_limit = template_limit,check_type = checked_type}
                  val _ = comparison := SOME proposal
              in proposal end
        in propose node end
      val arithmetic = ref NONE
      fun arithmetic_transfer node =
        let val propose = case !arithmetic of SOME cached => cached
          | NONE =>
              let val _ = fixed [integerTheory.INT_ADD,integerTheory.INT_MUL,
                                 integerTheory.INT_EXP]
                  val proposal = SmtLib_GraphNumArithmetic.propose graph scope
                    {template_limit = template_limit,check_type = checked_type}
                  val _ = arithmetic := SOME proposal
              in proposal end
        in propose node end
      val schemas = ref (Redblackmap.mkDict Int.compare)
      fun propose node =
        let
          val _ = admit_node node
          val id = G.node_id node
        in case Redblackmap.peek (!schemas,id) of SOME cached => cached
          | NONE =>
            let
              val result = case R.spine graph node of
                SOME (head,[left,right]) =>
                  if (Term.same_const head numSyntax.less_tm orelse
                      Term.same_const head numSyntax.leq_tm orelse
                      Term.same_const head boolSyntax.equality) andalso
                    Type.compare (G.type_of graph left,numSyntax.num) = EQUAL
                    andalso
                    Type.compare (G.type_of graph right,numSyntax.num) = EQUAL
                  then compare node else NONE
              | SOME (head,[_]) =>
                  if Term.same_const head intSyntax.int_injection then
                    arithmetic_transfer node else NONE
              | _ => NONE
              val _ = Option.app (fn schema => List.app admit_node
                (G.block_reachable graph [C.graph_schema_source schema,
                                         C.graph_schema_result schema])) result
              val _ = schemas := Redblackmap.insert (!schemas,id,result)
            in result end
        end
      val conversions = ref (Redblackmap.mkDict Int.compare)
      fun conversion node =
        case Redblackmap.peek (!conversions,G.node_id node) of SOME value => value
        | NONE =>
            let val _ = charge 1 (* retained conversion occurrence *)
                val value = C.graph_conversion graph scope true propose node
                val _ = List.app admit_node
                  (G.block_reachable graph (C.graph_roots value))
                val _ = conversions := Redblackmap.insert
                  (!conversions,G.node_id node,value)
            in value end
      fun normalized fact = F.transport graph scope
        (conversion (F.endpoint fact)) fact
      val original_facts = List.tabulate (List.length assumptions,
        fn index => normalized (F.original graph scope sources index))
      val denied_fact = normalized
        (F.original graph scope sources (List.length assumptions))
      val query_goal = C.graph_result (conversion original_goal)
      val selected = ref (Redblackset.empty Int.compare)
      val fact_nodes = ref (Redblackset.empty Int.compare)
      val facts = ref ([] : F.fact list)
      val rows = ref ([] : law_row list)
      val missing = ref ([] : law_gap list)
      val pending = ref ([] : G.node list)
      fun enqueue node =
        (charge 1;List.app admit_node (G.block_reachable graph [node]);
         pending := node :: !pending)
      (* A single cumulative charge survives every dependency pass. The law
         body is admitted before FVs/type work or graph fact construction. *)
      fun law head (ordinal,theorem) =
        let
          val _ = if Option.isSome head then admit_law (Thm.concl theorem)
            else ()
          val variables = Term.free_vars (Thm.concl theorem)
          val _ = charge (2 * List.length variables + 2)
          val _ = List.app (checked_type o Term.type_of) variables
          val operands = List.map (G.variable graph scope G.RigidSource) variables
          val original = F.closed graph scope
            {theorem = theorem,holes = variables,operands = operands,
             template_limit = template_limit}
          val fact = normalized original
          val node = F.endpoint fact
          val filtered = case R.equality graph node of
              SOME (left,right) => left = right | NONE => false
          val _ = rows := {head = head,ordinal = ordinal,original = theorem,
            normalized = node,filtered = filtered} :: !rows
          val _ = if filtered orelse
              Redblackset.member (!fact_nodes,G.node_id node) then () else
            (fact_nodes := Redblackset.add (!fact_nodes,G.node_id node);
             facts := fact :: !facts;enqueue node)
        in () end handle BinderLaw => missing :=
          {head = head,ordinal = ordinal,original = theorem,
           reason = "quantified stock law needs checked binder/NUM_BINDERS recipe"}
          :: !missing
      fun head node = case G.view graph node of G.Constant _ =>
          if Redblackset.member (!selected,G.node_id node) then () else
            let
              val _ = charge 1
              val _ = selected := Redblackset.add (!selected,G.node_id node)
              val wanted = if include_theorems then
                SmtLib.graph_preprocessing_theorems_for_head
                  (G.representative graph node) else []
              (* Reserve every ordinal row even when normalization makes
                 no change or the final query fact is deduplicated. *)
              val _ = charge (List.length wanted)
              fun enumerate [] _ = ()
                | enumerate (theorem :: rest) ordinal =
                    (law (SOME node) (ordinal,theorem);enumerate rest (ordinal+1))
              val _ = enumerate wanted 0
            in () end
        | _ => ()
      fun close_dependencies () = case !pending of [] => ()
        | node :: rest =>
            (pending := rest;List.app head (G.block_reachable graph [node]);
             close_dependencies ())
      fun seed [] _ = ()
        | seed (theorem :: rest) ordinal =
            (law NONE (ordinal,theorem);seed rest (ordinal+1))
      val _ = seed supplied 0
      val _ = List.app enqueue (query_goal :: F.endpoint denied_fact ::
        List.map F.endpoint original_facts)
      val _ = close_dependencies ()
      val validation = GP.from_portfolio (F.validate graph scope sources
        {assumptions = original_facts @ List.rev (!facts),goal = query_goal,
         denied = denied_fact,template_limit = template_limit})
      val _ = G.validate_scope graph scope
    in Plan {graph = graph,scope = scope,validation = validation,
      laws = List.rev (!rows),gaps = List.rev (!missing),charged = !used,
      template_limit = template_limit} end

  fun prepare graph scope sources {input_limit,template_limit,check_type} =
    prepare_with_closed_laws graph scope sources
      {input_limit = input_limit,template_limit = template_limit,
       check_type = check_type,laws = []}
end
