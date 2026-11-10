(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphSourcePortfolio :> SmtLib_GraphSourcePortfolio =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure C = SmtReplayCanonGraph
  structure P = SmtReplayProof
  structure R = SmtReplayRules
  structure W = SmtReplayInvocationWork
  val _ = SmtReplayCanonGraph.validate_conversion_with_policy
  val _ = SmtReplayProof.validate_conversion_for
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphSourcePortfolio"
  (* Private identifiers index exact opaque objects, never proof authority.
     Poly/ML's portable counter is synchronized; overflow cannot reuse IDs. *)
  val next_identity = Portable.make_counter {init = 0,inc = 1}
  structure RP = SmtReplayResourcePolicy
  datatype fact = Fact of
    {identity : int,graph : G.graph,scope : G.scope,node : G.node,row : row}
  and row = Original of S.sources * int
    | PolicyOriginal of S.sources * IntInf.int * G.node
    | Closed of C.graph_conversion
    | RecordedClosed of P.closed_fact
    | Transport of C.graph_conversion * fact
    | BinderTransport of P.closed_conversion * fact
    | Apply of {law : fact,premises : fact list}
  datatype validation = Validation of
    {graph : G.graph,scope : G.scope,sources : S.sources,
     assumptions : fact list,goal : G.node,denied : fact,roots : G.node list,
     template_limit : int,closed_facts : P.closed_fact list,
     conversions : P.closed_conversion list}
    | PolicyValidation of
    {work:W.portfolio,graph:G.graph,scope:G.scope,sources:S.sources,
     limits:RP.semantic_policy,assumptions:fact list,goal:G.node,
     denied:fact,roots:G.node list,closed_facts:P.closed_fact list,
     conversions:P.closed_conversion list}
  fun nodes sources = S.assumption_nodes sources @ [S.denied_goal_node sources]
  fun endpoint (Fact {graph,scope,node,...}) =
    (G.validate_scope graph scope;ignore (G.view graph node);node)
  fun owned graph scope (fact as Fact {graph = other,scope = owner,...}) =
    (G.validate_scope graph scope;ignore (endpoint fact);
     if G.root_scope graph = G.root_scope other andalso scope = owner then ()
     else raise ERR "owned" "foreign graph or preprocessing scope")
  fun visible graph scope node =
    if G.scope_visible graph scope (G.node_scope graph node) then () else
      raise ERR "visible" "node outside preprocessing scope"
  (* Validate the unique typed application key without reconstructing it.
     Even an intern hit can reorder the paid type cache, invalidating the
     original Source snapshot that this read-only guard must preserve. *)
  fun exact_denial graph scope goal denied =
    let
      val _ = G.validate_semantic_scope graph scope
      val _ = visible graph scope goal
      val {Name=negation,Ty=negation_type,...} =
        Term.dest_thy_constid boolSyntax.negation
      val _ = if Type.compare (G.type_of graph goal,Type.bool) = EQUAL then
          () else raise Feedback.mk_HOL_ERR "SmtReplayGraph"
            "application" "application operand type mismatch"
      val node = endpoint denied
    in
      G.node_scope graph node = scope andalso
      (case G.view graph node of
         G.Application (head,operand) =>
           operand = goal andalso
           G.node_scope graph head = G.root_scope graph andalso
           Type.compare (G.type_of graph head,negation_type) = EQUAL andalso
           (case G.view graph head of
              G.Constant actual => actual = negation | _ => false)
       | _ => false)
    end
  fun original graph scope sources index =
    let val _ = G.validate_scope graph scope
        val originals = nodes sources
        val _ = if index >= 0 andalso index < List.length originals then ()
          else raise ERR "original" "original Source occurrence index"
        val node = List.nth (originals,index)
        val _ = visible graph scope node
    in Fact {identity = next_identity (),graph = graph,scope = scope,
             node = node,
             row = Original (sources,index)} end
  (* This finite schema admission does not open a binder. Full binder laws
     require the separately checked binder packet producer, not this path. *)
  fun admit limit term =
    let fun walk [] count = ()
          | walk (current :: rest) count =
              if count >= limit then raise ERR "closed" "law exceeds limit"
              else if Term.is_comb current then
                let val (f,x) = Term.dest_comb current in
                  walk (f :: x :: rest) (count+1) end
              else if Term.is_var current orelse Term.is_const current then
                walk rest (count+1)
              else raise ERR "closed" "law needs recorded binder recipe"
    in if limit > 0 then walk [term] 0 else
      raise ERR "closed" "nonpositive law limit" end
  fun closed_using convert graph scope
      {theorem,holes,operands,template_limit} =
    let
      val _ = G.validate_scope graph scope
      val _ = admit template_limit (Thm.concl theorem)
      val _ = List.app (visible graph scope) operands
      val (tags,_) = Tag.dest_tag (Thm.tag theorem)
      val _ = if null (Thm.hyp theorem) andalso
          null (Tag.axioms_of (Thm.tag theorem)) andalso
          List.all (fn tag => tag = "DISK_THM") tags then () else
        raise ERR "closed" "auxiliary schema is not a clean closed law"
      val schema = C.checked_graph_schema graph scope
        {theorem = Drule.EQT_INTRO theorem,holes = holes,operands = operands,
         template_limit = template_limit}
      val node = C.graph_schema_source schema
      val truth = G.constant graph scope boolSyntax.T
      val _ = if C.graph_schema_result schema = truth then () else
        raise ERR "closed" "closed law lost truth endpoint"
      val conversion = convert graph scope schema node
    in Fact {identity = next_identity (),graph = graph,scope = scope,
             node = node,
             row = Closed conversion} end
  fun closed graph scope input = closed_using
    (fn graph => fn scope => fn schema => fn node =>
      C.graph_conversion graph scope false
        (fn current => if current = node then SOME schema else NONE) node)
    graph scope input
  fun recorded_closed graph scope plan =
    let val _ = G.validate_scope graph scope
        val node = P.closed_node plan
        val _ = visible graph scope node
    in Fact {identity = next_identity (),graph = graph,scope = scope,
             node = node,
             row = RecordedClosed plan} end
  fun specialize_recorded graph scope
      {law,operands,template_limit,check_type} =
    let val _ = P.validate_closed_fact graph scope template_limit law
        val {theorem,holes} = P.specialize_closed law
          {operands = operands,check_type = check_type}
    in closed graph scope {theorem = theorem,holes = holes,
      operands = operands,template_limit = template_limit} end
  fun transport_using inventory graph scope conversion fact =
    let val _ = owned graph scope fact
        val _ = List.app (visible graph scope) (inventory conversion)
        val _ = if C.graph_source conversion = endpoint fact then () else
          raise ERR "transport" "conversion changed dependency endpoint"
    in Fact {identity = next_identity (),graph = graph,scope = scope,
             node = C.graph_result conversion,
             row = Transport (conversion,fact)} end
  fun transport graph scope conversion fact =
    transport_using C.graph_roots graph scope conversion fact
  type expectation =
    {graph : G.graph,scope : G.scope,sources : S.sources,template : int}
  fun expected_work work : expectation =
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val scope = S.owning_scope sources
        val limits = W.semantic_limits work
        val _ = W.validate work graph scope sources limits
    in {graph = graph,scope = scope,sources = sources,
        template = #template_limit limits} end
  (* Private row/object inspection precedes every legacy getter. Immutable
     graph/scope/Original Sources headers reject foreign owners before payment.
     Old begin retains the original visit/comparison/insertion programme.
     Other modes' Original/PolicyOriginal occurrences pay a fixed quote24:
     <=8 fact-field/row dispatch events, <=8 expected-header projection,
     comparison-argument and equality events, <=8 successful branch/list/call/
     return events. Work's own active/scope/payment costs are additional.
     These private immutable leaves have no children or observer callbacks;
     even repeated leaves are checked and paid, never looked up or inserted.
     Their genuine private counter IDs cannot alias another fact (overflow
     raises), so omitting their collision check loses no admissibility check.
     Other rows retain paid visits/comparisons/insertions in a balanced index
     for shared dependencies, local to ONE synchronous guard operation;
     neither template incidence nor earlier validation supplies credit. *)
  fun guard_facts work (expected : expectation) inputs =
    let fun charge () = W.spend_guard_policy work 1
        fun compare keys = (charge ();Int.compare keys)
        val completed = ref (Redblackmap.mkDict compare : (int,fact)
          Redblackmap.dict)
        fun visit (fact as Fact {identity,graph,scope,row,...}) =
          (if Portable.pointer_eq (graph,#graph expected) andalso
              scope = #scope expected then () else
             raise ERR "guard_facts" "different original graph or scope";
           (case row of
                Original (sources,_) =>
                  if Portable.pointer_eq (sources,#sources expected) then ()
                  else raise ERR "guard_facts" "different original Sources"
              | PolicyOriginal (sources,_,_) =>
                  if Portable.pointer_eq (sources,#sources expected) then ()
                  else raise ERR "guard_facts" "different original Sources"
              | _ => ());
           case (W.ordinary_legacy_guard_mode work,row) of
                (false,Original _) => W.spend_guard_policy work 24
              | (false,PolicyOriginal _) => W.spend_guard_policy work 24
              | _ =>
           (charge ();
            case Redblackmap.peek (!completed,identity) of SOME held =>
             if Portable.pointer_eq (fact,held) then () else
               raise ERR "guard_facts" "private fact identity collision"
           | NONE =>
           (case row of
                Original _ => ()
              | PolicyOriginal _ => ()
              | Closed conversion =>
                  C.validate_conversion_with_policy work conversion
              | RecordedClosed _ => ()
              | Transport (conversion,source) =>
                  (C.validate_conversion_with_policy work conversion;
                   visit source)
              | BinderTransport (conversion,source) =>
                  (P.validate_conversion_for work conversion;visit source)
              | Apply {law,premises} => (visit law;List.app visit premises);
            charge ();
            completed := Redblackmap.insert (!completed,identity,fact))))
    in List.app visit inputs end
  fun transport_with_work work conversion fact =
    ((let val expected = expected_work work
          val _ = C.validate_conversion_with_policy work conversion
          val _ = guard_facts work expected [fact]
      in transport_using (C.graph_roots_for work)
        (#graph expected) (#scope expected) conversion fact end)
     handle primary => (W.close work;raise primary))
  fun binder_transport graph scope conversion fact =
    let val _ = owned graph scope fact
        val source = P.conversion_source conversion
        val target = P.conversion_target conversion
        val _ = List.app (visible graph scope) [source,target]
        val _ = if source = endpoint fact then () else
          raise ERR "binder_transport" "original dependency endpoint differs"
    in Fact {identity = next_identity (),graph = graph,scope = scope,
      node = target,row = BinderTransport (conversion,fact)} end
  fun apply graph scope {law,premises,target} =
    let val _ = List.app (owned graph scope) (law :: premises)
        val _ = visible graph scope target
        val expected = SmtReplayRules.implication graph scope
          (List.map endpoint premises) target
        val _ = if endpoint law = expected then () else
          raise ERR "apply" "law does not match ordered dependency endpoints"
    in Fact {identity = next_identity (),graph = graph,scope = scope,
             node = target,
             row = Apply {law = law,premises = premises}} end
  (* Only authenticated entrypoints supply Work. Template incidence checks
     do not pay Canon walks: each owned inventory call debits actual work,
     including repeated legacy projections in Idle, with no saved credit. *)
  fun validate_using work graph scope sources
      {assumptions,goal,denied,template_limit} =
    let
      val graph_roots = case work of NONE => C.graph_roots
        | SOME owner => C.graph_roots_for owner
      val graph_closed_facts = case work of NONE => C.graph_closed_facts
        | SOME owner => C.graph_closed_facts_for owner
      val graph_conversions = case work of NONE => C.graph_conversions
        | SOME owner => C.graph_conversions_for owner
      val _ = G.validate_scope graph scope
      val _ = visible graph scope goal
      val originals = nodes sources
      (* Use the SAME caller's common block template contract. Count actual
         portfolio incidences; a shared fact is expanded at most once. *)
      val used = ref 0
      fun charge count =
        if count < 0 orelse count > template_limit - !used then
          raise ERR "validate" "dependency portfolio exceeds template limit"
        else used := !used + count
      val _ = if template_limit > 0 then () else
        raise ERR "validate" "nonpositive original template contract"
      val _ = charge (List.length originals)
      val _ = charge 2 (* query goal and denial incidence *)
      val _ = List.app (fn _ => charge 1) assumptions
      val visited = ref (Redblackmap.mkDict Int.compare : (int,fact)
        Redblackmap.dict)
      val closed_facts = ref ([] : P.closed_fact list)
      val conversions = ref ([] : P.closed_conversion list)
      fun graph_leaves conversion =
        (List.app (fn plan =>
          (charge 1;P.validate_closed_fact graph scope template_limit plan;
           closed_facts := plan :: !closed_facts))
          (graph_closed_facts conversion);
         List.app (fn plan =>
          (charge 3;P.validate_conversion graph scope template_limit plan;
           conversions := plan :: !conversions))
          (graph_conversions conversion))
      val _ = if exact_denial graph scope goal denied then () else
        raise ERR "validate" "query denial is not exact negated query goal"
      fun walk [] roots = roots
        | walk ((fact as Fact {identity,node,row,...}) :: rest) roots =
            (case Redblackmap.peek (!visited,identity) of
               SOME held =>
                 if Portable.pointer_eq (held,fact) then walk rest roots
                 else raise ERR "validate" "private fact identity collision"
             | NONE => let val _ = charge 1
                val _ = visited := Redblackmap.insert (!visited,identity,fact)
                val _ = owned graph scope fact
                val _ = if Type.compare (G.type_of graph node,Type.bool)
                    = EQUAL then () else
                  raise ERR "validate" "query dependency is not Boolean"
                val roots = node :: roots
            in case row of
                Original (original,index) =>
                  if Portable.pointer_eq (sources,original) andalso
                      List.nth (originals,index) = node then walk rest roots
                  else raise ERR "validate" "different original Source object"
              | PolicyOriginal _ =>
                  raise ERR "validate" "policy original needs policy validation"
              | RecordedClosed plan =>
                  let val _ = if P.closed_node plan = node then () else
                        raise ERR "validate" "closed auxiliary node differs"
                      val _ = P.validate_closed_fact graph scope
                        template_limit plan
                      val _ = charge 1
                      val _ = closed_facts := plan :: !closed_facts
                  in walk rest roots end
              | Closed conversion =>
                  let val more = graph_roots conversion
                      val _ = graph_leaves conversion
                      val _ = List.app (fn _ => charge 1) more
                  in walk rest (more @ roots) end
              | Transport (conversion,source) =>
                  let val more = graph_roots conversion
                      val _ = graph_leaves conversion
                      val _ = charge 1 (* source dependency edge *)
                      val _ = List.app (fn _ => charge 1) more
                  in walk (source :: rest) (more @ roots) end
              | BinderTransport (conversion,source) =>
                  let val _ = P.validate_conversion graph scope
                        template_limit conversion
                      val _ = if P.conversion_source conversion =
                          endpoint source andalso
                          P.conversion_target conversion = node then () else
                        raise ERR "validate" "binder endpoints differ"
                      val _ = charge 3 (* leaf and both endpoints *)
                      val _ = charge 1 (* original dependency edge *)
                      val _ = conversions := conversion :: !conversions
                      val more = [P.conversion_source conversion,
                                  P.conversion_target conversion]
                  in walk (source :: rest) (more @ roots) end
              | Apply {law,premises} =>
                  let val _ = charge 1 (* law dependency edge *)
                      val _ = List.app (fn _ => charge 1) premises
                  in walk (law :: premises @ rest) roots end
            end)
      val roots = walk (denied :: assumptions) (goal :: originals)
    in Validation {graph = graph,scope = scope,sources = sources,
      assumptions = assumptions,goal = goal,denied = denied,roots = roots,
      template_limit = template_limit,
      closed_facts = List.rev (!closed_facts),
      conversions = List.rev (!conversions)} end
  fun validate graph scope sources input =
    validate_using NONE graph scope sources input
  fun active (Validation {graph,scope,sources,...}) =
    (G.validate_scope graph scope;ignore (nodes sources))
    | active (PolicyValidation
        {work,graph,scope,sources,limits,...}) =
        W.validate_policy work graph scope sources limits
  fun original_sources (v as Validation {sources,...}) = (active v;sources)
    | original_sources (v as PolicyValidation {sources,...}) =
        (active v;sources)
  fun validate_for graph scope sources
      (v as Validation {graph = held,scope = owner,sources = original,...}) =
    (G.validate_scope graph scope;
     if Portable.pointer_eq (graph,held) andalso scope = owner andalso
         Portable.pointer_eq (sources,original) then active v else
       raise ERR "validate_for" "foreign graph, scope or Source portfolio")
    | validate_for graph scope sources
        (v as PolicyValidation {graph=held,scope=owner,sources=original,...}) =
        (G.validate_scope graph scope;
         if Portable.pointer_eq (graph,held) andalso scope=owner andalso
             Portable.pointer_eq (sources,original) then active v else
           raise ERR "validate_for" "foreign graph, scope or Source portfolio")
  fun policy_expected work =
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val scope = S.owning_scope sources
        val limits = W.semantic_policy work
        val _ = W.validate_policy work graph scope sources limits
    in {graph=graph,scope=scope,sources=sources,limits=limits} end

  (* Original occurrence numbers are generated by this owned walk, not
     projected from a policy ceiling or supplied as caller authority. *)
  fun originals_with_policy work =
    ((let
        val expected = policy_expected work
        val graph = #graph expected val scope = #scope expected
        val sources = #sources expected
        fun make index node =
          (W.validate_policy work graph scope sources (#limits expected);
           visible graph scope node;
           Fact {identity=next_identity (),graph=graph,scope=scope,node=node,
             row=PolicyOriginal (sources,index,node)})
        fun ordered [] (index:IntInf.int) =
              ([],make index (S.denied_goal_node sources))
          | ordered (node::rest) index =
              let val fact = make index node
                  val (tail,denied) = ordered rest (index+1)
              in (fact::tail,denied) end
        val (assumptions,denied) = ordered (S.assumption_nodes sources) 0
      in {assumptions=assumptions,denied=denied} end)
     handle primary => (W.close work;raise primary))

  fun policy_nth originals index =
    if index < (0:IntInf.int) then
      raise ERR "validate_with_policy" "negative original occurrence"
    else let fun seek [] _ =
                   raise ERR "validate_with_policy" "original index absent"
               | seek (node::rest) n =
                   if n=0 then node else seek rest (n-1)
         in seek originals index end

  (* This pass precedes endpoint/Type getters, just as the finite owned
     validator's guard_facts pass does. Foreign facts cannot activate their
     graph or proof backing while the expected Work is being validated. *)
  fun guard_policy_facts work graph scope sources inputs =
    let
      fun charge () = W.spend_guard_policy work 1
      fun compare keys = (charge ();Int.compare keys)
      val completed = ref (Redblackmap.mkDict compare : (int,fact)
        Redblackmap.dict)
      fun visit (fact as Fact {identity,graph=held,scope=frame,row,...}) =
        (if Portable.pointer_eq (graph,held) andalso scope=frame then () else
           raise ERR "guard_policy_facts" "different original graph or scope";
         (case row of
              Original (saved,_) =>
                if Portable.pointer_eq (sources,saved) then () else
                  raise ERR "guard_policy_facts" "different original Sources"
            | PolicyOriginal (saved,_,_) =>
                if Portable.pointer_eq (sources,saved) then () else
                  raise ERR "guard_policy_facts" "different original Sources"
            | _ => ());
         charge ();
         case Redblackmap.peek (!completed,identity) of SOME held =>
           if Portable.pointer_eq (fact,held) then () else
             raise ERR "guard_policy_facts" "private fact identity collision"
         | NONE =>
         (case row of
              Original _ => ()
            | PolicyOriginal _ => ()
            | Closed conversion =>
                C.validate_conversion_with_policy work conversion
            | RecordedClosed plan =>
                P.validate_closed_fact_with_policy graph scope
                  (#template_limit (W.semantic_policy work)) plan
            | Transport (conversion,source) =>
                (C.validate_conversion_with_policy work conversion;
                 visit source)
            | BinderTransport (conversion,source) =>
                (P.validate_conversion_for work conversion;visit source)
            | Apply {law,premises} => (visit law;List.app visit premises);
          charge ();
          completed := Redblackmap.insert (!completed,identity,fact)))
    in List.app visit inputs end

  fun validate_policy_portfolio work {assumptions,goal,denied} =
    let
      val expected = policy_expected work
      val graph = #graph expected val scope = #scope expected
      val sources = #sources expected val limits = #limits expected
      val template = #template_limit limits
      val _ = guard_policy_facts work graph scope sources
        (denied::assumptions)
      val _ = G.validate_scope graph scope
      val _ = visible graph scope goal
      val originals = nodes sources
      val used = ref (0:IntInf.int)
      fun charge count =
        if count < 0 orelse not (RP.allows template (!used+count)) then
          raise ERR "validate_with_policy"
            "dependency portfolio exceeds template limit"
        else used := !used+count
      val _ = if RP.positive template then () else
        raise ERR "validate_with_policy" "nonpositive template contract"
      val _ = List.app (fn _=>charge 1) originals
      val _ = charge 2
      val _ = List.app (fn _=>charge 1) assumptions
      val visited = ref (Redblackmap.mkDict Int.compare : (int,fact)
        Redblackmap.dict)
      val closed_facts = ref ([]:P.closed_fact list)
      val conversions = ref ([]:P.closed_conversion list)
      fun graph_leaves conversion =
        let val _ = C.validate_conversion_with_policy work conversion
            val roots = C.graph_roots_for work conversion
            val _ = List.app (fn plan=>
           (charge 1;
            P.validate_closed_fact_with_policy graph scope template plan;
            closed_facts := plan :: !closed_facts))
           (C.graph_closed_facts_for work conversion)
            val _ = List.app (fn plan=>
           (charge 3;
            P.validate_conversion_with_policy graph scope template plan;
            conversions := plan :: !conversions))
           (C.graph_conversions_for work conversion)
        in roots end
      val _ = if exact_denial graph scope goal denied then () else
        raise ERR "validate_with_policy"
          "query denial is not exact negated query goal"
      fun original sources_from index node rest roots =
        if Portable.pointer_eq (sources,sources_from) andalso
            policy_nth originals index=node then walk rest roots
        else raise ERR "validate_with_policy" "different original Source"
      and walk [] roots = roots
        | walk ((fact as Fact
            {identity,node,row,graph=held,scope=frame})::rest) roots =
          (if Portable.pointer_eq (graph,held) andalso scope=frame then ()
             else raise ERR "validate_with_policy" "different fact owner";
           W.validate_policy work graph scope sources limits;
           case Redblackmap.peek (!visited,identity) of SOME held =>
             if Portable.pointer_eq (held,fact) then walk rest roots else
               raise ERR "validate_with_policy" "private identity collision"
           | NONE =>
             let val _ = charge 1
                 val _ = visited := Redblackmap.insert (!visited,identity,fact)
                 val _ = owned graph scope fact
                 val _ = if Type.compare (G.type_of graph node,Type.bool)
                     = EQUAL then () else
                   raise ERR "validate_with_policy"
                     "query dependency is not Boolean"
                 val roots = node::roots
             in case row of
                  Original (saved,index) =>
                    original saved (IntInf.fromInt index) node rest roots
                | PolicyOriginal (saved,_,held_node) =>
                    if Portable.pointer_eq (sources,saved) andalso
                        node=held_node then walk rest roots else
                      raise ERR "validate_with_policy"
                        "different produced original Source"
                | RecordedClosed plan =>
                    (P.validate_closed_fact_with_policy
                       graph scope template plan;
                     if P.closed_node plan=node then () else
                       raise ERR "validate_with_policy"
                         "closed auxiliary node differs";
                     charge 1;closed_facts := plan :: !closed_facts;
                     walk rest roots)
                | Closed conversion =>
                    let val more = graph_leaves conversion
                        val _ = List.app (fn _=>charge 1) more
                    in walk rest (more@roots) end
                | Transport (conversion,source) =>
                    let val more = graph_leaves conversion val _ = charge 1
                        val _ = List.app (fn _=>charge 1) more
                    in walk (source::rest) (more@roots) end
                | BinderTransport (conversion,source) =>
                    let val endpoints=P.conversion_endpoints_with_policy_for
                          work graph scope template conversion
                        val _=if #source endpoints=endpoint source andalso
                            #target endpoints=node then ()else
                          raise ERR "validate_with_policy" "binder endpoints"
                        val _=charge 3 val _=charge 1
                        val _=conversions:=conversion:: !conversions
                    in walk(source::rest)
                      (#source endpoints:: #target endpoints::roots)end
                | Apply {law,premises} =>
                    (charge 1;List.app (fn _=>charge 1) premises;
                     walk (law::premises@rest) roots)
             end)
      val roots = walk (denied::assumptions) (goal::originals)
      val _ = W.validate_policy work graph scope sources limits
    in PolicyValidation {work=work,graph=graph,scope=scope,sources=sources,
      limits=limits,assumptions=assumptions,goal=goal,denied=denied,
      roots=roots,closed_facts=List.rev (!closed_facts),
      conversions=List.rev (!conversions)} end

  fun validate_portfolio_with_policy work input =
    (validate_policy_portfolio work input
     handle primary => (W.close work;raise primary))

  fun validate_policy_for expected
      (value as PolicyValidation {work,...}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "validate_with_policy" "different original Work";
      let val PolicyValidation {graph,scope,sources,limits,assumptions,
            goal,denied,...} = value
          val _ = W.validate_policy expected graph scope sources limits
          val _ = validate_policy_portfolio expected
            {assumptions=assumptions,goal=goal,denied=denied}
      in () end)
     handle primary => (W.close expected;raise primary))

  fun validate_with_work expected (saved as PolicyValidation _) =
        validate_policy_for expected saved
    | validate_with_work work (v as Validation
      {graph,scope,sources,template_limit,conversions,assumptions,denied,...}) =
    ((let val expected = expected_work work
          val _ = if Portable.pointer_eq (graph,#graph expected) andalso
              scope = #scope expected andalso
              Portable.pointer_eq (sources,#sources expected) andalso
              template_limit = #template expected then () else
            raise ERR "validate_with_work" "different invocation portfolio"
          val _ = List.app (P.validate_conversion_for work) conversions
          val _ = guard_facts work expected (denied :: assumptions)
      in active v end)
     handle primary => (W.close work;raise primary))
  fun validate_portfolio_with_work work {assumptions,goal,denied} =
    ((let val expected = expected_work work
          val _ = guard_facts work expected (denied :: assumptions)
      in validate_using (SOME work)
        (#graph expected) (#scope expected) (#sources expected)
        {assumptions = assumptions,goal = goal,denied = denied,
         template_limit = #template expected} end)
     handle primary => (W.close work;raise primary))
  fun source_nodes v = nodes (original_sources v)
  fun processed_assumptions (v as Validation {assumptions,...}) =
    (active v;List.map endpoint assumptions)
    | processed_assumptions
        (v as PolicyValidation {assumptions,...}) =
        (active v;List.map endpoint assumptions)
  fun processed_denied_goal (v as Validation {denied,...}) =
    (active v;endpoint denied)
    | processed_denied_goal (v as PolicyValidation {denied,...}) =
        (active v;endpoint denied)
  fun processed_goal (v as Validation {graph,goal,...}) =
    (active v;(List.map (G.representative graph) (processed_assumptions v),
               G.representative graph goal))
    | processed_goal (v as PolicyValidation {graph,goal,...}) =
        (active v;(List.map (G.representative graph) (processed_assumptions v),
                   G.representative graph goal))
  fun roots (v as Validation {roots,...}) = (active v;roots)
    | roots (v as PolicyValidation {roots,...}) = (active v;roots)
  fun template_limit (v as Validation {template_limit,...}) =
    (active v;template_limit)
    | template_limit (v as PolicyValidation _) =
        (active v;raise ERR "template_limit" "requires policy template getter")
  fun closed_facts (v as Validation {closed_facts,...}) =
    (active v;closed_facts)
    | closed_facts (v as PolicyValidation {closed_facts,...}) =
        (active v;closed_facts)
  fun conversions (v as Validation {conversions,...}) =
    (active v;conversions)
    | conversions (v as PolicyValidation {conversions,...}) =
        (active v;conversions)
  fun prepend_recorded graph scope
      (v as Validation {graph = held,scope = owner,sources,assumptions,
                        goal,denied,template_limit,...}) plans =
    let
      val _ = G.validate_scope graph scope
      val _ = if Portable.pointer_eq (graph,held) andalso scope = owner
        then () else raise ERR "prepend_recorded" "foreign portfolio owner"
      val _ = active v
      val _ = List.app
        (P.validate_closed_fact graph scope template_limit) plans
      val auxiliary = List.map (recorded_closed graph scope) plans
    in validate graph scope sources
      {assumptions = List.rev auxiliary @ assumptions,goal = goal,
       denied = denied,template_limit = template_limit} end
    | prepend_recorded _ _ (v as PolicyValidation _) _ =
        (active v;raise ERR "prepend_recorded" "requires policy entrypoint")
  fun assembler (v as Validation
      {graph,scope,sources,assumptions,denied,template_limit,...})
      block =
    let
      val _ = active v
      val _ = if P.template_limit block = template_limit then () else
        raise ERR "assembler" "original template limit changed"
      val _ = if G.scope_visible graph (P.scope block) scope then () else
        raise ERR "assembler" "block outside preprocessing scope"
      val originals = nodes sources
      val _ = if List.length (P.sources block) >= List.length originals andalso
          List.take (P.sources block,List.length originals) = originals then ()
        else raise ERR "assembler" "original occurrence prefix changed"
      fun equality conversion = P.compose block
        (fn [proof,constructor] => Thm.EQ_MP constructor proof
          | _ => raise Fail "portfolio equality constructor")
        [C.graph_assemble graph block conversion,
         P.constructor block (C.graph_equality conversion)]
      val built = ref (Redblackmap.mkDict Int.compare :
        (int,fact * P.edge) Redblackmap.dict)
      fun build (fact as Fact {identity,node,row,...}) =
        (active v;ignore (P.name block node);
         case Redblackmap.peek (!built,identity) of SOME (held,edge) =>
           if Portable.pointer_eq (held,fact) then edge else
             raise ERR "assembler" "private fact identity collision"
         | NONE => let val edge = case row of
           Original (_,index) => P.source block index
         | PolicyOriginal _ =>
             raise ERR "assembler" "requires policy block Source operands"
         | RecordedClosed plan => P.closed block plan
         | Closed conversion => P.compose block
             (fn [eq,truth] => Drule.EQT_ELIM (Thm.TRANS eq truth)
               | _ => raise Fail "portfolio closed fact")
             [equality conversion,
              P.definition block (C.graph_result conversion)]
         | Transport (conversion,source) => P.compose block
             (fn [eq,proof] => Thm.EQ_MP eq proof
               | _ => raise Fail "portfolio transported fact")
             [equality conversion,build source]
         | BinderTransport (conversion,source) => P.compose block
             (fn [eq,proof] => Thm.EQ_MP eq proof
               | _ => raise Fail "portfolio binder transported fact")
             [P.conversion block conversion,build source]
         | Apply {law,premises} => R.apply_law graph block
             {law = (endpoint law,build law),target = node,
              premises = List.map (fn premise =>
                (endpoint premise,build premise)) premises}
             val _ = built := Redblackmap.insert
               (!built,identity,(fact,edge))
           in edge end)
      (* Retain the first query fact for each endpoint, as List.find did.
         Build this bounded index once, including denial after assumptions. *)
      fun index (fact,queries) =
        let val id = G.node_id (endpoint fact)
        in case Redblackmap.peek (queries,id) of SOME _ => queries
          | NONE => Redblackmap.insert (queries,id,fact) end
      val queries = List.foldl index (Redblackmap.mkDict Int.compare)
        (assumptions @ [denied])
      val memo = ref (Redblackmap.mkDict Int.compare)
      fun assemble node =
        (active v;ignore (P.name block node);
         case Redblackmap.peek (!memo,G.node_id node) of SOME edge => SOME edge
         | NONE => case Redblackmap.peek (queries,G.node_id node) of
             NONE => NONE
             | SOME fact => let val edge = build fact
                 val _ = memo := Redblackmap.insert (!memo,G.node_id node,edge)
               in SOME edge end)
    in assemble end
    | assembler (v as PolicyValidation _) _ =
        (active v;raise ERR "assembler" "requires policy block entrypoint")
  val validate_with_policy = validate_with_work
  fun template_policy (v as PolicyValidation {limits,...}) =
        (active v;#template_limit limits)
    | template_policy (v as Validation _) = RP.from_int (template_limit v)
  (* The closed conversion is authenticated against expected Work before
     endpoint getters. A fact's immutable owner is checked before backing. *)
  fun binder_transport_with_policy work conversion fact=
    ((let val e=policy_expected work
          val graph= #graph e val scope= #scope e val sources= #sources e
          val _=P.validate_conversion_for work conversion
          val _=guard_policy_facts work graph scope sources [fact]
          val result=binder_transport graph scope conversion fact
          val _=guard_policy_facts work graph scope sources [result]
      in result end)
     handle primary=>(W.close work;raise primary))
  (* Native proof effects use the original block's contract. Metadata
     limits never admit an expanded Source operand to a native rule. *)
  fun assembler_with_policy expected value block =
    ((W.with_step expected (fn () =>
      let
        val _ = case value of PolicyValidation {work,...} =>
            if Portable.pointer_eq (expected,work) then () else
              raise ERR "policy_assembler" "different original Work"
          | _ => raise ERR "policy_assembler" "policy portfolio required"
        val owner = P.policy_native_block_owner_for expected block
        fun valid () =
          (validate_with_policy expected value;
           ignore (P.policy_native_block_owner_for expected block))
        val _ = valid ()
        val PolicyValidation {graph,scope,sources,assumptions,denied,...} =
          value
        val _ = if Portable.pointer_eq (graph,#graph owner) andalso
            G.scope_visible graph (#scope owner) scope then () else
          raise ERR "policy_assembler" "different graph or invisible scope"
        val originals = nodes sources
        val actual = P.sources block
        (* Compare the actual ordered Source prefix, including duplicates.
           The returned int is an index into the admitted native vector;
           no policy ceiling or caller ordinal is narrowed to an int. *)
        fun prefix [] _ = ()
          | prefix (_::_) [] =
              raise ERR "policy_assembler" "original Source prefix absent"
          | prefix (wanted::rest) (held::tail) =
              (W.spend_policy expected 2;
               if wanted=held then prefix rest tail else
                 raise ERR "policy_assembler" "original Source prefix changed")
        val _ = prefix originals actual
        fun original index node =
          let fun seek [] _ _ =
                    raise ERR "policy_assembler" "original occurrence absent"
                | seek (held::rest) ordinal native =
                    (W.spend_policy expected 2;
                     if ordinal=(0:IntInf.int) then
                       if held=node then P.source block native else
                         raise ERR "policy_assembler" "Source endpoint changed"
                     else seek rest (ordinal-1) (native+1))
          in if index<0 then
               raise ERR "policy_assembler" "negative original occurrence"
             else seek originals index 0 end
        val built = ref ([]:(fact * P.edge) list)
        fun saved _ [] = NONE
          | saved fact ((held,edge)::rest) =
              (W.spend_policy expected 1;
               if Portable.pointer_eq (fact,held) then SOME edge else
                 saved fact rest)
        fun rule opcode premises =
          P.execute_primitive_with_policy expected
            (P.prepare_primitive_with_policy expected block opcode premises)
        fun build (fact as Fact {node,row,...}) =
          (valid ();W.spend_policy expected 2;
           ignore (P.name block node);
           case saved fact (!built) of SOME edge => edge
           | NONE =>
             let val edge = case row of
                   Original (_,index) => original (IntInf.fromInt index) node
                 | PolicyOriginal (_,index,held) =>
                     if held=node then original index node else
                       raise ERR "policy_assembler" "Source endpoint changed"
                 | RecordedClosed plan => P.closed block plan
                 | BinderTransport (conversion,source) =>
                     let val proof = build source
                         val _ = P.validate_conversion_for expected conversion
                         val equality = P.conversion block conversion
                     in rule P.EqualityMP [equality,proof] end
                 | Closed _ => raise ERR "policy_assembler"
                     "graph conversion needs its policy assembler"
                 | Transport _ => raise ERR "policy_assembler"
                     "graph conversion needs its policy assembler"
                 | Apply _ => raise ERR "policy_assembler"
                     "conditional law needs its owned implication rule"
                 val _ = valid ()
                 val _ = W.spend_policy expected 1
                 val _ = built := (fact,edge):: !built
             in edge end)
        fun query _ [] = NONE
          | query node (fact::rest) =
              (W.spend_policy expected 2;
               if endpoint fact=node then SOME fact else query node rest)
        val queries = assumptions @ [denied]
        fun assemble node =
          W.with_step expected (fn () =>
            (valid ();W.spend_policy expected 1;
             ignore (P.name block node);
             let val result = Option.map build (query node queries)
                 val _ = valid ()
             in result end))
        val _ = valid ()
      in assemble end))
     handle primary => (W.close expected;raise primary))

  structure OrdinaryPolicyAssembly=SmtReplaySourcePortfolioAssemblyFn
    (struct
       type block=P.block
       type edge=P.edge
       type inst_plan=P.policy_closed_named_inst_plan
       datatype fact = datatype fact
       datatype row = datatype row
       datatype validation = datatype validation
       val validate_with_policy=validate_with_policy
       val nodes=nodes
       val endpoint=endpoint
       val error=ERR
       val owner_for=P.policy_native_block_owner_for
       fun sources _ block=P.sources block
       fun source _ block index=P.source block index
       fun name _ block node=P.name block node
       fun derive expected block opcode premises=
         P.execute_primitive_with_policy expected
           (P.prepare_primitive_with_policy expected block opcode premises)
       val constructor=P.constructor_with_policy
       fun definition _ block node=P.definition block node
       fun closed _ block fact=P.closed block fact
       fun conversion _ block fact=P.conversion block fact
       val prepare_inst=P.prepare_closed_named_inst_with_policy
       val execute_inst=P.execute_closed_named_inst_with_policy
       val graph_assemble=C.graph_assemble_with_policy
       val apply_law=R.apply_implication_law_with_policy
     end)
  val assembler_with_policy=OrdinaryPolicyAssembly.assembler_with_policy

  structure SparseImplicationLaw=SmtReplayImplicationLawFn
    (struct
       type block=P.policy_sparse_block
       type edge=P.policy_sparse_edge
       val owner_for=P.policy_sparse_owner_for
       val theorem=P.policy_sparse_theorem_for
       val name=P.policy_sparse_name_for
       val constructor=P.policy_sparse_constructor_for
       val derive=P.policy_sparse_primitive_for
       fun implication_mp expected block law premise=
         P.policy_sparse_boolean_for expected block
           P.PolicyImplicationMP [law,premise]
       val error=Feedback.mk_HOL_ERR "SmtReplayRules"
     end)
  structure SparsePolicyAssembly=SmtReplaySourcePortfolioAssemblyFn
    (struct
       type block=P.policy_sparse_block
       type edge=P.policy_sparse_edge
       type inst_plan=P.policy_sparse_named_inst_plan
       datatype fact = datatype fact
       datatype row = datatype row
       datatype validation = datatype validation
       val validate_with_policy=validate_with_policy
       val nodes=nodes
       val endpoint=endpoint
       val error=ERR
       val owner_for=P.policy_sparse_owner_for
       val sources=P.policy_sparse_sources_for
       val source=P.policy_sparse_source_for
       val name=P.policy_sparse_name_for
       val derive=P.policy_sparse_primitive_for
       val constructor=P.policy_sparse_constructor_for
       val definition=P.policy_sparse_definition_for
       val closed=P.policy_sparse_closed_for
       val conversion=P.policy_sparse_conversion_for
       val prepare_inst=P.prepare_policy_sparse_named_inst
       val execute_inst=P.execute_policy_sparse_named_inst
       val graph_assemble=C.graph_assemble_sparse_with_policy
       val apply_law=SparseImplicationLaw.apply_implication_law_with_policy
     end)
  val assembler_sparse_with_policy=SparsePolicyAssembly.assembler_with_policy

  (* The positive Goal and ordered processed assumptions, including duplicate
     occurrences. Expected Work is compared before held backing activation. *)
  fun processed_nodes_with_policy_for expected value=
    ((case value of PolicyValidation{work,...}=>
        if Portable.pointer_eq(expected,work)then ()else
          raise ERR "processed_nodes_with_policy_for" "different original Work"
      | _=>raise ERR "processed_nodes_with_policy_for"
          "policy portfolio required";
      validate_with_policy expected value;
      let val PolicyValidation{assumptions,goal,...}=value
      in {assumptions=List.map endpoint assumptions,goal=goal}end)
     handle primary=>(W.close expected;raise primary))

  fun processed_nodes_in_action_with_policy_for expected value =
    ((case value of PolicyValidation {work,...} =>
        if Portable.pointer_eq (expected,work) then () else
          raise ERR "processed_nodes_in_action_with_policy_for"
            "different original Work"
      | _ => raise ERR "processed_nodes_in_action_with_policy_for"
          "policy portfolio required";
      validate_with_policy expected value;
      let
        val PolicyValidation {assumptions,goal,...} = value
        val _ = W.spend_policy expected 16
        fun copy [] = (W.spend_policy expected 1; [])
          | copy (fact :: rest) =
              (W.spend_policy expected 3; endpoint fact :: copy rest)
        val result = {assumptions=copy assumptions,goal=goal}
        val _ = validate_with_policy expected value
      in result end)
     handle primary => (W.close expected;raise primary))

  (* Actual completion keeps the legacy reverse-prepend order. Expected
     Work is fenced before held portfolio or closed-fact backing. *)
  fun prepend_recorded_with_policy expected value plans=
    ((case value of PolicyValidation{work,...}=>
        if Portable.pointer_eq(expected,work)then ()else
          raise ERR "prepend_recorded_with_policy" "different original Work"
      | _=>raise ERR "prepend_recorded_with_policy"
          "policy portfolio required";
      validate_with_policy expected value;
      let val PolicyValidation{graph,scope,limits,assumptions,goal,
            denied,...}=value
          val _=List.app (P.validate_closed_fact_with_policy graph scope
            (#template_limit limits)) plans
          val auxiliary=List.map(recorded_closed graph scope)plans
      in validate_portfolio_with_policy expected
        {assumptions=List.rev auxiliary@assumptions,goal=goal,denied=denied}
      end)
     handle primary=>(W.close expected;raise primary))

  fun transport_query_with_policy expected value
      {assumptions=selection,goal=goal_conversion,denied=denied_conversion} =
    ((case value of PolicyValidation {work,...} =>
        if Portable.pointer_eq (expected,work) then () else
          raise ERR "transport_query_with_policy" "different original Work"
      | _ => raise ERR "transport_query_with_policy"
          "policy portfolio required";
      W.with_step expected (fn () =>
        let
          val _ = validate_with_policy expected value
          val PolicyValidation
            {graph,scope,limits,assumptions,goal,denied,...} = value
          val cap = #template_limit limits
          fun spend amount = W.spend_policy expected amount
          fun checked conversion source =
            let
              val _ = P.validate_conversion_for expected conversion
              val _ = P.validate_conversion_with_policy
                graph scope cap conversion
              val _ = spend 4
              val actual = P.conversion_source conversion
              val target = P.conversion_target conversion
              val _ = if actual=source () then () else
                raise ERR "transport_query_with_policy"
                  "conversion starts at a different current endpoint"
              val _ = if Type.compare
                    (G.type_of graph actual,Type.bool)=EQUAL andalso
                  Type.compare (G.type_of graph target,Type.bool)=EQUAL then
                  () else raise ERR "transport_query_with_policy"
                    "query conversion is not Boolean"
            in target end
          fun occurrence index =
            if index < (0:IntInf.int) then
              raise ERR "transport_query_with_policy"
                "negative current assumption occurrence"
            else
              let fun seek remaining facts =
                    (spend 2;case facts of
                       [] => raise ERR "transport_query_with_policy"
                         "current assumption occurrence absent"
                     | fact::rest => if remaining=0 then fact
                         else seek (remaining-1) rest)
              in seek index assumptions end
          fun transported fact NONE = fact
            | transported fact (SOME conversion) =
                (ignore (checked conversion (fn () => endpoint fact));
                 spend 4;binder_transport graph scope conversion fact)
          fun select [] = (spend 1;[])
            | select ({occurrence=index,conversion}::rest) =
                let val _ = spend 3
                    val fact = transported (occurrence index) conversion
                in fact::select rest end
          val selected = select selection
          (* Positive syntax is checked here, not added as a proof premise.
             The retained negative fact supplies all final Source transport;
             ordinary validation requires its exact negation of positive. *)
          val positive = case goal_conversion of NONE => goal
            | SOME conversion => checked conversion (fn () => goal)
          val negative = transported denied denied_conversion
          val result = validate_policy_portfolio expected
            {assumptions=selected,goal=positive,denied=negative}
          val _ = validate_with_policy expected value
          val _ = validate_with_policy expected result
        in result end))
     handle primary => (W.close expected;raise primary))

  fun current_facts_with_policy_for expected
      (value as PolicyValidation {work,assumptions,goal,denied,...}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "current_facts_with_policy_for" "different original Work";
      validate_with_policy expected value;
      {assumptions=assumptions,goal=goal,denied=denied})
     handle primary => (W.close expected;raise primary))
    | current_facts_with_policy_for expected _ =
      (W.close expected;raise ERR "current_facts_with_policy_for"
        "policy portfolio required")
  fun apply_with_policy work {law,premises,target} =
    ((let val owner=policy_expected work
          val graph= #graph owner val scope= #scope owner
          val sources= #sources owner
          val _=guard_policy_facts work graph scope sources (law::premises)
          val result=apply graph scope
            {law=law,premises=premises,target=target}
          val _=guard_policy_facts work graph scope sources [result]
      in result end)
     handle primary => (W.close work;raise primary))
  structure Scope = SmtReplayOwnedScopeReceipt
  type closed_owner =
    {work:W.portfolio,frame:Scope.receipt,graph:G.graph,scope:G.scope,
     root:G.scope,sources:S.sources,limits:RP.semantic_policy,
     epoch:int,symbols:int}
  datatype closed_program = ClosedProgram of
    {owner:closed_owner,facts:fact list,roots:G.node list,
     closed_facts:P.closed_fact list,conversions:P.closed_conversion list}
  fun closed_owner work frame : closed_owner =
    let val actual = Scope.description_with_policy_for work frame
    in {work=work,frame=frame,graph= #graph actual,scope= #scope actual,
      root= #root actual,sources= #sources actual,limits= #limits actual,
      epoch=Type.type_epoch (),symbols=Term.term_epoch ()} end
  fun closed_active expected (owner:closed_owner) =
    (if Portable.pointer_eq (expected,#work owner) then () else
       raise ERR "closed_program" "different original Work";
     let val actual = Scope.description_with_policy_for expected (#frame owner)
     in if Portable.pointer_eq (#graph actual,#graph owner) andalso
         #root actual= #root owner andalso #scope actual= #scope owner andalso
         Portable.pointer_eq (#sources actual,#sources owner) andalso
         #limits actual= #limits owner andalso
         Type.type_epoch ()= #epoch owner andalso
         Term.term_epoch ()= #symbols owner then () else
       raise ERR "closed_program" "different lexical owner or epoch" end)
  (* This private walk proves closure independently of query validation.
     Source-bearing rows cannot become closed merely by having no currently
     selected query premises. Complete dependency endpoints are checked. *)
  fun closed_inventory expected (owner:closed_owner) inputs =
    let
      val _ = closed_active expected owner
      val graph = #graph owner val scope = #scope owner
      val template = #template_limit (#limits owner)
      val used = ref (0:IntInf.int)
      fun charge amount =
        (closed_active expected owner;W.spend_policy expected amount;
         used := !used+amount;
         if RP.allows template (!used) then () else
           raise ERR "closed_program" "closed dependency template exceeded")
      val seen = ref (Redblackmap.mkDict Int.compare :
        (int,fact) Redblackmap.dict)
      val roots = ref ([]:G.node list)
      val closed_facts = ref ([]:P.closed_fact list)
      val conversions = ref ([]:P.closed_conversion list)
      fun node current = (charge 1;visible graph scope current;
        ignore (G.view graph current);roots := current :: !roots)
      fun recorded plan =
        (charge 1;
         P.validate_closed_fact_in_scope_with_policy_for expected
           {frame= #frame owner,fact=plan};
         closed_facts := plan :: !closed_facts)
      fun conversion plan =
        (charge 1;P.validate_conversion_for expected plan;
         P.validate_conversion_with_policy graph scope template plan;
         conversions := plan :: !conversions)
      fun visit (fact as Fact {identity,graph=other,scope=held,node=current,
                              row}) =
        (closed_active expected owner;
         if Portable.pointer_eq (graph,other) andalso scope=held then () else
           raise ERR "closed_program" "different closed graph or scope";
         charge 1;
         case Redblackmap.peek (!seen,identity) of SOME saved =>
           if Portable.pointer_eq (fact,saved) then () else
             raise ERR "closed_program" "private fact identity collision"
         | NONE =>
           let
             val _ = case row of Closed _ => () | RecordedClosed _ => ()
               | Apply _ => () | _ => raise ERR "closed_program"
                   "Source-bearing dependency in closed programme"
             val _ = case row of
                 Closed recipe =>
                   (C.validate_conversion_with_policy expected recipe;
                    (* Keep the constructor/schema root closure as well as
                       the ordinary paid inventory; template reservations
                       cannot stand in for either recursive walk. *)
                    List.app node
                      (C.graph_roots_with_policy expected graph scope recipe);
                    if C.graph_source recipe=current andalso
                        (case G.view graph (C.graph_result recipe) of
                           G.Constant _ => Term.same_const
                             (G.representative graph (C.graph_result recipe))
                             boolSyntax.T
                         | _ => false) then () else
                      raise ERR "closed_program" "closed schema endpoint";
                    List.app recorded
                      (C.graph_closed_facts_for expected recipe);
                    List.app conversion
                      (C.graph_conversions_for expected recipe))
               | RecordedClosed plan =>
                   (recorded plan;
                    if P.closed_node plan=current then () else
                      raise ERR "closed_program" "recorded endpoint differs")
               | Apply {law,premises} =>
                   (visit law;List.app visit premises;
                    if endpoint law=R.implication graph scope
                        (List.map endpoint premises) current then () else
                      raise ERR "closed_program"
                        "ordered law endpoints differ")
               | _ => raise ERR "closed_program" "unreachable Source row"
             (* Authenticate retained proof Work/frame headers before the
                fact endpoint is activated, including through Apply rows. *)
             val _ = node current
             val _ = if Type.compare (G.type_of graph current,Type.bool)=EQUAL
               then () else raise ERR "closed_program" "law is not Boolean"
             val _ = charge 1
             val _ = seen := Redblackmap.insert (!seen,identity,fact)
           in () end)
      val _ = List.app visit inputs
      val _ = closed_active expected owner
    in {roots=List.rev (!roots),closed_facts=List.rev (!closed_facts),
        conversions=List.rev (!conversions)} end
  fun scoped_closed_with_policy expected frame input =
    ((let val owner = closed_owner expected frame
          val fact = closed_using
            (fn graph => fn scope => fn schema => fn _ =>
              C.graph_schema_leaf graph scope
                {schema=schema,observe=fn () =>
                  (closed_active expected owner;
                   W.spend_policy expected 1)})
            (#graph owner) (#scope owner) input
          val _ = closed_inventory expected owner [fact]
      in fact end) handle primary => (W.close expected;raise primary))
  fun scoped_closed_at_with_policy expected frame
      {theorem,holes,operands,statement,template_limit,type_work_limit} =
    ((let val owner=closed_owner expected frame
          val graph= #graph owner val scope= #scope owner
          fun observe ()=
            (closed_active expected owner;W.spend_policy expected 1)
          val schema=C.checked_closed_graph_schema_at graph scope
            {theorem=theorem,holes=holes,operands=operands,source=statement,
             template_limit=template_limit,type_work_limit=type_work_limit,
             observe=observe,pay=W.spend_policy expected}
          val node=C.graph_schema_source schema
          val conversion=C.graph_schema_leaf graph scope
            {schema=schema,observe=observe}
          val _=observe ()
          val fact=Fact {identity=next_identity (),graph=graph,scope=scope,
            node=node,row=Closed conversion}
          val _=closed_inventory expected owner [fact]
      in fact end) handle primary=>(W.close expected;raise primary))
  fun scoped_recorded_closed_with_policy expected frame plan =
    ((let val owner = closed_owner expected frame
          val _ = P.validate_closed_fact_in_scope_with_policy_for expected
            {frame=frame,fact=plan}
          val fact = recorded_closed (#graph owner) (#scope owner) plan
          val _ = closed_inventory expected owner [fact]
      in fact end) handle primary => (W.close expected;raise primary))
  fun scoped_apply_with_policy expected frame {law,premises,target} =
    ((let val owner = closed_owner expected frame
          val _ = closed_inventory expected owner (law::premises)
          val fact = apply (#graph owner) (#scope owner)
            {law=law,premises=premises,target=target}
          val _ = closed_inventory expected owner [fact]
      in fact end) handle primary => (W.close expected;raise primary))
  fun closed_program_with_policy expected frame facts =
    ((let val owner = closed_owner expected frame
          val data = closed_inventory expected owner facts
      in ClosedProgram {owner=owner,facts=facts,roots= #roots data,
        closed_facts= #closed_facts data,conversions= #conversions data} end)
     handle primary => (W.close expected;raise primary))
  fun closed_program_data_with_policy_for expected
      (ClosedProgram {owner,facts,roots,closed_facts,conversions}) =
    ((closed_active expected owner;
      ignore (closed_inventory expected owner facts);
      {roots=roots,closed_facts=closed_facts,conversions=conversions})
     handle primary => (W.close expected;raise primary))
  fun closed_assembler_with_policy expected
      (program as ClosedProgram {owner,facts,...}) block =
    ((W.with_step expected (fn () =>
      let
        val _ = closed_active expected owner
        val graph = #graph owner val scope = #scope owner
        fun valid () =
          let val _ = closed_active expected owner
              val actual = P.policy_native_block_owner_for expected block
              val _ = if Portable.pointer_eq (#graph actual,graph) andalso
                  #scope actual=scope andalso null (P.sources block) then ()
                else raise ERR "closed_assembler"
                  "different frame or nonempty Source context"
          in ignore (closed_program_data_with_policy_for expected program)
          end
        val _ = valid ()
        val built = ref ([]:(fact * P.edge) list)
        fun saved _ [] = NONE
          | saved fact ((held,edge)::rest) =
              (W.spend_policy expected 1;
               if Portable.pointer_eq (fact,held) then SOME edge else
                 saved fact rest)
        fun rule opcode premises = P.execute_primitive_with_policy expected
          (P.prepare_primitive_with_policy expected block opcode premises)
        fun equality recipe =
          let val converted = C.graph_assemble_with_policy
                expected graph block recipe
          in rule P.EqualityMP [P.constructor_with_policy expected block
            (C.graph_equality recipe),converted] end
        fun truth () = P.execute_closed_named_inst_with_policy expected
          (P.prepare_closed_named_inst_with_policy expected block
            {substitution=[],theorem=boolTheory.TRUTH})
        fun build (fact as Fact {node,row,...}) =
          (valid ();W.spend_policy expected 2;ignore (P.name block node);
           case saved fact (!built) of SOME edge => edge
           | NONE =>
             let val edge = case row of
                   RecordedClosed plan => P.closed block plan
                 | Closed recipe =>
                     let val equation = rule P.Transitivity
                           [equality recipe,
                            P.definition block (C.graph_result recipe)]
                     in rule P.EqualityMP
                       [rule P.Symmetry [equation],truth ()] end
                 | Apply {law,premises} =>
                     R.apply_implication_law_with_policy expected graph block
                       {law=(endpoint law,build law),target=node,
                        premises=List.map (fn premise =>
                          (endpoint premise,build premise)) premises}
                 | _ => raise ERR "closed_assembler"
                     "Source-bearing dependency in closed programme"
                 val _ = valid () val _ = W.spend_policy expected 1
                 val _ = built := (fact,edge):: !built
             in edge end)
        fun query _ [] = NONE
          | query node (fact::rest) =
              (W.spend_policy expected 2;
               if endpoint fact=node then SOME fact else query node rest)
        fun assemble node = W.with_step expected (fn () =>
          (valid ();W.spend_policy expected 1;ignore (P.name block node);
           let val result = Option.map build (query node facts)
               val _ = valid ()
           in result end))
      in assemble end))
     handle primary => (W.close expected;raise primary))
end
