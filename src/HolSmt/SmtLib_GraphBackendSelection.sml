(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphBackendSelection :> SmtLib_GraphBackendSelection =
struct
  structure Q = SmtLib_GraphQueryAnalysis
  structure Features = SmtLib_GraphQueryFeatures
  type carrier = Q.carrier
  type selection =
    {goal:carrier,assumptions:carrier list,
     sets:carrier list,bags:carrier list,raw_numbers:carrier list,
     finite_sets:carrier list,finite_bags:carrier list,
     sequence_emission:bool,set_backend:SmtLib.outbound_set_backend,
     bag_backend:SmtLib.outbound_bag_backend,
     target:{solver:string,version:string option} option}
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphBackendSelection"
  fun compare_key ((ls,ln),(rs,rn)) =
    case Int.compare (ls,rs) of
      EQUAL => Int.compare (ln,rn) | result => result
  fun compare_memo ((lt,lc,lk),(rt,rc,rk)) =
    case String.compare (lt,rt) of
      EQUAL => (case List.collate (List.collate compare_key) (lc,rc) of
          EQUAL => compare_key (lk,rk) | result => result)
    | result => result

  fun with_finite_trace (context:Q.outbound_context) report
      {operations,target,emit_sequences} action =
    let
      val operations : carrier SmtLib.outbound_term_translation_operations =
        operations
      fun guard current = ignore ((#key context) current)
      val _ = guard (#goal context)
      val sequence_emission = emit_sequences andalso
        #eligible (Features.sequence_eligibility context)
      val {sets,bags,raw_numbers,shadow_same} =
        (#collection_terms context) ()
      val analysis = #analysis context
      val set_analysis = #set_analysis analysis
      val bag_analysis = #bag_analysis analysis
      val cache = ref (Redblackmap.mkDict compare_memo)
      fun memoize tag contexts current compute =
        let
          val _ = guard (#goal context)
          val identity = (tag,List.map (List.map (#key context)) contexts,
            (#key context) current)
          fun valid () =
            (guard current;List.app (List.app guard) contexts;
             guard (#goal context))
        in case Redblackmap.peek (!cache,identity) of
            SOME result => (valid ();result)
          | NONE =>
              let val _ = (#step context) () val result = compute ()
                  val _ = valid ()
                  val _ = cache := Redblackmap.insert (!cache,identity,result)
              in result end
        end
      fun view current = case (#view context) current of
          Q.VariableView _ => SmtLib.BackendVariable
        | Q.ConstantView _ => SmtLib.BackendConstant
        | Q.ApplicationView pair => SmtLib.BackendApplication pair
        | Q.AbstractionView pair => SmtLib.BackendAbstraction pair
      val policy = SmtLib.outbound_backend_selection_with_finite_trace
        {view=view,type_of= #type_of context,
         strip_comb= #strip_comb context,same= #same context,
         shadow_same=shadow_same,free_variables= #free_variables context,
         same_const= #same_const operations,
         is_empty_set= #is_empty_set operations,
         is_univ_set= #is_univ_set operations,
         is_empty_bag= #is_empty_bag operations,
         is_parsed_bag_literal= #is_parsed_bag_literal operations,
         set_element_type= #set_element_type operations,
         bag_element_type= #bag_element_type operations,memoize=memoize}
        report
      val goal = (#assumptions context,#goal context)
      val {set_backend,bag_backend} = (#select policy) target
        {goal=goal,sets=sets,bags=bags,
         computed_set=not (null (#computed_applications set_analysis)),
         computed_bag=not (null (#computed_applications bag_analysis)),
         bound_set=fn () => #bound_application set_analysis,
         bound_bag=fn () => #bound_application bag_analysis,
         mixed_set=fn () => #mixed_argument set_analysis,
         mixed_bag=fn () => #mixed_argument bag_analysis}
      val finite_sets = (#finite_sets policy) (#assumptions context)
      val finite_bags = (#finite_bags policy) (#assumptions context)
      val _ = List.app guard
        (sets @ bags @ raw_numbers @ finite_sets @ finite_bags)
      val _ = guard (#goal context)
      val selection : selection =
        {goal= #goal context,assumptions= #assumptions context,
       sets=sets,bags=bags,raw_numbers=raw_numbers,
       finite_sets=finite_sets,finite_bags=finite_bags,
       sequence_emission=sequence_emission,
       set_backend=set_backend,bag_backend=bag_backend,target=target}
      fun checked predicate current =
        let val _ = guard (#goal context) val _ = guard current
            val result = predicate current
            val _ = guard current val _ = guard (#goal context)
        in result end
      fun hypothesis operands current = case operands [current] of
          [operand] => (guard operand;SOME operand)
        | _ => NONE
      val result = action
        {selection=selection,
         finite_set_term=checked ((#finite_set_term policy) finite_sets),
         finite_bag_term=checked ((#finite_bag_term policy) finite_bags),
         finite_set_hypothesis=checked (hypothesis (#finite_sets policy)),
         finite_bag_hypothesis=checked (hypothesis (#finite_bags policy))}
      val _ = guard (#goal context)
    in result
    end

  fun select_with_finite_trace context report options =
    with_finite_trace context report options (fn {selection,...} => selection)

  fun select context options =
    select_with_finite_trace context (fn _ => ()) options

  fun validate_selection (context:Q.outbound_context)
      (selection:selection) =
    let
      val expected = List.map (#key context)
        (#goal context :: #assumptions context)
      val actual = List.map (#key context)
        (#goal selection :: #assumptions selection)
      val _ = if expected=actual then () else
        raise ERR "with_context" "selection belongs to a different query"
    in List.app (fn current => ignore ((#key context) current))
      (#sets selection @ #bags selection @ #raw_numbers selection @
       #finite_sets selection @ #finite_bags selection) end

  fun install (context:Q.outbound_context) modes action =
    let
      fun guard () = ignore ((#key context) (#goal context))
      fun borrowed compute =
        (guard ();let val result = compute () val _ = guard () in result end)
      fun run (installed:SmtLib.outbound_backend_context) =
        let
          val state = #state installed
          val guarded : SmtLib.outbound_backend_context =
            {state={generated_forall=fn () =>
                 borrowed (#generated_forall state),
               sequence_emission=fn () => borrowed (#sequence_emission state),
               has_set_terms=fn () => borrowed (#has_set_terms state),
               native_set_backend=fn () =>
                 borrowed (#native_set_backend state),
               has_bag_terms=fn () => borrowed (#has_bag_terms state),
               native_bag_backend=fn () =>
                 borrowed (#native_bag_backend state)},
             snapshot=fn () => borrowed (#snapshot installed),
             translate_type=fn regime => fn input => borrowed
               (fn () => (#translate_type installed) regime input),
             sort_of_type=fn regime => fn dictionary => fn ty => borrowed
               (fn () => (#sort_of_type installed) regime dictionary ty)}
        in borrowed (fn () => action guarded) end
    in SmtLib.outbound_with_backend_context modes run end

  fun with_context (context:Q.outbound_context) (selection:selection) action =
    (validate_selection context selection;
     install context
      {sequence_emission= #sequence_emission selection,
       set_backend= #set_backend selection,bag_backend= #bag_backend selection,
       has_set_terms=not (null (#sets selection)),
       has_bag_terms=not (null (#bags selection))} action)

  structure W = SmtReplayInvocationWork
  structure GP = SmtLib_GraphPreprocess
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  datatype transport = Transport of
    {work:W.portfolio,original:GP.graph_query,graph:G.graph,scope:G.scope,
     sources:S.sources,roots:Q.scoped_node list,seeds:Q.marker_seeds,
     sequence_emission:bool,set_backend:SmtLib.outbound_set_backend,
     bag_backend:SmtLib.outbound_bag_backend,
     target:{solver:string,version:string option} option}

  fun capture_transport expected original (context:Q.outbound_context)
      (selection:selection) =
    ((let
      val _ = GP.validate_query_with_policy expected original
      val _ = validate_selection context selection
      val sources = W.original_sources expected
      val {graph,scope} = S.owner_for_scope_guard sources
      val markers = (#collection_terms context) ()
      fun same_positions (selected,actual) =
        List.map (#key context) selected = List.map (#key context) actual
      val _ = if same_positions (#sets selection,#sets markers) andalso
          same_positions (#bags selection,#bags markers) andalso
          same_positions (#raw_numbers selection,#raw_numbers markers)
        then () else raise ERR "capture_transport"
          "selection changed original analysis markers"
      fun scoped current = case (#graph_node context) current of
          SOME result => result
        | NONE => raise ERR "capture_transport"
            "original collection marker is an outbound recipe"
      val seeds : Q.marker_seeds =
        {graph=graph,scope=scope,sets=List.map scoped (#sets markers),
         bags=List.map scoped (#bags markers),
         raw_numbers=List.map scoped (#raw_numbers markers)}
      val roots = #roots (#set_analysis (#analysis context))
      val _ = ignore ((#key context) (#goal context))
      val _ = GP.validate_query_with_policy expected original
    in Transport {work=expected,original=original,graph=graph,scope=scope,
      sources=sources,roots=roots,seeds=seeds,
      sequence_emission= #sequence_emission selection,
      set_backend= #set_backend selection,bag_backend= #bag_backend selection,
      target= #target selection}
    end) handle primary => (W.close expected;raise primary))

  fun target_for_transport expected
      (Transport {work,original,target,...}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "target_for_transport" "different original Work";
      GP.validate_query_with_policy expected original;
      target) handle primary => (W.close expected;raise primary))

  fun with_original_context_with_policy expected
      (Transport {work,original,graph,scope,sources,roots,seeds,
                  sequence_emission,target,...}) open_opaque action =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "original_context" "different original Work";
      let
        val data = GP.query_nodes_with_policy_for expected original
        val _ = if Portable.pointer_eq (#graph data,graph) andalso
            #scope data=scope andalso
            Portable.pointer_eq (#sources data,sources) then () else
          raise ERR "original_context" "different original query owner"
        val _ = if List.map #node roots =
            (#goal data :: #assumptions data) andalso
            List.all (fn current => #scope current=scope) roots then () else
          raise ERR "original_context"
            "snapshot belongs to a different original query"
      in
        SmtLib_GraphTranslation.with_outbound_seeded_query_analysis_with_policy
          expected original
          open_opaque seeds (fn context => action
            {context=context,sequence_emission=sequence_emission,
             target=target})
      end) handle primary => (W.close expected;raise primary))

  fun with_transported_context_with_policy expected
      (Transport {work,original,graph,scope,sources,roots,seeds,
                  sequence_emission,set_backend,bag_backend,target=_})
      query open_opaque action =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "transport" "different original Work";
      let
        val original_data = GP.query_nodes_with_policy_for expected original
        val new_data = GP.query_nodes_with_policy_for expected query
        fun owner (actual_graph,actual_scope,actual_sources) =
          Portable.pointer_eq (actual_graph,graph) andalso actual_scope=scope
          andalso Portable.pointer_eq (actual_sources,sources)
        val _ = if owner (#graph original_data,#scope original_data,
              #sources original_data) andalso
            owner (#graph new_data,#scope new_data,#sources new_data)
          then () else
          raise ERR "transport" "different original query owner"
        val _ = if List.map #node roots =
            (#goal original_data :: #assumptions original_data) andalso
            List.all (fn current => #scope current=scope) roots then () else
          raise ERR "transport" "snapshot belongs to a different query"
      in
        SmtLib_GraphTranslation.with_outbound_seeded_query_analysis_with_policy
          expected query
          open_opaque seeds (fn context =>
          let
            val {sets,bags,...} = (#collection_terms context) ()
          in install context
            {sequence_emission=sequence_emission,set_backend=set_backend,
             bag_backend=bag_backend,has_set_terms=not (null sets),
             has_bag_terms=not (null bags)}
            (fn installed => action (context,installed)) end)
      end) handle primary => (W.close expected;raise primary))
end
