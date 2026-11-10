(* Copyright (c) 2026 The HOL4 contributors. *)

structure SmtReplaySource :> SmtReplaySource =
struct
  open SmtReplayGraph
  structure G = SmtReplayGraph
  structure A = SmtReplayOriginalAcquisition
  val ERR = Feedback.mk_HOL_ERR "SmtReplaySource"

  datatype sources = Sources of
    {graph : G.graph, scope : G.scope,
     goal : G.source, assumptions : G.source list,
     denied : G.source, allowed : Term.term list Array.array,
     ordinary : Term.term list Array.array,work_claimed : bool ref}
    | OriginalSources of A.source_binding

  fun active (Sources {graph,scope,...}) = G.validate_scope graph scope
    | active (OriginalSources binding) =
        A.source_binding_require_ready binding


  val buckets = 4093
  val hint = SmtReplayImport.pointer_bucket 4 buckets
  fun put table term =
    let val index = hint term in
      Array.update (table, index, term :: Array.sub (table, index))
    end
  fun member table term =
    List.exists (fn saved => Portable.pointer_eq (term, saved))
      (Array.sub (table, hint term))

  fun clean theorem =
    let val (oracles, _) = Tag.dest_tag (Thm.tag theorem) in
      List.all (fn oracle => oracle = "DISK_THM") oracles andalso
      List.null (Tag.axioms_of (Thm.tag theorem))
    end

  fun new graph scope maximum {goal, assumptions} =
    let
      val _ = G.validate_scope graph scope
      fun boolean term =
        if Type.compare (Term.type_of term, Type.bool) = EQUAL then ()
        else raise ERR "new" "non-Boolean source goal or assumption"
      val _ = List.app boolean (goal :: assumptions)
      val denied_term = boolSyntax.mk_neg goal
      val plans = G.plan_imports graph scope maximum
        (goal :: assumptions @ [denied_term])
      (* Per-source miss counts share one prospective memo, preserving
         the original sequential import's cross-source sharing credit. *)
      val imported = List.map G.execute_import plans
      val goal_source = List.hd imported
      val assumption_sources = List.take (List.tl imported,length assumptions)
      val denied = List.last imported
      val allowed = Array.array (buckets, [])
      val ordinary = Array.array (buckets, [])
      val _ = List.app (fn source =>
        let val term = G.representative graph (#node source) in
          put ordinary term; put allowed term
        end) assumption_sources
      val _ = put allowed (G.representative graph (#node denied))
      val _ = List.app (fn source =>
        if clean (#bridge source) then () else
          raise ERR "new" "unexpected source bridge tags")
        (goal_source :: denied :: assumption_sources)
    in Sources {graph = graph, scope = scope, goal = goal_source,
      assumptions = assumption_sources, denied = denied,
      allowed = allowed, ordinary = ordinary,work_claimed = ref false} end

  fun owning_graph (sources as Sources {graph,...}) =
    (active sources;graph)
    | owning_graph (OriginalSources binding) =
        (A.source_binding_require_ready binding;
         #graph (A.source_binding_header binding))

  fun owning_scope (sources as Sources {scope,...}) =
    (active sources;scope)
    | owning_scope (OriginalSources binding) =
        (A.source_binding_require_ready binding;
         #root (A.source_binding_header binding))


  fun claim_invocation_work (sources as Sources {work_claimed,...}) =
    (active sources;
     if !work_claimed then raise ERR "claim_invocation_work"
       "original Source work invocation already claimed"
     else work_claimed := true)

    | claim_invocation_work (OriginalSources binding) =
        A.source_binding_refuse_legacy binding

  (* Pure immutable ownership DATA. No view/proof/lifetime grant. The
     original Work bootstrap authenticates and pays its G path first. *)
  fun owner_for_scope_guard (Sources {graph,scope,...}) =
    {graph=graph,scope=scope}
    | owner_for_scope_guard (OriginalSources binding) =
        let val {graph,root}=A.source_binding_header binding
        in {graph=graph,scope=root} end

  fun claim_invocation_work_with_path
      (Sources {graph,scope,work_claimed,...}) path =
    (G.validate_scope_path graph scope path;
     if !work_claimed then raise ERR "claim_invocation_work"
       "original Source work invocation already claimed"
     else work_claimed := true)

    | claim_invocation_work_with_path (OriginalSources binding) _ =
        A.source_binding_refuse_legacy binding

  (* An ownership-checked failed bootstrap consumes this SAME attempt,
     including insufficient setup budget. No Work/proof/allowance issued. *)
  fun consume_scope_guard_attempt (Sources {work_claimed,...}) =
    work_claimed := true
    | consume_scope_guard_attempt (OriginalSources binding) =
        A.source_binding_consume_attempt binding


  fun original_goal (sources as Sources {goal,assumptions,...}) =
    (active sources; (List.map #original assumptions,#original goal))
    | original_goal (OriginalSources binding) =
        A.source_binding_original binding


  fun reconciliation_sources
      (sources as Sources {denied,assumptions,...}) =
    (active sources;denied :: assumptions)
    | reconciliation_sources (OriginalSources binding) =
        A.source_binding_reconciliation binding


  fun goal_source (sources as Sources {goal,...}) =
    (active sources;goal)
    | goal_source (OriginalSources binding) =
        #goal (A.source_binding_sources binding)


  fun canonical_goal (sources as Sources {graph, goal, ...}) =
    (active sources;G.representative graph (#node goal))
    | canonical_goal (OriginalSources binding) =
        A.source_binding_canonical_goal binding

  fun assumption_nodes (sources as Sources {assumptions, ...}) =
    (active sources;List.map #node assumptions)
    | assumption_nodes (OriginalSources binding) =
        A.source_binding_assumption_nodes binding

  fun denied_goal_node (sources as Sources {denied, ...}) =
    (active sources;#node denied)
    | denied_goal_node (OriginalSources binding) =
        #node (#denied (A.source_binding_sources binding))

  fun goal_bridge (sources as Sources {goal, ...}) =
    (active sources;#bridge goal)
    | goal_bridge (OriginalSources binding) =
        #bridge (#goal (A.source_binding_sources binding))


  fun check_hypotheses operation table theorem =
    if List.all (member table) (Thm.hyp theorem) then () else
      raise ERR operation "hypothesis is not a retained permitted source"

  fun check_contradiction (sources as Sources {allowed, ...}) theorem =
    (active sources;
     if Portable.pointer_eq (Thm.concl theorem, boolSyntax.F) orelse
        (Term.is_const (Thm.concl theorem) andalso
         Term.same_const (Thm.concl theorem) boolSyntax.F) then ()
     else raise ERR "check_contradiction" "replay did not prove F";
     check_hypotheses "check_contradiction" allowed theorem;
     if clean theorem then () else
       raise ERR "check_contradiction" "unexpected replay tags")
    | check_contradiction (OriginalSources binding) theorem =
        A.source_binding_check_contradiction binding theorem


  fun check_goal (sources as Sources {goal, ordinary, ...}) theorem =
    (active sources;
     if Portable.pointer_eq (Thm.concl theorem, #original goal) then () else
       raise ERR "check_goal" "source conclusion was not retained exactly";
     check_hypotheses "check_goal" ordinary theorem;
     if clean theorem then () else
       raise ERR "check_goal" "unexpected replay tags")
    | check_goal (OriginalSources binding) theorem =
        A.source_binding_check_goal binding theorem


  fun close_contradiction (sources as Sources _) theorem =
    let
      val _ = check_contradiction sources theorem
      (* Delete the canonical denied goal from its canonical hypothesis set.
         Only then transport the conclusion to the exact original object. *)
      val canonical = Thm.CCONTR (canonical_goal sources) theorem
      val result = Thm.EQ_MP (Thm.SYM (goal_bridge sources)) canonical
      val _ = check_goal sources result
    in result end
    | close_contradiction (OriginalSources binding) theorem =
        A.source_binding_close_contradiction binding theorem
  fun new_with_policy graph scope maximum {goal, assumptions} =
    let
      val _ = G.validate_scope graph scope
      fun boolean term =
        if Type.compare (Term.type_of term, Type.bool) = EQUAL then ()
        else raise ERR "new" "non-Boolean source goal or assumption"
      val _ = List.app boolean (goal :: assumptions)
      val denied_term = boolSyntax.mk_neg goal
      val plans = G.plan_imports_with_policy graph scope maximum
        (goal :: assumptions @ [denied_term])
      (* Per-source miss counts share one prospective memo, preserving
         the original sequential import's cross-source sharing credit. *)
      val imported = List.map G.execute_import_with_policy plans
      val goal_source = List.hd imported
      val assumption_sources = List.take (List.tl imported,length assumptions)
      val denied = List.last imported
      val allowed = Array.array (buckets, [])
      val ordinary = Array.array (buckets, [])
      val _ = List.app (fn source =>
        let val term = G.representative graph (#node source) in
          put ordinary term; put allowed term
        end) assumption_sources
      val _ = put allowed (G.representative graph (#node denied))
      val _ = List.app (fn source =>
        if clean (#bridge source) then () else
          raise ERR "new" "unexpected source bridge tags")
        (goal_source :: denied :: assumption_sources)
    in Sources {graph = graph, scope = scope, goal = goal_source,
      assumptions = assumption_sources, denied = denied,
      allowed = allowed, ordinary = ordinary,work_claimed = ref false} end


  (* This Source object exists before acquisition and remains the SAME
     object after the private A publication. No Ready wrapper is adopted. *)
  fun new_pending seed =
    let val work = A.claim_work seed
    in
      (A.with_action work
        (fn () => OriginalSources (A.bind_pending_sources work seed)))
      handle primary => (A.retire_work work;raise primary)
    end
  fun claim_original_work (OriginalSources binding) =
        A.source_binding_claim_work binding
    | claim_original_work (Sources _) =
        raise ERR "claim_original_work" "not an original acquisition Source"
  fun validate_original_work expected (OriginalSources binding) =
        A.source_binding_validate_work expected binding
    | validate_original_work expected (Sources _) =
        (A.retire_work expected;
         raise ERR "validate_original_work" "different original Source")
end
