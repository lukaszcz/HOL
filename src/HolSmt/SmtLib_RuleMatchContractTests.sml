(* Copyright (c) 2026 The HOL4 contributors.
 * Contract of the three rule matchers (fixed integer, fixed policy and
 * local-context) that share their closure-tree walk and matching operations.
 * Every assertion is a relation computed inside one run: an outcome against
 * another outcome of the same fixture, a boundary against the charge that
 * the same fixture reports.  No number captured from earlier code is
 * pinned.  The fixtures follow the selftest postludes of the same matchers.
 *)
structure SmtLib_RuleMatchContractTests =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure P = SmtReplayProof
  structure RP = SmtReplayResourcePolicy
  structure NC = SmtReplayNativeContract
  structure C = SmtLib_GraphNumericRewriteCatalogue
  structure M = SmtLib_GraphNumericRuleMatch
  structure Scope = SmtReplayOwnedScopeReceipt
  structure T = SmtLib_CompactCarrierScheduler
  structure N = SmtLib_OwnedNaturalSequentTransfer
  structure Q = SmtLib_OwnedStrippedNaturalQuery
  structure Ctx = SmtLib_OwnedLocalContextRules
  structure L = SmtLib_LocalContextRuleMatch

  fun require message yes = if yes then () else testutils.die message
  fun test label action = (testutils.tprint label;action ();testutils.OK ())
  fun refusal action = (ignore (action ());NONE)
    handle Feedback.HOL_ERR detail => SOME (Feedback.message_of detail)
  fun refuses action = Option.isSome (refusal action)

  (* One complete matcher run: how it ended and what it charged. *)
  datatype outcome = Done of IntInf.int | Refused of string
  fun done (Done _) = true | done _ = false
  fun refused_with text (Refused message) = message = text
    | refused_with _ _ = false
  fun attempt (run : unit -> IntInf.int) =
    Done (run ()) handle Feedback.HOL_ERR detail =>
      Refused (Feedback.message_of detail)

  (* Smallest budget (in [0,hi]) for which the monotone predicate holds. *)
  fun least hi holds =
    let fun go lo hi = if lo >= hi then lo else
          let val mid = (lo + hi) div 2
          in if holds mid then go lo mid else go (mid + 1) hi end
    in go 0 hi end

  (* ---- Fixed integer matcher ---- *)

  local
    val cap = 50000
    val ample = 16000000
    fun setup budget =
      let val graph = G.new () val scope = G.root_scope graph
          val sources = S.new graph scope cap
            {goal = boolSyntax.T,assumptions = []}
          val work = W.begin graph scope sources
            {limits = {input_limit = 5,output_limit = cap,
               template_limit = cap},work_limit = budget}
          val catalogue = C.execute (C.prepare
            (C.begin work {check_type = fn _ => ()}))
          val owner = M.begin work catalogue
      in (graph,scope,work,owner,M.compile owner) end
    fun schema schemas original =
      valOf (List.find (fn s => Portable.pointer_eq (M.original s,original))
        schemas)
    fun query graph scope term =
      let val imported = G.import graph scope cap term
          val opened = G.record_opened_view graph scope cap (#node imported)
      in G.closure_root graph scope (#node opened) end
    val division = ``integer$int_of_num ((n:num) DIV m)``
    fun prepare (graph,scope,_,owner,schemas) term =
      M.prepare owner {schema = schema schemas HolSmtTheory.INT_NUM_EDIV,
        caller = scope,traversal = scope,target = query graph scope term}
    fun matched fixture term = case prepare fixture term of
        M.Matched value => value
      | _ => raise Fail "fixed integer division did not match"
    fun run budget () =
      let val fixture as (_,_,work,_,_) = setup budget
          val instance = M.instantiate (matched fixture division)
            {check_type = fn _ => ()}
          val fact = M.instance_fact_for work instance
      in require "instance fact lost its theorem"
           (null (Thm.hyp (P.closed_original fact)));
         IntInf.fromInt (#charged (W.audit work)) end
  in
    fun int_tests () =
      let
        val _ = test "Int matcher: successful instance keeps Source and Work"
          (fn () =>
            let val fixture as (_,_,work,_,_) = setup ample
                val instance = M.instantiate (matched fixture division)
                  {check_type = fn _ => ()}
                val th = P.closed_original (M.instance_fact_for work instance)
            in require "instance changed its query or retained a hypothesis"
              (null (Thm.hyp th) andalso Term.aconv
                 (boolSyntax.lhs (Thm.concl th)) division andalso
               not (#retired (W.audit work))) end)
        val _ = test "Int matcher: NoMatch is semantic and keeps the owner"
          (fn () =>
            let val fixture as (_,_,work,_,_) = setup ample
                val missed = prepare fixture
                  ``integer$int_of_num ((n:num) * m)``
            in require "mismatch retired the owner or was not NoMatch"
              ((case missed of M.NoMatch => true | _ => false) andalso
               not (#retired (W.audit work))) end)
        val _ = test "Int matcher: foreign schema retires only its owner"
          (fn () =>
            let val a as (_,_,wa,_,schemas_a) = setup ample
                val b as (graph,scope,wb,owner,_) = setup ample
                val foreign = schema schemas_a HolSmtTheory.INT_NUM_EDIV
                val stopped = refuses (fn () => M.prepare owner
                  {schema = foreign,caller = scope,traversal = scope,
                   target = query graph scope division})
            in require "foreign schema was accepted or retired its holder"
              (stopped andalso #retired (W.audit wb) andalso
               not (#retired (W.audit wa))) end)
        val _ = test "Int matcher: retired owner is refused"
          (fn () =>
            let val fixture as (_,_,work,_,_) = setup ample
                val value = matched fixture division
                val _ = W.close work
                val stopped_prepare = refuses (fn () =>
                  prepare fixture division)
                val stopped_instance = refuses (fn () =>
                  M.instantiate value {check_type = fn _ => ()})
            in require "retired owner still matched or instantiated"
              (stopped_prepare andalso stopped_instance) end)
        val _ = test "Int matcher: Work budget boundary is exact"
          (fn () =>
            let val total = case attempt (run ample) of Done n => n
                  | Refused m => raise Fail ("ample run refused: " ^ m)
                val exact = attempt (run (IntInf.toInt total))
                val short = attempt (run (IntInf.toInt total - 1))
            in require "budget equal to the charge refused"
                 (case exact of Done n => n = total | _ => false);
               require "budget below the charge was accepted"
                 (not (done short)) end)
      in () end
  end

  (* ---- Fixed policy matcher ---- *)

  local
    val unlimited : RP.semantic_policy =
      {input_limit = RP.Uncapped,output_limit = RP.Uncapped,
       template_limit = RP.Uncapped}
    fun request allowance : NC.limits =
      {semantic_limits = {input_limit = 100000,output_limit = 100000,
         template_limit = 100000},
       import_limit = 100000,type_work_limit = allowance}
    fun setup budget allowance =
      let val graph = G.new () val scope = G.root_scope graph
          val sources = S.new_with_policy graph scope RP.Uncapped
            {goal = boolSyntax.T,assumptions = []}
          val work = W.begin_with_policy graph scope sources
            {limits = unlimited,work_limit = budget}
          val native = NC.capture work (request allowance)
          val catalogue = C.execute_with_policy (C.prepare_with_policy
            (C.begin_with_policy work
              {native_contract = native,check_type = fn _ => ()}))
          val owner = M.begin_with_policy work catalogue
      in (graph,scope,work,owner,M.compile_with_policy owner) end
    fun schema schemas original =
      valOf (List.find (fn s =>
        Portable.pointer_eq (M.original_with_policy s,original)) schemas)
    fun query graph scope term =
      let val imported = G.import_with_policy graph scope
            (RP.AtMost 100000) term
          val opened = G.record_opened_view_with_policy graph scope
            (RP.AtMost 100000) (#node imported)
      in G.closure_root graph scope (#node opened) end
    val guarded = ``integer$int_of_num (Num (i:int))``
    fun prepare (graph,scope,_,owner,schemas) term =
      M.prepare_with_policy owner
        {policy_schema = schema schemas HolSmtTheory.NUM_TO_INT_GUARDED,
         caller = scope,traversal = scope,target = query graph scope term}
    fun matched fixture term = case prepare fixture term of
        M.PolicyMatched value => value
      | _ => raise Fail "fixed guarded cancellation did not match"
    fun run budget allowance () =
      let val fixture as (_,_,work,_,_) = setup budget allowance
          val instance = M.instantiate_with_policy
            (matched fixture guarded) {check_type = fn _ => ()}
          val fact = M.instance_fact_with_policy_for work instance
      in require "policy instance fact lost its theorem"
           (null (Thm.hyp (P.closed_original fact)));
         #charged (W.audit_policy work) end
    val ample = 20000000
    val remaining = RP.Uncapped
  in
    fun policy_tests () =
      let
        val _ = test "Policy matcher: successful instance keeps Source"
          (fn () =>
            let val fixture as (_,_,work,_,_) = setup remaining ample
                val value = matched fixture guarded
                val d = M.describe_with_policy_for work value
                val instance = M.instantiate_with_policy value
                  {check_type = fn _ => ()}
                val th = P.closed_original
                  (M.instance_fact_with_policy_for work instance)
            in require "guarded instance lost its condition or closure"
              (length (#conditions d) = 1 andalso null (Thm.hyp th) andalso
               boolSyntax.is_imp (Thm.concl th) andalso
               not (#retired (W.audit_policy work))) end)
        val _ = test "Policy matcher: NoMatch is semantic and keeps the owner"
          (fn () =>
            let val fixture as (_,_,work,_,_) = setup remaining ample
                val missed = prepare fixture
                  ``integer$int_of_num ((n:num) * m)``
            in require "mismatch retired the owner or was not NoMatch"
              ((case missed of M.PolicyNoMatch => true | _ => false) andalso
               not (#retired (W.audit_policy work))) end)
        val _ = test "Policy matcher: foreign schema retires only its owner"
          (fn () =>
            let val a as (_,_,wa,_,schemas_a) = setup remaining ample
                val b as (graph,scope,wb,owner,_) = setup remaining ample
                val foreign =
                  schema schemas_a HolSmtTheory.NUM_TO_INT_GUARDED
                val stopped = refuses (fn () => M.prepare_with_policy owner
                  {policy_schema = foreign,caller = scope,traversal = scope,
                   target = query graph scope guarded})
            in require "foreign schema was accepted or retired its holder"
              (stopped andalso #retired (W.audit_policy wb) andalso
               not (#retired (W.audit_policy wa))) end)
        val _ = test "Policy matcher: retired owner is refused"
          (fn () =>
            let val fixture as (_,_,work,_,_) = setup remaining ample
                val value = matched fixture guarded
                val _ = W.close work
                val stopped_prepare = refuses (fn () =>
                  prepare fixture guarded)
                val stopped_instance = refuses (fn () =>
                  M.instantiate_with_policy value {check_type = fn _ => ()})
            in require "retired owner still matched or instantiated"
              (stopped_prepare andalso stopped_instance) end)
        val _ = test "Policy matcher: Work budget boundary is exact"
          (fn () =>
            let val total = case attempt (run remaining ample) of Done n => n
                  | Refused m => raise Fail ("ample run refused: " ^ m)
                val exact = attempt (run (RP.AtMost total) ample)
                val short = attempt (run (RP.AtMost (total - 1)) ample)
            in require "budget equal to the charge refused"
                 (case exact of Done n => n = total | _ => false);
               require "budget below the charge was accepted"
                 (not (done short)) end)
        val _ = test "Policy matcher: native allowance boundary is exact"
          (fn () =>
            let val total = case attempt (run remaining ample) of Done n => n
                  | Refused m => raise Fail ("ample run refused: " ^ m)
                fun ok allowance = done (attempt
                  (run remaining (IntInf.toInt allowance)))
                val least_allowance = least (IntInf.toInt total)
                  (fn n => ok (IntInf.fromInt n))
                val at = attempt (run remaining least_allowance)
                val below = attempt (run remaining (least_allowance - 1))
            in require "tightest native allowance was not found"
                 (least_allowance > 0 andalso done at);
               require "native allowance one below the boundary was accepted"
                 (not (done below));
               require "tightest allowance changed the Work charge"
                 (case at of Done n => n = total | _ => false) end)
      in () end
  end

  (* ---- Local-context matcher ---- *)

  local
    val cap = 100000
    fun setup budget assumptions goal =
      let val graph = G.new () val root = G.root_scope graph
          val sources = S.new graph root cap
            {assumptions = assumptions,goal = goal}
          val work = W.begin graph root sources
            {limits = {input_limit = cap,output_limit = cap,
               template_limit = cap},work_limit = budget}
          val traversal = T.begin work
            {check_type = fn _ => (),scope_opened = fn _ => ()}
          val natural = N.begin work
            {traversal = traversal,check_type = fn _ => (),
             scope_opened = fn _ => ()}
          val transferred = N.execute (N.prepare natural)
          val qo = Q.begin work {transfer = transferred,
            check_type = fn _ => (),scope_opened = fn _ => ()}
          val query = Q.execute (Q.prepare qo)
          val catalogue = Ctx.execute (Ctx.prepare (Ctx.begin work
            {query = query,check_type = fn _ => ()}))
          val matcher = L.begin work catalogue
          val scope = #scope (Scope.description_for work
            (#frame (Q.description_for work query)))
      in {graph = graph,sources = sources,work = work,query = query,
          matcher = matcher,schemas = L.compile matcher,scope = scope} end
    fun goal e = #goal (Q.description_for (#work e) (#query e))
    fun prepare e schema target = L.prepare (#matcher e)
      {schema = schema,caller = #scope e,traversal = #scope e,
       target = G.closure_root (#graph e) (#scope e) target}
    (* First schema that matches (or the first higher-order refusal). *)
    fun survey e target =
      let fun go [] = L.NoMatch
            | go (schema::rest) = case prepare e schema target of
                L.NoMatch => go rest
              | other => other
      in go (#schemas e) end
    fun matched e target = case survey e target of
        L.Matched value => value
      | _ => raise Fail "expected genuine local match absent"
    val equal_hyps = [``(local_ctx_p:bool)=local_ctx_q``,
                      ``local_ctx_q:bool``]
    val equal_goal = ``local_ctx_p:bool``
    fun run budget () =
      let val e = setup budget equal_hyps equal_goal
          val instance = L.instantiate (matched e (goal e))
            {check_type = fn _ => ()}
          val fact = L.instance_fact_for (#work e) instance
      in ignore (P.closed_original fact);
         IntInf.fromInt (#charged (W.audit (#work e))) end
    fun is_no_match L.NoMatch = true | is_no_match _ = false
    fun is_higher_order L.NeedsHigherOrder = true | is_higher_order _ = false
  in
    fun local_tests () =
      let
        val big = 20000000
        val _ = test "Local matcher: successful instance keeps Source"
          (fn () =>
            let val e = setup big equal_hyps equal_goal
                val instance = L.instantiate (matched e (goal e))
                  {check_type = fn _ => ()}
                val fact = L.instance_fact_for (#work e) instance
            in require "local instance retired its owner or lost its fact"
              (not (#retired (W.audit (#work e))) andalso
               Portable.pointer_eq (W.original_sources (#work e),
                 #sources e) andalso
               #node (L.instance_target_for (#work e) instance) = goal e
               andalso P.closed_node fact <> goal e) end)
        val _ = test "Local matcher: free Hyp variable stays rigid (NoMatch)"
          (fn () =>
            let val e = setup big [``(local_ctx_p:bool)=local_ctx_r``]
                  ``local_ctx_q:bool``
            in require "Hyp variable was instantiated to an unrelated goal"
              (is_no_match (survey e (goal e)) andalso
               not (#retired (W.audit (#work e)))) end)
        val _ = test "Local matcher: bound-only Hyp type variable is rigid"
          (fn () =>
            let val e = setup big
                  [``!local_ctx_x:'a. local_ctx_x=local_ctx_x``]
                  ``(0:num)=(0:num)``
                val node = case G.view (#graph e) (goal e) of
                    G.Application (partial,_) =>
                      (case G.view (#graph e) partial of
                         G.Application (_,left) => left
                       | _ => raise Fail "goal equality spine absent")
                  | _ => raise Fail "goal equality absent"
            in require "bound-only Hyp type was silently instantiated"
              (is_no_match (survey e node) andalso
               not (#retired (W.audit (#work e)))) end)
        val _ = test "Local matcher: binder capture needs higher order"
          (fn () =>
            let val e = setup big
                  [``!local_ctx_v:num. (local_ctx_k:(num->bool)->bool)
                      (\local_ctx_x:num. (local_ctx_c:num->bool)
                        local_ctx_v)``]
                  ``(local_ctx_k:(num->bool)->bool)
                      (\local_ctx_x:num. (local_ctx_c:num->bool)
                        local_ctx_x)``
            in require "capturing a bound variable was not reported"
              (is_higher_order (survey e (goal e)) andalso
               not (#retired (W.audit (#work e)))) end)
        val _ = test "Local matcher: foreign schema retires only its owner"
          (fn () =>
            let val a = setup big equal_hyps equal_goal
                val b = setup big equal_hyps equal_goal
                val foreign = hd (#schemas a)
                val stopped = refuses (fn () => prepare b foreign (goal b))
            in require "foreign schema was accepted or retired its holder"
              (stopped andalso #retired (W.audit (#work b)) andalso
               not (#retired (W.audit (#work a)))) end)
        val _ = test "Local matcher: retired owner is refused"
          (fn () =>
            let val e = setup big equal_hyps equal_goal
                val value = matched e (goal e)
                val _ = W.close (#work e)
                val stopped_prepare = refuses (fn () =>
                  prepare e (hd (#schemas e)) (goal e))
                val stopped_instance = refuses (fn () =>
                  L.instantiate value {check_type = fn _ => ()})
            in require "retired owner still matched or instantiated"
              (stopped_prepare andalso stopped_instance) end)
        val _ = test "Local matcher: Work budget boundary is exact"
          (fn () =>
            let val total = case attempt (run big) of Done n => n
                  | Refused m => raise Fail ("ample run refused: " ^ m)
                val exact = attempt (run (IntInf.toInt total))
                val short = attempt (run (IntInf.toInt total - 1))
            in require "budget equal to the charge refused"
                 (case exact of Done n => n = total | _ => false);
               require "budget below the charge was accepted"
                 (not (done short)) end)
      in () end
  end

  fun run () = (int_tests ();policy_tests ();local_tests ())
end
