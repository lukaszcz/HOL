open HolKernel testutils

fun test (name, check) =
  (tprint name;
   if check () then OK () else die "failed")

fun residual tactic goal =
  #1 (Tactical.VALID tactic goal)

fun rewrite_rhs ss tm =
  snd
    (boolSyntax.dest_eq
      (concl (Conv.QCONV (simpLib.SIMP_CONV ss []) tm)))

val _ =
  test
    ("aesop_simp settype and attribute are registered without collision",
     fn () =>
       List.exists (equal "aesop_simp") (ThmSetData.all_set_types ()) andalso
       ThmAttribute.is_attribute "aesop_simp")

val _ =
  test
    ("aesop trace is registered at levels one through three",
     fn () =>
       List.exists
         (fn Feedback.TraceElt {name, max, ...} =>
           name = "aesop" andalso max = 3)
         (Feedback.traces ()))

val _ =
  test
    ("aesop simpset fixes conditional-rewrite depth at forty",
     fn () =>
       #cond_depth
         (simpLib.traversedata_for_ss (aesopData.aesop_ss ())) =
       SOME 40)

val _ =
  test
    ("aesop simpset uses the clasimp safe solver stack",
     fn () =>
       null
         (residual
           (simpLib.GEN_GLOBAL_SIMP_TAC {safe = true}
             {base =
                {strip = false, elimvars = false, droptrues = false,
                 oldestfirst = false},
              concl_in_fixpoint = false, imp_rebuild = false}
             (simpLib.clear_rules (aesopData.aesop_ss ())) [])
           ([boolSyntax.F], ``aesop_safe_solver_goal:bool``)))

val derived_lhs = ``aesop_derived_lhs:'a``
val derived_rhs = ``aesop_derived_rhs:'a``
val derived_rule =
  ASSUME (boolSyntax.mk_eq (derived_lhs, derived_rhs))
val derived_before =
  rewrite_rhs (aesopData.aesop_ss ()) derived_lhs
val derived_after =
  BasicProvers.with_simpset_updates
    (fn ss =>
      simpLib.++
        (ss,
         simpLib.named_rewrites "aesop-selftest-derived" [derived_rule]))
    (fn () => rewrite_rhs (aesopData.aesop_ss ()) derived_lhs)
    ()
val derived_restored =
  rewrite_rhs (aesopData.aesop_ss ()) derived_lhs

val _ =
  test
    ("aesop simpset cache derives from srw_ss updates",
     fn () =>
       aconv derived_before derived_lhs andalso
       aconv derived_after derived_rhs andalso
       aconv derived_restored derived_lhs)

val attribute_lhs = ``aesop_attribute_lhs:'a``
val attribute_rhs = ``aesop_attribute_rhs:'a``
val attribute_rule =
  ASSUME (boolSyntax.mk_eq (attribute_lhs, attribute_rhs))
val attribute_before =
  rewrite_rhs (aesopData.aesop_ss ()) attribute_lhs
val _ =
  ThmAttribute.local_attribute
    {attrname = "aesop_simp", name = "aesop_selftest_attribute",
     args = [], thm = attribute_rule}
val attribute_after =
  rewrite_rhs (aesopData.aesop_ss ()) attribute_lhs

val _ =
  test
    ("aesop_simp additions mark the derived simpset cache stale",
     fn () =>
       aconv attribute_before attribute_lhs andalso
       aconv attribute_after attribute_rhs)

val _ =
  test
    ("aesop simpset leaves conditional splitting to safe rules",
     fn () =>
       let
         val original =
           ``P (if aesop_split_b then aesop_split_x:'a
               else aesop_split_y) : bool``
         val goal = ([], original)
         val unsplit =
           residual
             (simpLib.SIMP_TAC (aesopData.aesop_ss ()) []) goal
         val split =
           residual
             (simpLib.SIMP_TAC
               (simpLib.++ (aesopData.aesop_ss (), simpLib.split_ss)) [])
             goal
       in
         case (unsplit, split) of
             ([([], unsplit_goal)], [([], split_goal)]) =>
               can (find_term boolSyntax.is_cond) unsplit_goal andalso
               not (can (find_term boolSyntax.is_cond) split_goal)
           | _ => false
       end)

fun rule_names rules =
  map (fn ({name, ...} : aesopRule.rule) => name) rules

fun is_phase expected ({phase, ...} : aesopRule.rule) =
  phase = expected

fun engine_step_succeeds rule goal =
  case #apply (rule : aesopRule.rule) of
      aesopRule.EngineStep step =>
        not (seq.null (step (clasetGoal.from_goal goal, 1)))
    | _ => false

val _ =
  test
    ("aesop closers are safe and ordered assumption before contradiction",
     fn () =>
       let
         val p = Term.mk_var ("aesop_closer_p", Type.bool)
         val q = Term.mk_var ("aesop_closer_q", Type.bool)
         val closers = aesopRule.closers ()
       in
         rule_names closers = ["assumption", "contradiction"] andalso
         List.all (is_phase aesopRule.RSafe) closers andalso
         engine_step_succeeds (hd closers) ([p], p) andalso
         engine_step_succeeds (hd (tl closers))
           ([boolSyntax.mk_neg p, p], q)
       end)

fun add_premise premise theorem =
  DISCH premise (Drule.ADD_ASSUM premise theorem)

val assembly_p =
  Term.mk_var ("aesop_assembly_p", Type.bool)
val assembly_q =
  Term.mk_var ("aesop_assembly_q", Type.bool)
val assembly_r =
  Term.mk_var ("aesop_assembly_r", Type.bool)
val assembly_s =
  Term.mk_var ("aesop_assembly_s", Type.bool)

val assembly_cs =
  clasetLib.empty_cs
  |> clasetLib.add_rule
       {kind = clasetRules.Intro, safe = true, prio = NONE}
       ("safe0", boolTheory.TRUTH)
  |> clasetLib.add_rule
       {kind = clasetRules.Intro, safe = true, prio = NONE}
       ("safep", add_premise assembly_p boolTheory.TRUTH)
  |> clasetLib.add_rule
       {kind = clasetRules.Intro, safe = false, prio = NONE}
       ("unsafe_default", add_premise assembly_q boolTheory.TRUTH)
  |> clasetLib.add_rule
       {kind = clasetRules.Intro, safe = false, prio = SOME 80}
       ("unsafe_eighty",
        add_premise assembly_r
          (add_premise assembly_s boolTheory.TRUTH))

val assembled =
  aesopRule.claset_rules
    {claset = assembly_cs, mode = clasetUnify.Unify,
     conclusion = boolSyntax.T, assumptions = [],
     qvars = HOLset.empty Term.compare, simp_args = []}

val _ =
  test
    ("aesop claset assembly defaults unsafe rules to fifty percent",
     fn () =>
       case #unsafe assembled of
           [{name = "unsafe_eighty", phase = aesopRule.RUnsafe 80, ...},
            {name = "unsafe_default", phase = aesopRule.RUnsafe 50, ...}] =>
             true
         | _ => false)

val _ =
  test
    ("aesop safe-order scaffold locks closers safe0 and safep slots",
     fn () =>
       let
         val safe = #safe assembled
       in
         rule_names (aesopRule.safe_rules safe) =
           ["assumption", "contradiction", "safe0", "safep"] andalso
         null (#safe_forward safe) andalso
         null (#conclusion_splits safe) andalso
         null (#assumption_splits safe)
       end)

fun first_engine_record rule goal =
  case #apply (rule : aesopRule.rule) of
      aesopRule.EngineStep step =>
        (case seq.cases (step (clasetGoal.from_goal goal, 1)) of
             SOME ((record, _), _) => SOME record
           | NONE => NONE)
    | _ => NONE

val elim_p = Term.mk_var ("aesop_elim_p", Type.bool)
val elim_q = Term.mk_var ("aesop_elim_q", Type.bool)
val elim_theorem =
  DISCH elim_p (DISCH elim_q (ASSUME elim_q))
val dest_theorem =
  DISCH elim_p (ASSUME elim_p)
val elim_dest_cs =
  clasetLib.empty_cs
  |> clasetLib.add_rule
       {kind = clasetRules.Elim, safe = true, prio = NONE}
       ("safe_elim", elim_theorem)
  |> clasetLib.add_rule
       {kind = clasetRules.Dest, safe = false, prio = SOME 70}
       ("unsafe_dest", dest_theorem)
val elim_dest_rules =
  aesopRule.claset_rules
    {claset = elim_dest_cs, mode = clasetUnify.Unify,
     conclusion = elim_q, assumptions = [elim_p],
     qvars = HOLset.empty Term.compare, simp_args = []}

val _ =
  test
    ("aesop assembly uses plain elim and make-elim dest without variants",
     fn () =>
       let
         val safe =
           List.filter
             (fn ({name, ...} : aesopRule.rule) => name = "safe_elim")
             (aesopRule.safe_rules (#safe elim_dest_rules))
         val unsafe = #unsafe elim_dest_rules
       in
         case (safe, unsafe) of
             ([elim_rule],
              [dest_rule as
                 {name = "unsafe_dest",
                  phase = aesopRule.RUnsafe 70, ...}]) =>
               (case
                  (first_engine_record elim_rule ([elim_p], elim_q),
                   first_engine_record dest_rule ([elim_p], elim_q))
                of
                    (SOME elim_record, SOME dest_record) =>
                      clasetStep.consumed_of elim_record = SOME 1 andalso
                      clasetStep.consumed_of dest_record = SOME 1 andalso
                      (case clasetStep.kind_of elim_record of
                           clasetStep.RuleApplication
                             {variant = clasetStep.Plain, ...} => true
                         | _ => false) andalso
                      (case clasetStep.kind_of dest_record of
                           clasetStep.RuleApplication
                             {variant = clasetStep.Plain, ...} => true
                         | _ => false)
                  | _ => false)
           | _ => false
       end)

val _ =
  test
    ("aesop apply builder makes one engine step with its supplied phase",
     fn () =>
       let
         val rule =
           aesopRule.apply_rule
             {name = "apply_truth", phase = aesopRule.RUnsafe 65,
              theorem = boolTheory.TRUTH, mode = clasetUnify.Unify}
       in
         #name rule = "apply_truth" andalso
         is_phase (aesopRule.RUnsafe 65) rule andalso
         not (#once rule) andalso
         engine_step_succeeds rule ([], boolSyntax.T)
       end)

val _ =
  test
    ("aesop constructors builder is multi-step and unsafe by default",
     fn () =>
       let
         val unsafe =
           aesopRule.constructors_rule
             {name = "constructors", theorems = [boolTheory.TRUTH],
              percent = NONE, mode = clasetUnify.Unify}
         val safe =
           aesopRule.safe_constructors_rule
             {name = "safe_constructors",
              theorems = [boolTheory.TRUTH],
              mode = clasetUnify.Match}
         fun singleton_multi rule =
           case #apply (rule : aesopRule.rule) of
               aesopRule.MultiStep [_] => true
             | _ => false
       in
         is_phase (aesopRule.RUnsafe 50) unsafe andalso
         is_phase aesopRule.RSafe safe andalso
         singleton_multi unsafe andalso singleton_multi safe
       end)

val _ =
  test
    ("aesop simp builder is the built-in penalty-zero rendered rule",
     fn () =>
       let
         val rule =
           aesopRule.simp_rule [clasetLib.Simp boolTheory.TRUTH]
       in
         #name rule = "simp" andalso
         is_phase (aesopRule.RNorm 0) rule andalso
         (case #apply rule of
              aesopRule.RenderedTactic tactic =>
                not (seq.null (tactic ([], boolSyntax.T)))
            | _ => false)
       end)

fun first_engine_result rule goal =
  case #apply (rule : aesopRule.rule) of
      aesopRule.EngineStep step =>
        (case seq.cases (step (clasetGoal.from_goal goal, 1)) of
             SOME (result, _) => SOME result
           | NONE => NONE)
    | _ => NONE

fun rendered_succeeds rule goal =
  case #apply (rule : aesopRule.rule) of
      aesopRule.RenderedTactic tactic =>
        not (seq.null (tactic goal))
    | _ => false

val forward_p = Term.mk_var ("aesop_forward_p", Type.bool)
val forward_q = Term.mk_var ("aesop_forward_q", Type.bool)
val forward_target =
  Term.mk_var ("aesop_forward_target", Type.bool)
val forward_conclusion =
  boolSyntax.mk_conj (forward_p, forward_q)
val forward_theorem =
  DISCH forward_p
    (DISCH forward_q
      (CONJ (ASSUME forward_p) (ASSUME forward_q)))
val reverse_forward_theorem =
  DISCH forward_p
    (DISCH forward_q
      (CONJ (ASSUME forward_q) (ASSUME forward_p)))

val _ =
  test
    ("aesop forward is all-immediate and retains matched assumptions",
     fn () =>
       let
         val rule =
           aesopRule.default_forward_rule
             {name = "forward", phase = aesopRule.RSafe,
              theorem = forward_theorem, mode = clasetUnify.Match}
       in
         case first_engine_result rule
           ([forward_p, forward_q], forward_target)
         of
             SOME (record, node) =>
               #once rule andalso
               clasetStep.consumed_of record = NONE andalso
               (case clasetGoal.render node 1 of
                    ([added, retained_p, retained_q], target) =>
                      aconv added forward_conclusion andalso
                      aconv retained_p forward_p andalso
                      aconv retained_q forward_q andalso
                      aconv target forward_target
                  | _ => false)
           | NONE => false
       end)

val _ =
  test
    ("aesop forward keeps a non-immediate suffix in the new hypothesis",
     fn () =>
       let
         val rule =
           aesopRule.forward_rule
             {name = "partial_forward", phase = aesopRule.RUnsafe 60,
              theorem = forward_theorem, immediate = 1,
              mode = clasetUnify.Unify}
         val expected =
           boolSyntax.mk_imp (forward_q, forward_conclusion)
       in
         case first_engine_result rule
           ([forward_p, forward_q], forward_target)
         of
             SOME (record, node) =>
               clasetStep.consumed_of record = NONE andalso
               (case clasetGoal.render node 1 of
                    (added :: retained, target) =>
                      aconv added expected andalso
                      ListPair.allEq (fn (left, right) =>
                        aconv left right)
                        (retained, [forward_p, forward_q]) andalso
                      aconv target forward_target
                  | _ => false)
           | NONE => false
       end)

val _ =
  test
    ("aesop forward records a replayable non-consuming transition",
     fn () =>
       let
         val original = ([forward_p, forward_q], forward_target)
         val rule =
           aesopRule.default_forward_rule
             {name = "forward_replay", phase = aesopRule.RSafe,
              theorem = forward_theorem, mode = clasetUnify.Match}
       in
         case first_engine_result rule original of
             SOME (_, node) =>
               let
                 val grounded =
                   clasetReplay.ground (clasetGoal.store node)
                     (clasetGoal.replay node)
               in
                 case clasetReplay.replay grounded original of
                     clasetReplay.Replayed
                       ([(added :: retained, target)], _) =>
                         aconv added forward_conclusion andalso
                         ListPair.allEq (fn (left, right) =>
                           aconv left right)
                           (retained, [forward_p, forward_q]) andalso
                         aconv target forward_target
                   | _ => false
               end
           | NONE => false
       end)

val _ =
  test
    ("aesop forward duplicate check instantiates before alpha comparison",
     fn () =>
       let
         val (meta, store0) =
           clasetMeta.new_meta
             {allow = [], ty = Type.bool} clasetMeta.empty
       in
         case clasetMeta.bind (meta, forward_p) store0 of
             SOME store =>
               aesopRule.forward_duplicate store [meta] forward_p
           | NONE => false
       end)

val forward_cs =
  clasetLib.empty_cs
  |> clasetLib.add_rule
       {kind = clasetRules.Forward, safe = true, prio = NONE}
       ("safe_forward", forward_theorem)
  |> clasetLib.add_rule
       {kind = clasetRules.Forward, safe = false, prio = SOME 77}
       ("unsafe_forward", reverse_forward_theorem)

val forward_assembled =
  aesopRule.claset_rules
    {claset = forward_cs, mode = clasetUnify.Match,
     conclusion = forward_target, assumptions = [forward_q],
     qvars = HOLset.empty Term.compare, simp_args = []}

val _ =
  test
    ("aesop claset assembly puts forward declarations in their phases",
     fn () =>
       let val safe = #safe forward_assembled
       in
         rule_names (#safe_forward safe) = ["safe_forward"] andalso
         (case #unsafe forward_assembled of
              [{name = "unsafe_forward",
                phase = aesopRule.RUnsafe 77, once = true, ...}] => true
            | _ => false)
       end)

val cases_theorem =
  DISCH boolSyntax.T
    (DISCH forward_q (ASSUME forward_q))

val _ =
  test
    ("aesop cases consumes its major assumption and honours patterns",
     fn () =>
       let
         val allowed =
           aesopRule.cases_rule
             {name = "cases", phase = aesopRule.RUnsafe 50,
              theorem = cases_theorem, patterns = [boolSyntax.T],
              mode = clasetUnify.Match}
         val blocked =
           aesopRule.cases_rule
             {name = "blocked_cases", phase = aesopRule.RUnsafe 50,
              theorem = cases_theorem, patterns = [boolSyntax.F],
              mode = clasetUnify.Match}
       in
         (case first_engine_record allowed ([boolSyntax.T], forward_q) of
              SOME record =>
                clasetStep.consumed_of record = SOME 1
            | NONE => false) andalso
         not (engine_step_succeeds blocked
           ([boolSyntax.T], forward_q))
       end)

val _ =
  test
    ("aesop TypeBase cases builder constructs a changing rendered rule",
     fn () =>
       let
         val variable =
           Term.mk_var ("aesop_cases_bool", Type.bool)
         val target = boolSyntax.mk_eq (variable, boolSyntax.T)
       in
         rendered_succeeds
           (aesopRule.cases_rule_for Type.bool) ([], target)
       end)

val _ =
  test
    ("aesop tactic builder rejects no-op results and applies indexes",
     fn () =>
       let
         val no_op =
           aesopRule.tactic_rule
             {name = "no_op", phase = aesopRule.RSafe,
              tactic = NTactical.NALL_TAC, index = NONE}
         val target_rule =
           aesopRule.tactic_rule
             {name = "target", phase = aesopRule.RSafe,
              tactic = NTactical.LIFT (Tactic.ACCEPT_TAC boolTheory.TRUTH),
              index =
                SOME (aesopRule.TargetPattern boolSyntax.T)}
         val hyp_rule =
           aesopRule.tactic_rule
             {name = "hyp", phase = aesopRule.RSafe,
              tactic = NTactical.LIFT Tactic.DISCH_TAC,
              index = SOME (aesopRule.HypPattern boolSyntax.T)}
       in
         not (rendered_succeeds no_op ([], boolSyntax.T)) andalso
         rendered_succeeds target_rule ([], boolSyntax.T) andalso
         not (rendered_succeeds target_rule ([], boolSyntax.F)) andalso
         rendered_succeeds hyp_rule
           ([boolSyntax.T],
            boolSyntax.mk_imp (forward_p, forward_p)) andalso
         not (rendered_succeeds hyp_rule
           ([], boolSyntax.mk_imp (forward_p, forward_p)))
       end)

val registered_before =
  length (aesopRule.registered_tactic_rules ())
val _ =
  aesopRule.register_tactic_rule
    {name = "registered_target", phase = aesopRule.RUnsafe 42,
     tactic = NTactical.LIFT (Tactic.ACCEPT_TAC boolTheory.TRUTH),
     index = SOME (aesopRule.TargetPattern boolSyntax.T)}
val registered_matching =
  aesopRule.claset_rules
    {claset = clasetLib.empty_cs, mode = clasetUnify.Match,
     conclusion = boolSyntax.T, assumptions = [],
     qvars = HOLset.empty Term.compare, simp_args = []}
val registered_blocked =
  aesopRule.claset_rules
    {claset = clasetLib.empty_cs, mode = clasetUnify.Match,
     conclusion = boolSyntax.F, assumptions = [],
     qvars = HOLset.empty Term.compare, simp_args = []}

val _ =
  test
    ("aesop tactic registry retains rules and applies its index",
     fn () =>
       length (aesopRule.registered_tactic_rules ()) =
         registered_before + 1 andalso
       List.exists
         (fn ({name, ...} : aesopRule.rule) =>
           name = "registered_target")
         (#unsafe registered_matching) andalso
       not
         (List.exists
           (fn ({name, ...} : aesopRule.rule) =>
             name = "registered_target")
           (#unsafe registered_blocked)))

val split_theorem = TypeBase.case_pred_disj_of Type.bool
val split_pair =
  aesopRule.split_rule_pair
    {name = "bool_case_split", theorem = split_theorem}
val assumption_split_pair =
  aesopRule.split_rule_pair
    {name = "bool_assumption_split",
     theorem = splitLib.mk_asm_split split_theorem}
val split_goal : Term.term list * Term.term =
  ([],
   ``aesop_split_pred
       (if aesop_split_test then aesop_split_left:'a
        else aesop_split_right) : bool``)
val split_assumption_goal =
  (#2 split_goal :: [], forward_target)

val _ =
  test
    ("aesop split builders change conclusions and assumptions",
     fn () =>
       rendered_succeeds (#conclusion split_pair) split_goal andalso
       rendered_succeeds (#assumption split_pair)
         split_assumption_goal andalso
       rendered_succeeds (#conclusion assumption_split_pair)
         split_goal andalso
       rendered_succeeds (#assumption assumption_split_pair)
         split_assumption_goal)

val _ =
  test
    ("aesop split builders occupy conclusion before assumption slots",
     fn () =>
       let
         val safe =
           {closers = [], safe0_claset = [], safe_forward = [],
            safep_claset = [],
            conclusion_splits = [#conclusion split_pair],
            assumption_splits = [#assumption split_pair]}
       in
         rule_names (aesopRule.safe_rules safe) =
           ["bool_case_split (conclusion split)",
            "bool_case_split (assumption split)"] andalso
         List.all (is_phase aesopRule.RSafe)
           (aesopRule.safe_rules safe)
       end)

fun tree_cgoal params assumptions target : clasetGoal.cgoal =
  {params = params, asl = assumptions, w = target}

fun tree_node store level goals =
  clasetGoal.create {goals = goals, store = store, level = level}

fun new_tree store cgoal unsafe =
  aesopTree.create
    {node = tree_node store 0 [cgoal], unsafe_cursor = unsafe}

fun pop_expected tree =
  case aesopTree.pop_goal tree of
      (SOME id, rest) => (id, rest)
    | _ => raise Fail "expected a queued aesop tree goal"

fun install_tree_rapp tree parent phase name store children records =
  aesopTree.install_rapp parent
    {rule = name, phase = phase, records = records,
     forwarded = NONE,
     node =
       tree_node store
         (#level (aesopTree.goal tree parent) + 1) children}
    tree

fun close_tree_goal tree id =
  #tree
    (install_tree_rapp tree id aesopRule.RSafe "close"
      (aesopTree.active_store (aesopTree.goal tree id)) [] [])

fun norm_complete outcome =
  case outcome of
      aesopNorm.Complete result => SOME result
    | aesopNorm.IterationLimit _ => NONE

fun norm_target tree id =
  #w (aesopTree.active_cgoal (aesopTree.goal tree id))

fun norm_records tree id =
  case #norm (aesopTree.goal tree id) of
      aesopTree.Normalised {records, ...} => records
    | aesopTree.NormProved {records, ...} => records
    | aesopTree.Unnormalised => []

fun record_is_disch record =
  case clasetStep.kind_of record of clasetStep.Disch => true | _ => false

fun record_is_gen record =
  case clasetStep.kind_of record of clasetStep.Gen => true | _ => false

fun record_is_hyp_subst record =
  case clasetStep.kind_of record of
      clasetStep.HypSubst => true
    | _ => false

fun record_is_wrapper record =
  case clasetStep.kind_of record of
      clasetStep.Wrapper => true
    | _ => false

fun norm_transition name penalty equality =
  let
    val (_, target) = boolSyntax.dest_eq (concl equality)
    val theorem =
      DISCH target (EQ_MP (SYM equality) (ASSUME target))
  in
    aesopRule.apply_rule
      {name = name, phase = aesopRule.RNorm penalty,
       theorem = theorem, mode = clasetUnify.Match}
  end

val norm_state1 =
  Term.mk_var ("aesop_norm_state1", Type.bool)
val norm_state2 =
  Term.mk_var ("aesop_norm_state2", Type.bool)
val norm_state3 =
  Term.mk_var ("aesop_norm_state3", Type.bool)
val norm_state4 =
  Term.mk_var ("aesop_norm_state4", Type.bool)
val norm_state_alt =
  Term.mk_var ("aesop_norm_state_alt", Type.bool)

val norm_4_to_3 =
  ASSUME (boolSyntax.mk_eq (norm_state4, norm_state3))
val norm_3_to_2 =
  ASSUME (boolSyntax.mk_eq (norm_state3, norm_state2))
val norm_3_to_alt =
  ASSUME (boolSyntax.mk_eq (norm_state3, norm_state_alt))
val norm_2_to_3 =
  SYM norm_3_to_2

val norm_restart_rules =
  [norm_transition "competing" 10 norm_3_to_alt,
   norm_transition "unlock" 5 norm_4_to_3,
   norm_transition "low" ~10 norm_3_to_2]
val norm_restart_tree0 =
  new_tree clasetMeta.empty
    (tree_cgoal []
      (map concl [norm_4_to_3, norm_3_to_2, norm_3_to_alt])
      norm_state4) []
val norm_restart_root =
  aesopTree.root norm_restart_tree0
val norm_restart_outcome =
  aesopNorm.normalise
    {max_depth = 10, rules = norm_restart_rules}
    norm_restart_root norm_restart_tree0

val _ =
  test
    ("aesop norm orders penalties and restarts after every success",
     fn () =>
       case norm_complete norm_restart_outcome of
           SOME {tree, iterations} =>
             iterations = 2 andalso
             aconv (norm_target tree norm_restart_root) norm_state2
         | NONE => false)

val custom_norm_simp =
  aesopRule.simp_rule_with
    {name = "simp",
     simpset =
       simpLib.++ (simpLib.empty_ss, simpLib.rewrites [norm_3_to_2]),
     controls = []}
val negative_norm =
  norm_transition "negative" ~1 norm_4_to_3
val norm_simp_tree0 =
  new_tree clasetMeta.empty
    (tree_cgoal []
      (map concl [norm_4_to_3, norm_3_to_2])
      norm_state4) []
val norm_simp_root =
  aesopTree.root norm_simp_tree0
val norm_simp_outcome =
  aesopNorm.normalise
    {max_depth = 10,
     rules = [custom_norm_simp, negative_norm]}
    norm_simp_root norm_simp_tree0

val _ =
  test
    ("aesop norm runs a negative user rule before penalty-zero simp",
     fn () =>
       case norm_complete norm_simp_outcome of
           SOME {tree, iterations} =>
             iterations = 2 andalso
             aconv (norm_target tree norm_simp_root) norm_state2 andalso
             (case norm_records tree norm_simp_root of
                  [first, second] =>
                    (case clasetStep.kind_of first of
                         clasetStep.RuleApplication _ => true
                       | _ => false) andalso
                    record_is_wrapper second
                | _ => false)
         | NONE => false)

val _ =
  test
    ("aesop norm built-ins have their documented penalty-zero order",
     fn () =>
       rule_names (aesopRule.norm_builtins []) =
         ["disch", "gen", "hyp-subst", "simp"] andalso
       List.all (is_phase (aesopRule.RNorm 0))
         (aesopRule.norm_builtins []))

val norm_declaration_cs =
  clasetLib.empty_cs
  |> clasetLib.add_rule
       {kind = clasetRules.Norm, safe = false, prio = SOME ~7}
       ("declared_norm",
        DISCH norm_state3
          (EQ_MP (SYM norm_4_to_3) (ASSUME norm_state3)))
val norm_declaration_rules =
  aesopRule.claset_rules
    {claset = norm_declaration_cs, mode = clasetUnify.Unify,
     conclusion = norm_state4, assumptions = [concl norm_4_to_3],
     qvars = HOLset.empty Term.compare, simp_args = []}

val _ =
  test
    ("aesop norm declarations are Match-mode apply rules with penalties",
     fn () =>
       case
         List.filter
           (fn ({name, ...} : aesopRule.rule) =>
             name = "declared_norm")
           (#norm norm_declaration_rules)
       of
           [rule as {phase = aesopRule.RNorm ~7, ...}] =>
             (case first_engine_result rule
                ([concl norm_4_to_3], norm_state4)
              of
                  SOME (_, node) =>
                    (case clasetGoal.goals node of
                         [{w, ...}] => aconv w norm_state3
                       | _ => false)
                | NONE => false)
         | _ => false)

val norm_builtin_p =
  Term.mk_var ("aesop_norm_builtin_p", Type.bool)
val norm_builtin_x =
  Term.mk_var ("aesop_norm_builtin_x", Type.bool)
val norm_builtin_goal =
  boolSyntax.mk_imp
    (norm_builtin_p,
     boolSyntax.mk_forall (norm_builtin_x, norm_builtin_p))
val norm_builtin_tree0 =
  new_tree clasetMeta.empty
    (tree_cgoal [] [] norm_builtin_goal) []
val norm_builtin_root =
  aesopTree.root norm_builtin_tree0
val norm_builtin_outcome =
  aesopNorm.normalise
    {max_depth = 10, rules = aesopRule.norm_builtins []}
    norm_builtin_root norm_builtin_tree0

val _ =
  test
    ("aesop norm introduces assumptions and universals before simp",
     fn () =>
       case norm_complete norm_builtin_outcome of
           SOME {tree, iterations} =>
             iterations = 3 andalso
             #state (aesopTree.goal tree norm_builtin_root) =
               aesopTree.Proved andalso
             (case norm_records tree norm_builtin_root of
                  [disch, gen, simp] =>
                    record_is_disch disch andalso
                    record_is_gen gen andalso
                    record_is_wrapper simp
                | _ => false)
         | NONE => false)

val norm_subst_variable =
  Term.mk_var ("aesop_norm_subst_variable", Type.bool)
val norm_subst_equality =
  boolSyntax.mk_eq (norm_subst_variable, boolSyntax.T)
val norm_subst_tree0 =
  new_tree clasetMeta.empty
    (tree_cgoal [] [norm_subst_equality] norm_subst_variable) []
val norm_subst_root =
  aesopTree.root norm_subst_tree0
val norm_subst_outcome =
  aesopNorm.normalise
    {max_depth = 10, rules = aesopRule.norm_builtins []}
    norm_subst_root norm_subst_tree0

val _ =
  test
    ("aesop norm hypothesis substitution eliminates variables",
     fn () =>
       case norm_complete norm_subst_outcome of
           SOME {tree, ...} =>
             #state (aesopTree.goal tree norm_subst_root) =
               aesopTree.Proved andalso
             (case norm_records tree norm_subst_root of
                  first :: _ =>
                    record_is_hyp_subst first
                | [] => false)
         | NONE => false)

val norm_function =
  Term.mk_var
    ("aesop_norm_function", Type.bool --> Type.bool)
val norm_argument =
  Term.mk_var ("aesop_norm_argument", Type.bool)
val norm_application =
  Term.mk_comb (norm_function, norm_argument)
val norm_rewrite_assumption =
  boolSyntax.mk_eq (norm_application, boolSyntax.T)

fun run_simp_controls controls =
  let
    val tree0 =
      new_tree clasetMeta.empty
        (tree_cgoal [] [norm_rewrite_assumption]
          norm_application) []
    val root = aesopTree.root tree0
  in
    (root,
     aesopNorm.normalise
       {max_depth = 10,
        rules = [aesopRule.simp_rule controls]} root tree0)
  end

val (norm_asms_root, norm_asms_outcome) =
  run_simp_controls []
val (norm_no_asms_root, norm_no_asms_outcome) =
  run_simp_controls [markerLib.NoAsms]

val _ =
  test
    ("aesop norm simp uses assumptions unless NoAsms disables them",
     fn () =>
       case
         (norm_complete norm_asms_outcome,
          norm_complete norm_no_asms_outcome)
       of
           (SOME {tree = with_asms, ...},
            SOME {tree = without_asms, iterations = 0}) =>
             #state (aesopTree.goal with_asms norm_asms_root) =
               aesopTree.Proved andalso
             aconv
               (norm_target without_asms norm_no_asms_root)
               norm_application
         | _ => false)

val branching_norm_theorem =
  add_premise norm_state2
    (add_premise norm_state1 (ASSUME norm_state4))
val branching_norm_rule =
  aesopRule.apply_rule
    {name = "branching", phase = aesopRule.RNorm 0,
     theorem = branching_norm_theorem, mode = clasetUnify.Match}
val branching_norm_tree0 =
  new_tree clasetMeta.empty
    (tree_cgoal [] [norm_state4] norm_state4) []
val branching_norm_root =
  aesopTree.root branching_norm_tree0
val branching_norm_outcome =
  aesopNorm.normalise
    {max_depth = 10, rules = [branching_norm_rule]}
    branching_norm_root branching_norm_tree0

val _ =
  test
    ("aesop norm dynamically rejects applications with two subgoals",
     fn () =>
       case norm_complete branching_norm_outcome of
           SOME {tree, iterations = 0} =>
             aconv (norm_target tree branching_norm_root) norm_state4 andalso
             null (norm_records tree branching_norm_root)
         | _ => false)

fun duplicated_disch input =
  case seq.cases (clasetStep.blast_disch_step input) of
      NONE => seq.empty
    | SOME (result, _) => seq.fromList [result, result]

val alternative_norm_rule : aesopRule.rule =
  {name = "alternatives", phase = aesopRule.RNorm 0,
   apply = aesopRule.EngineStep duplicated_disch, once = false}
val alternative_norm_tree0 =
  new_tree clasetMeta.empty
    (tree_cgoal [] []
      (boolSyntax.mk_imp (norm_builtin_p, norm_builtin_p))) []
val alternative_norm_root =
  aesopTree.root alternative_norm_tree0
val alternative_norm_outcome =
  aesopNorm.normalise
    {max_depth = 10, rules = [alternative_norm_rule]}
    alternative_norm_root alternative_norm_tree0

val _ =
  test
    ("aesop norm dynamically rejects multiple application alternatives",
     fn () =>
       case norm_complete alternative_norm_outcome of
           SOME {tree, iterations = 0} =>
             aconv
               (norm_target tree alternative_norm_root)
               (boolSyntax.mk_imp
                 (norm_builtin_p, norm_builtin_p))
         | _ => false)

val (norm_meta, norm_meta_store) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val binding_norm_rule =
  aesopRule.apply_rule
    {name = "bind-meta", phase = aesopRule.RNorm 0,
     theorem = boolTheory.TRUTH, mode = clasetUnify.Unify}
val binding_norm_tree0 =
  new_tree norm_meta_store
    (tree_cgoal [] [] norm_meta) []
val binding_norm_root =
  aesopTree.root binding_norm_tree0
val binding_norm_outcome =
  aesopNorm.normalise
    {max_depth = 10, rules = [binding_norm_rule]}
    binding_norm_root binding_norm_tree0

val _ =
  test
    ("aesop norm dynamically rejects metavariable-binding applications",
     fn () =>
       case norm_complete binding_norm_outcome of
           SOME {tree, iterations = 0} =>
             aconv (norm_target tree binding_norm_root) norm_meta andalso
             null
               (#terms
                 (clasetMeta.bindings
                   (aesopTree.active_store
                     (aesopTree.goal tree binding_norm_root))))
         | _ => false)

val looping_norm_rules =
  [norm_transition "forth" 0 norm_2_to_3,
   norm_transition "back" 0 norm_3_to_2]
val looping_norm_tree0 =
  new_tree clasetMeta.empty
    (tree_cgoal []
      (map concl [norm_2_to_3, norm_3_to_2])
      norm_state2) []
val looping_norm_root =
  aesopTree.root looping_norm_tree0
val looping_norm_outcome =
  aesopNorm.normalise
    {max_depth = 3, rules = looping_norm_rules}
    looping_norm_root looping_norm_tree0

val _ =
  test
    ("aesop norm iteration bound is clean and installs no partial chain",
     fn () =>
       case looping_norm_outcome of
           aesopNorm.IterationLimit
             {tree, iterations = 3, rule = "back"} =>
               not
                 (aesopTree.is_normalised
                   (aesopTree.goal tree looping_norm_root)) andalso
               aconv
                 (#w (#cgoal
                   (aesopTree.goal tree looping_norm_root)))
                 norm_state2
         | _ => false)

fun near expected actual =
  Real.abs (expected - actual) < 0.000000001

val _ =
  test
    ("aesop tree priorities multiply in the log domain",
     fn () =>
       let
         val first =
           aesopTree.extend_priority 0.0 (aesopRule.RUnsafe 50)
         val second =
           aesopTree.extend_priority first (aesopRule.RUnsafe 20)
       in
         near (Math.ln 0.1) second andalso
         near second
           (aesopTree.extend_priority second aesopRule.RSafe)
       end)

val fifo_goal =
  tree_cgoal [] [] boolSyntax.T
val fifo_tree0 =
  new_tree clasetMeta.empty fifo_goal []
val (fifo_root, fifo_tree1) =
  pop_expected fifo_tree0
val fifo_install =
  install_tree_rapp fifo_tree1 fifo_root
    (aesopRule.RUnsafe 50) "fifo" clasetMeta.empty
    [fifo_goal, fifo_goal] []
val (fifo_first, fifo_tree2) =
  pop_expected (#tree fifo_install)
val (fifo_second, _) =
  pop_expected fifo_tree2

val _ =
  test
    ("aesop tree queue uses FIFO order for equal priorities",
     fn () =>
       #goals fifo_install = [fifo_first, fifo_second] andalso
       near
         (#prio (aesopTree.goal (#tree fifo_install) fifo_first))
         (Math.ln 0.5))

val priority_tree0 =
  new_tree clasetMeta.empty fifo_goal []
val (priority_root, priority_tree1) =
  pop_expected priority_tree0
val priority_low =
  install_tree_rapp priority_tree1 priority_root
    (aesopRule.RUnsafe 20) "low_priority" clasetMeta.empty
    [fifo_goal] []
val priority_high =
  install_tree_rapp (#tree priority_low) priority_root
    (aesopRule.RUnsafe 80) "high_priority" clasetMeta.empty
    [fifo_goal] []
val (priority_first, _) =
  pop_expected (#tree priority_high)

val _ =
  test
    ("aesop tree queue pops higher log priorities first",
     fn () => #goals priority_high = [priority_first])

val proved_tree0 =
  new_tree clasetMeta.empty fifo_goal []
val (proved_root, proved_tree1) =
  pop_expected proved_tree0
val proved_install =
  install_tree_rapp proved_tree1 proved_root aesopRule.RSafe
    "two_children" clasetMeta.empty [fifo_goal, fifo_goal] []
val [proved_left, proved_right] = #goals proved_install
val proved_tree2 =
  close_tree_goal (#tree proved_install) proved_left
val proved_rapp =
  #rapp proved_install

val _ =
  test
    ("aesop tree proved states wait for every independent cluster",
     fn () =>
       #state (aesopTree.goal proved_tree2 proved_left) =
         aesopTree.Proved andalso
       #state (aesopTree.rapp proved_tree2 proved_rapp) =
         aesopTree.Unknown andalso
       #state (aesopTree.goal proved_tree2 proved_root) =
         aesopTree.Unknown)

val proved_tree3 =
  close_tree_goal proved_tree2 proved_right

val _ =
  test
    ("aesop tree proved states cascade from clusters to the root",
     fn () =>
       #state (aesopTree.rapp proved_tree3 proved_rapp) =
         aesopTree.Proved andalso
       #state (aesopTree.goal proved_tree3 proved_root) =
         aesopTree.Proved)

val stuck_tree0 =
  new_tree clasetMeta.empty fifo_goal []
val (stuck_root, stuck_tree1) =
  pop_expected stuck_tree0
val stuck_install =
  install_tree_rapp stuck_tree1 stuck_root aesopRule.RSafe
    "stuck_children" clasetMeta.empty [fifo_goal, fifo_goal] []
val [stuck_left, stuck_right] = #goals stuck_install
val stuck_tree2 =
  aesopTree.exhaust_goal stuck_left (#tree stuck_install)
val stuck_rapp =
  #rapp stuck_install

val _ =
  test
    ("aesop tree rapps stick when any child cluster sticks",
     fn () =>
       #state (aesopTree.goal stuck_tree2 stuck_left) =
         aesopTree.Stuck andalso
       #state (aesopTree.rapp stuck_tree2 stuck_rapp) =
         aesopTree.Stuck andalso
       #state (aesopTree.goal stuck_tree2 stuck_root) =
         aesopTree.Unknown)

val stuck_tree3 =
  aesopTree.exhaust_goal stuck_root stuck_tree2

val _ =
  test
    ("aesop tree stuck states cascade and make descendants irrelevant",
     fn () =>
       #state (aesopTree.goal stuck_tree3 stuck_root) =
         aesopTree.Stuck andalso
       #state (aesopTree.goal stuck_tree3 stuck_right) =
         aesopTree.Unknown andalso
       aesopTree.goal_irrelevant stuck_tree3 stuck_right)

val unfinished_rule =
  hd (aesopRule.closers ())
val completion_tree0 =
  new_tree clasetMeta.empty fifo_goal [unfinished_rule]
val completion_root =
  aesopTree.root completion_tree0
val completion_tree1 =
  completion_tree0
  |> aesopTree.set_normalised completion_root
       {records = [], cgoal = fifo_goal, store = clasetMeta.empty}
  |> aesopTree.set_safe_done completion_root true

val _ =
  test
    ("aesop goals stick only after every search phase is exhausted",
     fn () =>
       #state (aesopTree.goal completion_tree1 completion_root) =
         aesopTree.Unknown andalso
       #state
         (aesopTree.goal
           (aesopTree.set_unsafe_cursor completion_root []
             completion_tree1)
           completion_root) =
         aesopTree.Stuck)

val (cluster_m1, cluster_store1) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val (cluster_m2, cluster_store2) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} cluster_store1
val (cluster_m3, cluster_store3) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} cluster_store2
val cluster_g1 =
  tree_cgoal [] [] cluster_m1
val cluster_g2 =
  tree_cgoal [] []
    (boolSyntax.mk_conj (cluster_m1, cluster_m2))
val cluster_g3 =
  tree_cgoal [] [] cluster_m2
val cluster_g4 =
  tree_cgoal [] [] cluster_m3
val cluster_tree0 =
  new_tree cluster_store3 fifo_goal []
val (cluster_root, cluster_tree1) =
  pop_expected cluster_tree0
val cluster_install =
  install_tree_rapp cluster_tree1 cluster_root aesopRule.RSafe
    "clusters" cluster_store3
    [cluster_g1, cluster_g2, cluster_g3, cluster_g4] []
val [cluster_id1, cluster_id2] =
  #clusters (aesopTree.rapp (#tree cluster_install)
    (#rapp cluster_install))

val _ =
  test
    ("aesop tree clusters close transitive metavariable overlap",
     fn () =>
       #goals (aesopTree.cluster (#tree cluster_install) cluster_id1) =
         List.take (#goals cluster_install, 3) andalso
       #goals (aesopTree.cluster (#tree cluster_install) cluster_id2) =
         [List.nth (#goals cluster_install, 3)])

val coupled_tree0 =
  new_tree cluster_store1 fifo_goal []
val (coupled_root, coupled_tree1) =
  pop_expected coupled_tree0
val coupled_goal =
  tree_cgoal [] [] cluster_m1
val coupled_install =
  install_tree_rapp coupled_tree1 coupled_root aesopRule.RSafe
    "coupled" cluster_store1 [coupled_goal, coupled_goal] []
val [coupled_left, coupled_right] =
  #goals coupled_install
val coupled_tree2 =
  close_tree_goal (#tree coupled_install) coupled_left
val coupled_closer =
  hd (aesopTree.child_rapps coupled_tree2 coupled_left)
val coupled_cluster =
  #cluster (aesopTree.goal coupled_tree2 coupled_right)
val coupled_pop =
  aesopTree.pop_goal coupled_tree2

val _ =
  test
    ("aesop proof lazily removes every kind of irrelevant queued node",
     fn () =>
       #state (aesopTree.goal coupled_tree2 coupled_root) =
         aesopTree.Proved andalso
       #state (aesopTree.goal coupled_tree2 coupled_right) =
         aesopTree.Unknown andalso
       aesopTree.goal_irrelevant coupled_tree2 coupled_right andalso
       aesopTree.rapp_irrelevant coupled_tree2 coupled_closer andalso
       aesopTree.cluster_irrelevant coupled_tree2 coupled_cluster andalso
       #1 coupled_pop = NONE)

val coupled_stuck_tree0 =
  new_tree cluster_store1 fifo_goal []
val (coupled_stuck_root, coupled_stuck_tree1) =
  pop_expected coupled_stuck_tree0
val coupled_stuck_install =
  install_tree_rapp coupled_stuck_tree1 coupled_stuck_root
    aesopRule.RSafe "coupled_stuck" cluster_store1
    [coupled_goal, coupled_goal] []
val [coupled_stuck_left, coupled_stuck_right] =
  #goals coupled_stuck_install
val coupled_stuck_rapp =
  #rapp coupled_stuck_install
val coupled_stuck_tree2 =
  aesopTree.exhaust_goal coupled_stuck_left
    (#tree coupled_stuck_install)
val coupled_stuck_tree3 =
  aesopTree.exhaust_goal coupled_stuck_right coupled_stuck_tree2

val _ =
  test
    ("aesop clusters stick only after every coupled goal sticks",
     fn () =>
       #state
         (aesopTree.rapp coupled_stuck_tree2 coupled_stuck_rapp) =
         aesopTree.Unknown andalso
       #state
         (aesopTree.rapp coupled_stuck_tree3 coupled_stuck_rapp) =
         aesopTree.Stuck)

val (dependency_m1, dependency_store1) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val (dependency_m2, dependency_store2) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} dependency_store1
val dependency_store3 =
  valOf (clasetMeta.bind
    (dependency_m1, dependency_m2) dependency_store2)
val (dependency_ty1, dependency_store4) =
  clasetMeta.new_tymeta dependency_store3
val (dependency_ty2, dependency_store5) =
  clasetMeta.new_tymeta dependency_store4
val dependency_store6 =
  valOf (clasetMeta.bind_ty
    (dependency_ty1, dependency_ty2) dependency_store5)
val dependency_param =
  Term.mk_var ("aesop_dependency_param", dependency_ty1)
val dependency_goal =
  tree_cgoal [dependency_param] [] dependency_m1
val dependency_deps =
  aesopTree.dependencies_of dependency_store6 dependency_goal

val _ =
  test
    ("aesop goal dependencies follow term and type binding residues",
     fn () =>
       HOLset.equal
         (#terms dependency_deps,
          HOLset.singleton Term.compare dependency_m2) andalso
       HOLset.equal
         (#types dependency_deps,
          HOLset.singleton Type.compare dependency_ty2))

val (assigned_meta, bookkeeping_store1) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val (assigned_type, bookkeeping_store2) =
  clasetMeta.new_tymeta bookkeeping_store1
val (created_meta, bookkeeping_store3) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} bookkeeping_store2
val (created_type, bookkeeping_store4) =
  clasetMeta.new_tymeta bookkeeping_store3
val bookkeeping_store5 =
  valOf
    (clasetMeta.bind (assigned_meta, boolSyntax.T)
      bookkeeping_store4)
val bookkeeping_store6 =
  valOf
    (clasetMeta.bind_ty (assigned_type, Type.bool)
      bookkeeping_store5)
val bookkeeping_result =
  Tactical.ALL_TAC ([], boolSyntax.T)
val bookkeeping_record =
  clasetReplay.make_record
    {kind = clasetReplay.Wrapper, target = 1, consumed = NONE,
     created = {terms = [created_meta], types = [created_type]},
     eigenvariables = [], validation = #2 bookkeeping_result,
     action = clasetReplay.fixed_action bookkeeping_result,
     children = []}
val bookkeeping_root_goal =
  tree_cgoal
    [Term.mk_var ("aesop_assigned_type", assigned_type)]
    [] assigned_meta
val bookkeeping_tree0 =
  new_tree bookkeeping_store2 bookkeeping_root_goal []
val (bookkeeping_root, bookkeeping_tree1) =
  pop_expected bookkeeping_tree0
val bookkeeping_install =
  install_tree_rapp bookkeeping_tree1 bookkeeping_root aesopRule.RSafe
    "bookkeeping" bookkeeping_store6 [] [bookkeeping_record]
val bookkeeping_rapp =
  aesopTree.rapp (#tree bookkeeping_install)
    (#rapp bookkeeping_install)

val _ =
  test
    ("aesop rapps cache created records and parent-to-child assignments",
     fn () =>
       HOLset.equal
         (#terms (#created bookkeeping_rapp),
          HOLset.singleton Term.compare created_meta) andalso
       HOLset.equal
         (#types (#created bookkeeping_rapp),
          HOLset.singleton Type.compare created_type) andalso
       HOLset.equal
         (#terms (#assigned bookkeeping_rapp),
          HOLset.singleton Term.compare assigned_meta) andalso
       HOLset.equal
         (#types (#assigned bookkeeping_rapp),
          HOLset.singleton Type.compare assigned_type))

fun tree_creation_record terms types =
  let
    val result = Tactical.ALL_TAC ([], boolSyntax.T)
  in
    clasetReplay.make_record
      {kind = clasetReplay.Wrapper, target = 1, consumed = NONE,
       created = {terms = terms, types = types},
       eigenvariables = [], validation = #2 result,
       action = clasetReplay.fixed_action result, children = []}
  end

fun bind_tree_meta meta value store =
  case clasetMeta.bind (meta, value) store of
      SOME result => result
    | NONE => raise Fail "expected aesop tree metavariable binding"

fun original_goal tree id =
  case #copy_of (aesopTree.goal tree id) of
      NONE => id
    | SOME original => original

val (copy_meta, copy_store1) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val copy_creator_record =
  tree_creation_record [copy_meta] []
val copy_tree0 =
  new_tree clasetMeta.empty fifo_goal []
val (copy_root, copy_tree1) =
  pop_expected copy_tree0
val copy_created =
  install_tree_rapp copy_tree1 copy_root aesopRule.RSafe
    "copy_creator" copy_store1
    [tree_cgoal [] [] copy_meta, tree_cgoal [] [] copy_meta]
    [copy_creator_record]
val [copy_path, copy_sibling] =
  #goals copy_created
val copy_explored =
  install_tree_rapp (#tree copy_created) copy_sibling aesopRule.RSafe
    "copy_existing_subtree" copy_store1
    [tree_cgoal [] [] copy_meta] []
val copy_store2 =
  bind_tree_meta copy_meta boolSyntax.T copy_store1
val copy_assigned =
  install_tree_rapp (#tree copy_explored) copy_path aesopRule.RSafe
    "copy_assign" copy_store2 [] []
val [copied_sibling] =
  #goals copy_assigned
val copied_sibling_node =
  aesopTree.goal (#tree copy_assigned) copied_sibling

val _ =
  test
    ("aesop copying instantiates coupled siblings without their subtrees",
     fn () =>
       #copy_of copied_sibling_node = SOME copy_sibling andalso
       aconv (#w (#cgoal copied_sibling_node)) boolSyntax.T andalso
       not
         (null
           (aesopTree.child_rapps
             (#tree copy_assigned) copy_sibling)) andalso
       null
         (aesopTree.child_rapps
           (#tree copy_assigned) copied_sibling))

val (transitive_x, transitive_store1) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val (transitive_y, transitive_store2) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} transitive_store1
val (transitive_z, transitive_store3) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} transitive_store2
val transitive_g1 =
  tree_cgoal [] [] transitive_x
val transitive_g2 =
  tree_cgoal [] []
    (boolSyntax.mk_conj (transitive_x, transitive_y))
val transitive_g3 =
  tree_cgoal [] [] transitive_y
val transitive_g4 =
  tree_cgoal [] [] transitive_z
val transitive_tree0 =
  new_tree clasetMeta.empty fifo_goal []
val (transitive_root, transitive_tree1) =
  pop_expected transitive_tree0
val transitive_created =
  install_tree_rapp transitive_tree1 transitive_root aesopRule.RSafe
    "transitive_creator" transitive_store3
    [transitive_g1, transitive_g2, transitive_g3, transitive_g4]
    [tree_creation_record
       [transitive_x, transitive_y, transitive_z] []]
val [transitive_id1, transitive_id2, transitive_id3,
     transitive_id4] =
  #goals transitive_created
val transitive_store4 =
  bind_tree_meta transitive_y boolSyntax.T transitive_store3
val transitive_first =
  install_tree_rapp (#tree transitive_created) transitive_id3
    aesopRule.RSafe "transitive_assign_y" transitive_store4 [] []
val [transitive_copy2] =
  #goals transitive_first
val transitive_store5 =
  bind_tree_meta transitive_x boolSyntax.F transitive_store4
val transitive_second =
  install_tree_rapp (#tree transitive_first) transitive_copy2
    aesopRule.RSafe "transitive_assign_x" transitive_store5 [] []
val [transitive_copy1] =
  #goals transitive_second

val _ =
  test
    ("aesop copying follows transitive G1-G2-G3 coupling",
     fn () =>
       #copy_of
         (aesopTree.goal
           (#tree transitive_first) transitive_copy2) =
         SOME transitive_id2 andalso
       #copy_of
         (aesopTree.goal
           (#tree transitive_second) transitive_copy1) =
         SOME transitive_id1 andalso
       aconv
         (#w
           (#cgoal
             (aesopTree.goal
               (#tree transitive_second) transitive_copy1)))
         boolSyntax.F andalso
       original_goal (#tree transitive_second) transitive_copy2 =
         transitive_id2 andalso
       transitive_id4 <> transitive_copy1)

val (duplicate_x, duplicate_store1) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val (duplicate_y, duplicate_store2) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} duplicate_store1
val duplicate_path_goal =
  tree_cgoal [] []
    (boolSyntax.mk_conj (duplicate_x, duplicate_y))
val duplicate_sibling_goal =
  tree_cgoal [] []
    (boolSyntax.mk_disj (duplicate_x, duplicate_y))
val duplicate_tree0 =
  new_tree clasetMeta.empty fifo_goal []
val (duplicate_root, duplicate_tree1) =
  pop_expected duplicate_tree0
val duplicate_created =
  install_tree_rapp duplicate_tree1 duplicate_root aesopRule.RSafe
    "duplicate_creator" duplicate_store2
    [duplicate_path_goal, duplicate_sibling_goal]
    [tree_creation_record [duplicate_x, duplicate_y] []]
val [duplicate_path, duplicate_original] =
  #goals duplicate_created
val duplicate_store3 =
  bind_tree_meta duplicate_x boolSyntax.T duplicate_store2
val duplicate_first =
  install_tree_rapp (#tree duplicate_created) duplicate_path
    aesopRule.RSafe "duplicate_assign_x" duplicate_store3
    [tree_cgoal [] [] duplicate_y] []
val [duplicate_next, duplicate_first_copy] =
  #goals duplicate_first
val duplicate_store4 =
  bind_tree_meta duplicate_y boolSyntax.F duplicate_store3
val duplicate_second =
  install_tree_rapp (#tree duplicate_first) duplicate_next
    aesopRule.RSafe "duplicate_assign_y" duplicate_store4 [] []
val [duplicate_only_copy] =
  #goals duplicate_second

val _ =
  test
    ("aesop copying suppresses duplicate copies of one original",
     fn () =>
       #copy_of
         (aesopTree.goal
           (#tree duplicate_first) duplicate_first_copy) =
         SOME duplicate_original andalso
       #copy_of
         (aesopTree.goal
           (#tree duplicate_second) duplicate_only_copy) =
         SOME duplicate_original andalso
       aconv
         (#w
           (#cgoal
             (aesopTree.goal
               (#tree duplicate_second) duplicate_only_copy)))
         (clasetMeta.norm duplicate_store4
           (#w duplicate_sibling_goal)))

val dropped_homo =
  Term.mk_var
    ("aesop_dropped_homo",
     Type.bool --> Type.bool)
val dropped_bound =
  Term.mk_var ("aesop_dropped_bound", Type.bool)
val dropped_all =
  boolSyntax.mk_forall
    (dropped_bound, Term.mk_comb (dropped_homo, dropped_bound))
val dropped_root_goal =
  tree_cgoal [] []
    (boolSyntax.mk_exists
      (dropped_bound, Term.mk_comb (dropped_homo, dropped_bound)))
val (dropped_meta, dropped_store1) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val dropped_homo_goal =
  tree_cgoal [] [dropped_all]
    (Term.mk_comb (dropped_homo, dropped_meta))
val dropped_related_goal =
  tree_cgoal [] [] dropped_meta
val dropped_tree0 =
  new_tree clasetMeta.empty dropped_root_goal []
val (dropped_root, dropped_tree1) =
  pop_expected dropped_tree0
val dropped_created =
  install_tree_rapp dropped_tree1 dropped_root aesopRule.RSafe
    "dropped_exists_intro" dropped_store1
    [dropped_homo_goal, dropped_related_goal]
    [tree_creation_record [dropped_meta] []]
val [dropped_path, dropped_related] =
  #goals dropped_created
val dropped_closed =
  install_tree_rapp (#tree dropped_created) dropped_path
    aesopRule.RSafe "dropped_witness_independent" dropped_store1 [] []
val [dropped_copy] =
  #goals dropped_closed
val dropped_grounded =
  clasetMeta.ground dropped_store1
val dropped_kernel_proof =
  SPEC (boolSyntax.mk_arb Type.bool) (ASSUME dropped_all)

val _ =
  test
    ("aesop dropped metas copy related goals without synthesis subgoals",
     fn () =>
       #copy_of
         (aesopTree.goal (#tree dropped_closed) dropped_copy) =
         SOME dropped_related andalso
       aconv
         (concl dropped_kernel_proof)
         (clasetMeta.norm dropped_grounded
           (Term.mk_comb (dropped_homo, dropped_meta))))

fun search_source norm safe unsafe
      ({mode, ...} :
       {mode : clasetUnify.mode, cgoal : clasetGoal.cgoal,
        store : clasetMeta.store}) : aesopRule.ruleset =
  {norm = norm,
   safe =
     {closers = safe mode, safe0_claset = [], safe_forward = [],
      safep_claset = [], conclusion_splits = [],
      assumption_splits = []},
   unsafe = unsafe}

fun search_tree outcome =
  case outcome of
      aesopSearch.SafeSaturated tree => tree
    | aesopSearch.SafeDepthLimit _ =>
        raise Fail "unexpected aesop search depth limit"
    | aesopSearch.SafeNormalisationLimit _ =>
        raise Fail "unexpected aesop search normalisation limit"

val search_first_rule =
  aesopRule.apply_rule
    {name = "first-safe", phase = aesopRule.RSafe,
     theorem = boolTheory.TRUTH, mode = clasetUnify.Match}
val search_second_rule =
  aesopRule.apply_rule
    {name = "second-safe", phase = aesopRule.RSafe,
     theorem = boolTheory.TRUTH, mode = clasetUnify.Match}
val search_commit_tree0 =
  new_tree clasetMeta.empty (tree_cgoal [] [] boolSyntax.T) []
val search_commit_tree =
  search_tree
    (aesopSearch.safe_saturate
      {max_depth = 10,
       rules =
         search_source []
           (fn clasetUnify.Match =>
                 [search_first_rule, search_second_rule]
             | clasetUnify.Unify => [search_second_rule])
           []}
      search_commit_tree0)
val search_commit_root =
  aesopTree.root search_commit_tree

val _ =
  test
    ("aesop safe search uses Match mode and commits the first rule",
     fn () =>
       case aesopTree.child_rapps search_commit_tree search_commit_root of
           [rid] =>
             #rule (aesopTree.rapp search_commit_tree rid) =
               "first-safe" andalso
             #state
               (aesopTree.goal search_commit_tree search_commit_root) =
               aesopTree.Proved
         | _ => false)

fun duplicate_search_step input =
  case
    seq.cases
      ((clasetStep.rule_step
         {theorem = boolTheory.TRUTH, elim = false,
          mode = clasetUnify.Match}) input)
  of
      NONE => seq.empty
    | SOME (result, _) => seq.fromList [result, result]

val search_multi_rule : aesopRule.rule =
  {name = "multi-step", phase = aesopRule.RSafe,
   apply =
     aesopRule.MultiStep
       [clasetStep.rule_step
          {theorem = boolTheory.TRUTH, elim = false,
           mode = clasetUnify.Match},
        clasetStep.rule_step
          {theorem = boolTheory.TRUTH, elim = false,
           mode = clasetUnify.Match}],
   once = false}
val search_alternative_rule : aesopRule.rule =
  {name = "alternatives", phase = aesopRule.RSafe,
   apply = aesopRule.EngineStep duplicate_search_step, once = false}
val search_fallback_rule =
  aesopRule.apply_rule
    {name = "fallback", phase = aesopRule.RSafe,
     theorem = boolTheory.TRUTH, mode = clasetUnify.Match}
val search_multi_tree =
  search_tree
    (aesopSearch.safe_saturate
      {max_depth = 10,
       rules =
         search_source []
           (fn _ =>
             [search_multi_rule, search_alternative_rule,
              search_fallback_rule])
           []}
      (new_tree clasetMeta.empty
        (tree_cgoal [] [] boolSyntax.T) []))
val search_multi_root =
  aesopTree.root search_multi_tree

val _ =
  test
    ("aesop safe search dynamically rejects multi-rule alternatives",
     fn () =>
       case aesopTree.child_rapps search_multi_tree search_multi_root of
           [rid] =>
             #rule (aesopTree.rapp search_multi_tree rid) = "fallback"
         | _ => false)

val (search_postpone_meta, search_postpone_store) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val search_postpone_tree0 =
  new_tree search_postpone_store
    (tree_cgoal [] [boolSyntax.T] search_postpone_meta) []
val search_postpone_tree =
  search_tree
    (aesopSearch.safe_saturate
      {max_depth = 10,
       rules =
         search_source []
           (fn clasetUnify.Match => []
             | clasetUnify.Unify => [hd (aesopRule.closers ())])
           []}
      search_postpone_tree0)
val search_postpone_root =
  aesopTree.root search_postpone_tree

val _ =
  test
    ("aesop safe search postpones assumption close that assigns a meta",
     fn () =>
       let val root = aesopTree.goal search_postpone_tree
                        search_postpone_root
       in
         #safe_done root andalso
         null (aesopTree.child_rapps search_postpone_tree
           search_postpone_root) andalso
         (case #postponed root of
              [{rule = "assumption", node, ...}] =>
                null (clasetGoal.goals node) andalso
                not
                  (null
                    (#terms
                      (clasetMeta.bindings
                        (clasetGoal.store node))))
            | _ => false)
       end)

val (search_drop_meta, search_drop_store) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val search_drop_target =
  boolSyntax.mk_conj (search_drop_meta, boolSyntax.T)
val search_drop_assumption =
  boolSyntax.mk_conj (boolSyntax.T, boolSyntax.T)
val search_split_rule =
  aesopRule.tactic_rule
    {name = "split", phase = aesopRule.RSafe,
     tactic = NTactical.LIFT Tactic.CONJ_TAC, index = NONE}
val search_drop_tree0 =
  new_tree search_drop_store
    (tree_cgoal [] [search_drop_assumption] search_drop_target) []
val search_drop_tree =
  search_tree
    (aesopSearch.safe_saturate
      {max_depth = 10,
       rules =
         search_source []
           (fn clasetUnify.Match => [search_split_rule]
             | clasetUnify.Unify =>
                 [hd (aesopRule.closers ()), search_split_rule])
           []}
      search_drop_tree0)
val search_drop_root =
  aesopTree.root search_drop_tree

val _ =
  test
    ("aesop installed safe result drops earlier postponed results",
     fn () =>
       case aesopTree.child_rapps search_drop_tree search_drop_root of
           [rid] =>
             null
               (#postponed
                 (aesopTree.goal search_drop_tree search_drop_root))
             andalso
             #rule (aesopTree.rapp search_drop_tree rid) = "split"
         | _ => false)

val search_forward_tree0 =
  new_tree clasetMeta.empty
    (tree_cgoal [] [forward_p, forward_q] forward_target) []
fun search_forward_rules mode =
  [aesopRule.default_forward_rule
    {name = "safe-forward", phase = aesopRule.RSafe,
     theorem = forward_theorem, mode = mode}]
val search_forward_tree =
  search_tree
    (aesopSearch.safe_saturate
      {max_depth = 10,
       rules =
         search_source [] search_forward_rules []}
      search_forward_tree0)
val search_forward_root =
  aesopTree.root search_forward_tree
val [search_forward_rapp] =
  aesopTree.child_rapps search_forward_tree search_forward_root
val [search_forward_child] =
  List.concat
    (map
      (fn cluster =>
        #goals (aesopTree.cluster search_forward_tree cluster))
      (#clusters
        (aesopTree.rapp search_forward_tree search_forward_rapp)))

val _ =
  test
    ("aesop safe search prevents repeated forward hypotheses",
     fn () =>
       length (aesopTree.rapps search_forward_tree) = 1 andalso
       (case
          #forwarded
            (aesopTree.goal search_forward_tree search_forward_child)
        of
            [added] => aconv added forward_conclusion
          | _ => false) andalso
       (case aesopSearch.safe_frontier search_forward_tree of
            [(id, {asl = added :: _, w, ...})] =>
              id = search_forward_child andalso
              aconv added forward_conclusion andalso
              aconv w forward_target
          | _ => false))

val search_frontier_p =
  Term.mk_var ("aesop_search_frontier_p", Type.bool)
val search_frontier_q =
  Term.mk_var ("aesop_search_frontier_q", Type.bool)
val search_frontier_goal =
  boolSyntax.mk_imp
    (search_frontier_p,
     boolSyntax.mk_conj (search_frontier_p, search_frontier_q))
val search_disch_rule : aesopRule.rule =
  {name = "disch", phase = aesopRule.RNorm 0,
   apply = aesopRule.EngineStep clasetStep.blast_disch_step,
   once = false}
val search_frontier_tree =
  search_tree
    (aesopSearch.safe_saturate
      {max_depth = 10,
       rules =
         search_source [search_disch_rule]
           (fn _ => aesopRule.closers () @ [search_split_rule])
           []}
      (new_tree clasetMeta.empty
        (tree_cgoal [] [] search_frontier_goal) []))

val _ =
  test
    ("aesop safe saturation returns the exact normalised frontier",
     fn () =>
       case aesopSearch.safe_frontier search_frontier_tree of
           [(_, {asl = [assumption], w, ...})] =>
             aconv assumption search_frontier_p andalso
             aconv w search_frontier_q
         | _ => false)

val _ =
  test
    ("aesop search defaults bound rapps and depth",
     fn () =>
       aesopSearch.default_config =
         {max_rapps = 200, max_depth = 30})

val search_unsafe_alternatives : aesopRule.rule =
  {name = "unsafe-alternatives", phase = aesopRule.RUnsafe 70,
   apply = aesopRule.EngineStep duplicate_search_step, once = false}
val search_unsafe_alternative_outcome =
  aesopSearch.search aesopSearch.default_config
    (search_source [] (fn _ => []) [search_unsafe_alternatives])
    (new_tree clasetMeta.empty
      (tree_cgoal [] [] boolSyntax.T) [])

val _ =
  test
    ("aesop unsafe multi-rules install every alternative as sibling rapps",
     fn () =>
       case search_unsafe_alternative_outcome of
           aesopSearch.SearchProved tree =>
             let val root = aesopTree.root tree
             in
               case aesopTree.child_rapps tree root of
                   [first, second] =>
                     #rule (aesopTree.rapp tree first) =
                       "unsafe-alternatives" andalso
                     #rule (aesopTree.rapp tree second) =
                       "unsafe-alternatives" andalso
                     #prob (aesopTree.rapp tree first) = 70 andalso
                     #prob (aesopTree.rapp tree second) = 70
                 | _ => false
             end
         | _ => false)

val search_reoffer_unsafe =
  aesopRule.apply_rule
    {name = "unsafe-eighty", phase = aesopRule.RUnsafe 80,
     theorem = boolTheory.TRUTH, mode = clasetUnify.Unify}
val search_reoffer_outcome =
  aesopSearch.search aesopSearch.default_config
    (search_source []
      (fn clasetUnify.Match => []
        | clasetUnify.Unify => [hd (aesopRule.closers ())])
      [search_reoffer_unsafe])
    (new_tree search_postpone_store
      (tree_cgoal [] [boolSyntax.T] search_postpone_meta) [])

val _ =
  test
    ("aesop re-offers postponed safe results as ninety-percent rapps",
     fn () =>
       case search_reoffer_outcome of
           aesopSearch.SearchProved tree =>
             let val root = aesopTree.root tree
             in
               case aesopTree.child_rapps tree root of
                   [rid] =>
                     #rule (aesopTree.rapp tree rid) = "assumption" andalso
                     #prob (aesopTree.rapp tree rid) = 90 andalso
                     (case #unsafe_cursor (aesopTree.goal tree root) of
                          [{name = "unsafe-eighty", ...}] => true
                        | _ => false)
                 | _ => false
             end
         | _ => false)

val transitivity_x =
  Term.mk_var ("aesop_transitivity_x", numSyntax.num)
val transitivity_a =
  Term.mk_var ("aesop_transitivity_a", numSyntax.num)
val transitivity_z =
  Term.mk_var ("aesop_transitivity_z", numSyntax.num)
val transitivity_xa =
  numSyntax.mk_leq (transitivity_x, transitivity_a)
val transitivity_az =
  numSyntax.mk_leq (transitivity_a, transitivity_z)
val transitivity_xz =
  numSyntax.mk_leq (transitivity_x, transitivity_z)

fun transitivity_source
      ({mode, cgoal = {w, ...}, ...} :
       {mode : clasetUnify.mode, cgoal : clasetGoal.cgoal,
        store : clasetMeta.store}) =
  let
    val reflexivity =
      aesopRule.apply_rule
        {name = "le-reflexivity", phase = aesopRule.RSafe,
         theorem = arithmeticTheory.LESS_EQ_REFL, mode = mode}
    val transitivity =
      aesopRule.apply_rule
        {name = "le-transitivity", phase = aesopRule.RUnsafe 60,
         theorem = arithmeticTheory.LESS_EQ_TRANS, mode = mode}
  in
    {norm = [],
     safe =
       {closers = [hd (aesopRule.closers ()), reflexivity],
        safe0_claset = [], safe_forward = [], safep_claset = [],
        conclusion_splits = [], assumption_splits = []},
     unsafe = if aconv w transitivity_xz then [transitivity] else []}
  end

val transitivity_outcome =
  aesopSearch.search aesopSearch.default_config transitivity_source
    (new_tree clasetMeta.empty
      (tree_cgoal []
        [transitivity_xa, transitivity_az] transitivity_xz) [])

fun rapp_named name ({rule, ...} : aesopTree.rapp) =
  rule = name

val _ =
  test
    ("aesop proves a transitivity chain through both witness choices",
     fn () =>
       case transitivity_outcome of
           aesopSearch.SearchProved tree =>
             let
               val root = aesopTree.root tree
               val trans_rapps =
                 List.filter (rapp_named "le-transitivity")
                   (aesopTree.rapps tree)
               val trans_children =
                 case trans_rapps of
                     [rapp] =>
                       List.concat
                         (map
                           (fn cid =>
                             #goals (aesopTree.cluster tree cid))
                           (#clusters rapp))
                   | _ => []
               val first =
                 case trans_children of child :: _ => SOME child | _ => NONE
               val choices =
                 case first of
                     NONE => []
                   | SOME child =>
                       map (aesopTree.rapp tree)
                         (aesopTree.child_rapps tree child)
             in
               #state (aesopTree.goal tree root) =
                 aesopTree.Proved andalso
               List.exists (rapp_named "assumption") choices andalso
               List.exists (rapp_named "le-reflexivity") choices andalso
               List.all
                 (fn rapp =>
                   not (aesopTree.dependencies_empty (#assigned rapp)))
                 choices
             end
         | _ => false)

fun kernel_replays tree (goal as (_, target)) =
  case Tactical.VALID (aesopSearch.REPLAY_TAC tree) goal of
      ([], validation) => aconv (concl (validation [])) target
    | _ => false

val _ =
  test
    ("aesop extracts copied transitivity branches positionally",
     fn () =>
       case transitivity_outcome of
           aesopSearch.SearchProved tree =>
             kernel_replays tree
               ([transitivity_xa, transitivity_az],
                transitivity_xz)
         | _ => false)

val replay_norm_p =
  Term.mk_var ("aesop_replay_norm_p", Type.bool)
val replay_norm_target =
  boolSyntax.mk_imp (replay_norm_p, replay_norm_p)
val replay_norm_outcome =
  aesopSearch.search aesopSearch.default_config
    (search_source [search_disch_rule]
      (fn _ => aesopRule.closers ()) [])
    (new_tree clasetMeta.empty
      (tree_cgoal [] [] replay_norm_target) [])

val _ =
  test
    ("aesop replays each norm chain before its winning rapp",
     fn () =>
       case replay_norm_outcome of
           aesopSearch.SearchProved tree =>
             kernel_replays tree ([], replay_norm_target)
         | _ => false)

val replay_wrapper_target =
  boolSyntax.mk_conj (boolSyntax.T, boolSyntax.T)
fun replay_wrapper_rules mode =
  aesopRule.closers () @
  [aesopRule.apply_rule
     {name = "replay-truth", phase = aesopRule.RSafe,
      theorem = boolTheory.TRUTH, mode = mode},
   search_split_rule]
val replay_wrapper_outcome =
  aesopSearch.search aesopSearch.default_config
    (search_source []
      replay_wrapper_rules [])
    (new_tree clasetMeta.empty
      (tree_cgoal [] [] replay_wrapper_target) [])

val _ =
  test
    ("aesop replays recorded rendered-tactic actions exactly",
     fn () =>
       case replay_wrapper_outcome of
           aesopSearch.SearchProved tree =>
             kernel_replays tree ([], replay_wrapper_target)
         | _ => false)

val replay_dropped_pred =
  Term.mk_var
    ("aesop_replay_dropped_pred", Type.bool --> Type.bool)
val replay_dropped_bound =
  Term.mk_var ("aesop_replay_dropped_bound", Type.bool)
val replay_dropped_body =
  Term.mk_comb (replay_dropped_pred, replay_dropped_bound)
val replay_dropped_all =
  boolSyntax.mk_forall
    (replay_dropped_bound, replay_dropped_body)
val replay_dropped_exists =
  boolSyntax.mk_exists
    (replay_dropped_bound, replay_dropped_body)
val replay_exists_intro =
  GEN replay_dropped_pred
    (GEN replay_dropped_bound
      (DISCH replay_dropped_body
        (EXISTS
          (replay_dropped_exists, replay_dropped_bound)
          (ASSUME replay_dropped_body))))
val replay_all_elim =
  GEN replay_dropped_pred
    (GEN replay_dropped_bound
      (DISCH replay_dropped_all
        (SPEC replay_dropped_bound
          (ASSUME replay_dropped_all))))

fun replay_dropped_source
      ({mode, ...} :
       {mode : clasetUnify.mode, cgoal : clasetGoal.cgoal,
        store : clasetMeta.store}) =
  let
    val all_elim =
      aesopRule.apply_rule
        {name = "dropped-all-elim", phase = aesopRule.RSafe,
         theorem = replay_all_elim, mode = mode}
    val exists_intro =
      aesopRule.apply_rule
        {name = "dropped-exists-intro",
         phase = aesopRule.RUnsafe 50,
         theorem = replay_exists_intro, mode = mode}
  in
    {norm = [],
     safe =
       {closers = aesopRule.closers (),
        safe0_claset = [all_elim], safe_forward = [],
        safep_claset = [], conclusion_splits = [],
        assumption_splits = []},
     unsafe = [exists_intro]}
  end

val replay_dropped_goal =
  ([replay_dropped_all], replay_dropped_exists)
val replay_dropped_outcome =
  aesopSearch.search aesopSearch.default_config
    replay_dropped_source
    (new_tree clasetMeta.empty
      (tree_cgoal [] [replay_dropped_all]
        replay_dropped_exists) [])

val _ =
  test
    ("aesop grounds a dropped witness to ARB and verifies it kernel-side",
     fn () =>
       case replay_dropped_outcome of
           aesopSearch.SearchProved tree =>
             let
               val root = aesopTree.root tree
               val rid =
                 valOf
                   (List.find
                     (fn id =>
                       #rule (aesopTree.rapp tree id) =
                         "dropped-exists-intro")
                     (aesopTree.child_rapps tree root))
               val witness =
                 valOf
                   (List.find
                     (fn meta =>
                       Type.compare (type_of meta, Type.bool) = EQUAL)
                     (HOLset.listItems
                       (#terms (#created
                         (aesopTree.rapp tree rid)))))
               val grounded =
                 clasetReplay.grounded_store
                   (aesopSearch.extract tree)
             in
               aconv
                 (clasetMeta.norm grounded witness)
                 (boolSyntax.mk_arb Type.bool) andalso
               kernel_replays tree replay_dropped_goal
             end
         | _ => false)

fun replay_wrapper_record (goals, validation) =
  clasetReplay.make_record
    {kind = clasetReplay.Wrapper, target = 1, consumed = NONE,
     created = {terms = [], types = []},
     eigenvariables = map (fn _ => []) goals,
     validation = validation,
     action = clasetReplay.fixed_action (goals, validation),
     children = map (fn _ => NONE) goals}

val (corrupt_meta, corrupt_store0) =
  clasetMeta.new_meta
    {allow = [], ty = Type.bool} clasetMeta.empty
val corrupt_store_true =
  bind_tree_meta corrupt_meta boolSyntax.T corrupt_store0
val corrupt_store_false =
  bind_tree_meta corrupt_meta boolSyntax.F corrupt_store0
val corrupt_goal : Abbrev.goal =
  ([], boolSyntax.mk_conj (boolSyntax.T, boolSyntax.T))
val corrupt_split_result =
  Tactic.CONJ_TAC corrupt_goal
val corrupt_tree0 =
  new_tree corrupt_store0
    (tree_cgoal [] (#1 corrupt_goal) (#2 corrupt_goal)) []
val (corrupt_root, corrupt_tree1) =
  pop_expected corrupt_tree0
val corrupt_split =
  install_tree_rapp corrupt_tree1 corrupt_root aesopRule.RSafe
    "corrupt-split" corrupt_store0
    (map
      (fn (asl, w) => tree_cgoal [] asl w)
      (#1 corrupt_split_result))
    [replay_wrapper_record corrupt_split_result]
val [corrupt_left, corrupt_right] =
  #goals corrupt_split
val corrupt_close_result =
  Tactic.ACCEPT_TAC boolTheory.TRUTH ([], boolSyntax.T)
val corrupt_left_closed =
  install_tree_rapp (#tree corrupt_split) corrupt_left
    aesopRule.RSafe "corrupt-left" corrupt_store_true []
    [replay_wrapper_record corrupt_close_result]
val corrupt_tree =
  #tree
    (install_tree_rapp (#tree corrupt_left_closed) corrupt_right
      aesopRule.RSafe "corrupt-right" corrupt_store_false []
      [replay_wrapper_record corrupt_close_result])

val _ =
  test
    ("aesop treats conflicting winning stores as a hard replay error",
     fn () =>
       ((ignore (aesopSearch.REPLAY_TAC corrupt_tree corrupt_goal);
         false)
        handle HOL_ERR error =>
          String.isSubstring "engine bug" (Feedback.message_of error)))

val search_limit_goal = boolSyntax.T
val search_limit_close =
  aesopRule.apply_rule
    {name = "limit-close", phase = aesopRule.RUnsafe 50,
     theorem = boolTheory.TRUTH, mode = clasetUnify.Unify}
val search_rapp_limit_outcome =
  aesopSearch.search {max_rapps = 0, max_depth = 10}
    (search_source [] (fn _ => []) [search_limit_close])
    (new_tree clasetMeta.empty
      (tree_cgoal [] [] search_limit_goal) [])

val _ =
  test
    ("aesop max_rapps stops cleanly on the failure path",
     fn () =>
       case search_rapp_limit_outcome of
           aesopSearch.SearchFailed
             {tree, reason = aesopSearch.RappLimitReached,
              safe_goals = [(_, {w, ...})]} =>
                null (aesopTree.rapps tree) andalso
                aconv w search_limit_goal
         | _ => false)

val search_depth_split =
  aesopRule.tactic_rule
    {name = "depth-split", phase = aesopRule.RUnsafe 50,
     tactic = NTactical.LIFT Tactic.CONJ_TAC, index = NONE}
val search_depth_target =
  boolSyntax.mk_conj (search_limit_goal, search_limit_goal)
val search_depth_limit_outcome =
  aesopSearch.search {max_rapps = 10, max_depth = 1}
    (search_source [] (fn _ => []) [search_depth_split])
    (new_tree clasetMeta.empty
      (tree_cgoal [] [] search_depth_target) [])

val _ =
  test
    ("aesop max_depth exhausts only the offending branch and fails cleanly",
     fn () =>
       case search_depth_limit_outcome of
           aesopSearch.SearchFailed
             {tree, reason = aesopSearch.DepthLimitReached,
              safe_goals = [(_, {w, ...})]} =>
                length (aesopTree.rapps tree) = 1 andalso
                aconv w search_depth_target
         | _ => false)

val search_safe_goal_p =
  Term.mk_var ("aesop_safe_goal_p", Type.bool)
val search_safe_goal_q =
  Term.mk_var ("aesop_safe_goal_q", Type.bool)
val search_safe_goal_target =
  boolSyntax.mk_conj
    (boolSyntax.F,
     boolSyntax.mk_conj (search_safe_goal_p, search_safe_goal_q))
val search_safe_goal_outcome =
  aesopSearch.search aesopSearch.default_config
    (search_source [] (fn _ => [search_split_rule]) [])
    (new_tree clasetMeta.empty
      (tree_cgoal [] [] search_safe_goal_target) [])

fun contains_target target =
  List.exists
    (fn (_, ({w, ...} : clasetGoal.cgoal)) => aconv w target)

val _ =
  test
    ("aesop failure completes and reports the exhaustive safe goals",
     fn () =>
       case search_safe_goal_outcome of
           aesopSearch.SearchFailed
             {reason = aesopSearch.SearchExhausted, safe_goals, ...} =>
               length safe_goals = 3 andalso
               contains_target boolSyntax.F safe_goals andalso
               contains_target search_safe_goal_p safe_goals andalso
               contains_target search_safe_goal_q safe_goals
         | _ => false)

val _ =
  test
    ("aesop trace levels report outcomes expansions and full nodes",
     fn () =>
       let
         val old_trace = Feedback.current_trace "aesop"
         val notices = ref ([] : string list)
         fun remember message = notices := message :: !notices
         val _ = Feedback.set_trace "aesop" 3
         val _ =
           Lib.with_flag
             (Feedback.MESG_outstream, remember)
             (fn () =>
               (ignore
                  (aesopSearch.search aesopSearch.default_config
                    transitivity_source
                    (new_tree clasetMeta.empty
                      (tree_cgoal []
                        [transitivity_xa, transitivity_az]
                        transitivity_xz) []));
                ignore
                  (aesopSearch.search aesopSearch.default_config
                    (search_source [] (fn _ => []) [])
                    (new_tree clasetMeta.empty
                      (tree_cgoal [] [] search_limit_goal) [])))) ()
         val _ = Feedback.set_trace "aesop" old_trace
       in
         List.exists (String.isSubstring "search exhausted") (!notices)
         andalso
         List.exists (String.isSubstring "safe goal") (!notices)
         andalso
         List.exists (String.isSubstring "expanding goal") (!notices)
         andalso
         List.exists (String.isSubstring "copied") (!notices)
         andalso
         List.exists (String.isSubstring "candidate goal") (!notices)
       end)

val _ =
  test
    ("aesopLib exposes the search defaults and TypeBase cases builder",
     fn () =>
       aesopLib.default_config =
         {max_rapps = 200, max_depth = 30} andalso
       String.isPrefix "cases "
         (#name
           (aesopLib.cases_rule_for Type.bool : aesopLib.rule)))

val surface_p = Term.mk_var ("aesop_surface_p", Type.bool)
val surface_q = Term.mk_var ("aesop_surface_q", Type.bool)
val surface_r = Term.mk_var ("aesop_surface_r", Type.bool)

val _ =
  test
    ("AESOP_TAC has close-or-fail semantics",
     fn () =>
       ((ignore (aesopLib.AESOP_TAC [] ([], surface_p)); false)
        handle HOL_ERR _ => true))

val surface_global_rules =
  map (fn (_, (name, _)) => name)
    (clasetLib.rules_of (clasetLib.the_claset ()))

val surface_fact =
  DISJ1 (ASSUME surface_q) surface_r
val surface_inserted =
  residual
    (aesopLib.AESOP_SAFE_TAC [surface_fact, markerLib.NoAsms])
    ([surface_q], surface_p)

val _ =
  test
    ("AESOP_SAFE_TAC counts fact insertion as progress and retains facts",
     fn () =>
       case surface_inserted of
           [([left, left_original], left_target),
            ([right, right_original], right_target)] =>
             aconv left surface_q andalso
             aconv left_original surface_q andalso
             aconv right surface_r andalso
             aconv right_original surface_q andalso
             aconv left_target surface_p andalso
             aconv right_target surface_p
         | _ => false)

val _ =
  test
    ("AESOP_SAFE_TAC fails when insertion and safe search change nothing",
     fn () =>
       ((ignore (aesopLib.AESOP_SAFE_TAC [] ([], surface_p)); false)
        handle HOL_ERR _ => true))

val surface_conj_intro =
  DISCH surface_p
    (DISCH surface_q
      (CONJ (ASSUME surface_p) (ASSUME surface_q)))
val surface_safe_residue =
  residual
    (aesopLib.AESOP_SAFE_TAC
      [clasetLib.SIntro surface_conj_intro])
    ([], boolSyntax.mk_conj (surface_p, surface_q))

val _ =
  test
    ("AESOP_SAFE_TAC consumes claset markers and returns exact residues",
     fn () =>
       case surface_safe_residue of
           [([], left), ([], right)] =>
             aconv left surface_p andalso aconv right surface_q
         | _ => false)

val surface_norm_rule =
  DISCH surface_p
    (DISJ1 (ASSUME surface_p) surface_q)
val surface_norm_residue =
  residual
    (aesopLib.AESOP_SAFE_TAC
      [clasetLib.Norm surface_norm_rule, markerLib.NoAsms])
    ([], boolSyntax.mk_disj (surface_p, surface_q))

val _ =
  test
    ("AESOP_SAFE_TAC consumes Norm markers through the norm builder",
     fn () =>
       case surface_norm_residue of
           [([], target)] => aconv target surface_p
         | _ => false)

val surface_implication =
  boolSyntax.mk_imp (surface_p, surface_q)
val surface_forward_rule = ASSUME surface_implication

val _ =
  test
    ("AESOP_TAC consumes unsafe Forward markers",
     fn () =>
       null
         (residual
           (aesopLib.AESOP_TAC
             [clasetLib.Forward surface_forward_rule,
              markerLib.NoAsms])
           ([surface_p, surface_implication], surface_q)))

val _ =
  test
    ("AESOP_SAFE_TAC consumes SForward markers",
     fn () =>
       null
         (residual
           (aesopLib.AESOP_SAFE_TAC
             [clasetLib.SForward surface_forward_rule,
              markerLib.NoAsms])
           ([surface_p, surface_implication], surface_q)))

val surface_function =
  Term.mk_var
    ("aesop_surface_function", Type.bool --> Type.bool)
val surface_application =
  Term.mk_comb (surface_function, surface_p)
val surface_rewrite =
  ASSUME (boolSyntax.mk_eq (surface_application, surface_p))

val _ =
  test
    ("AESOP_TAC installs Simp arguments in the invocation simpset",
     fn () =>
       null
         (residual
           (aesopLib.AESOP_TAC
             [clasetLib.Simp surface_rewrite, markerLib.NoAsms])
           ([surface_p, concl surface_rewrite],
            surface_application)))

val surface_iff_function =
  Term.mk_var
    ("aesop_surface_iff_function", Type.bool --> Type.bool)
val surface_iff_application =
  Term.mk_comb (surface_iff_function, surface_p)
val surface_iff =
  ASSUME (boolSyntax.mk_eq (surface_iff_application, surface_p))

val _ =
  test
    ("AESOP_TAC installs Iff arguments as rules and rewrites",
     fn () =>
       null
         (residual
           (aesopLib.AESOP_TAC
             [clasetLib.Iff surface_iff, markerLib.NoAsms])
           ([surface_p, concl surface_iff],
            surface_iff_application)))

val surface_control_function =
  Term.mk_var
    ("aesop_surface_control_function", Type.bool --> Type.bool)
val surface_control_application =
  Term.mk_comb (surface_control_function, surface_p)
val surface_control_equality =
  boolSyntax.mk_eq (surface_control_application, boolSyntax.T)

val surface_with_asms =
  residual
    (aesopLib.AESOP_SAFE_TAC [])
    ([surface_control_equality], surface_control_application)
val surface_without_asms =
  SOME
    (residual
      (aesopLib.AESOP_SAFE_TAC [markerLib.NoAsms])
      ([surface_control_equality], surface_control_application))
  handle HOL_ERR _ => NONE

val _ =
  test
    ("AESOP_SAFE_TAC forwards generic simplifier controls",
     fn () =>
       null surface_with_asms andalso
       (case surface_without_asms of
            SOME [(_, target)] =>
              aconv target surface_control_application
          | _ => false))

val surface_explicit_simpset =
  simpLib.++
    (simpLib.empty_ss, simpLib.rewrites [surface_rewrite])

val _ =
  test
    ("CS_AESOP_TAC uses its explicit claset and simpset",
     fn () =>
       null
         (residual
           (aesopLib.CS_AESOP_TAC
             aesopLib.default_config clasetLib.empty_cs
             surface_explicit_simpset)
           ([surface_p, concl surface_rewrite],
            surface_application)))

val surface_explicit_claset =
  clasetLib.add_rule
    {kind = clasetRules.Intro, safe = true, prio = NONE}
    ("aesop-selftest-explicit-safe", surface_conj_intro)
    clasetLib.empty_cs
val surface_explicit_residue =
  residual
    (aesopLib.CS_AESOP_SAFE_TAC
      aesopLib.default_config surface_explicit_claset
      simpLib.empty_ss)
    ([], boolSyntax.mk_conj (surface_p, surface_q))

val _ =
  test
    ("CS_AESOP_SAFE_TAC saturates its explicit safe context",
     fn () =>
       case surface_explicit_residue of
           [([], left), ([], right)] =>
             aconv left surface_p andalso aconv right surface_q
         | _ => false)

val _ =
  test
    ("aesop invocation arguments do not leak into the global claset",
     fn () =>
       map (fn (_, (name, _)) => name)
         (clasetLib.rules_of (clasetLib.the_claset ())) =
       surface_global_rules)

fun aesop_closes proposition =
  null (residual (aesopLib.AESOP_TAC []) ([], proposition))

val list_strength_ss =
  simpLib.named_rewrites "aesop-selftest-list-strength"
    [listTheory.APPEND, listTheory.LENGTH, listTheory.REVERSE_DEF,
     listTheory.MEM]

fun aesop_list_closes proposition =
  BasicProvers.with_simpset_updates
    (fn ss =>
      simpLib.++ (ss, list_strength_ss))
    aesop_closes proposition

val list_strength_smoke =
  [("append",
   ``((x:'a) :: xs) ++ ys = x :: (xs ++ ys)``),
   ("length",
    ``LENGTH [(x:'a); y] = SUC (SUC 0)``),
   ("reverse",
    ``REVERSE [(x:'a); y] = [y; x]``),
   ("membership",
    ``MEM (x:'a) ([y] ++ xs) <=> (x = y) \/ MEM x xs``)]

val _ =
  List.app
    (fn (name, proposition) =>
      test
        ("AESOP_TAC listTheory strength smoke: " ^ name,
         fn () => aesop_list_closes proposition))
    list_strength_smoke

val pelletier_propositional_smoke =
  [(1, ``(P ==> Q) <=> (~Q ==> ~P)``),
   (2, ``~~P <=> P``),
   (4, ``(~P ==> Q) <=> (~Q ==> P)``),
   (5, ``((P \/ Q) ==> (P \/ R)) ==> (P \/ (Q ==> R))``),
   (8, ``((P ==> Q) ==> P) ==> P``)]

val _ =
  List.app
    (fn (number, proposition) =>
      test
        ("AESOP_TAC Pelletier " ^ Int.toString number ^
         " propositional smoke",
         fn () => aesop_closes proposition))
    pelletier_propositional_smoke

val strength_safe_imp_residue =
  residual
    (aesopLib.AESOP_SAFE_TAC [])
    ([],
     boolSyntax.mk_imp
       (surface_p, boolSyntax.mk_conj (surface_q, surface_r)))

val _ =
  test
    ("AESOP_SAFE_TAC returns the exact implication-conjunction frontier",
     fn () =>
       case strength_safe_imp_residue of
           [([left_assumption], left), ([right_assumption], right)] =>
             aconv left_assumption surface_p andalso
             aconv right_assumption surface_p andalso
             aconv left surface_q andalso
             aconv right surface_r
         | _ => false)

val strength_safe_disj_residue =
  residual
    (aesopLib.AESOP_SAFE_TAC [])
    ([], boolSyntax.mk_disj (surface_p, surface_q))

val _ =
  test
    ("AESOP_SAFE_TAC returns the exact safe disjunction frontier",
     fn () =>
       case strength_safe_disj_residue of
           [([assumption], target)] =>
             aconv assumption (boolSyntax.mk_neg surface_q) andalso
             aconv target surface_p
         | _ => false)

val surface_augmented =
  Term.mk_var ("aesop_surface_augmented", Type.bool)
val surface_augmented_called = ref false
val _ =
  aesopLib.augment_aesop
    {name = "aesop-selftest-session-tactic",
     phase = aesopRule.RNorm ~1,
     tactic =
       NTactical.LIFT
         (fn goal =>
           (surface_augmented_called := true;
            Tactic.ACCEPT_TAC (ASSUME surface_augmented) goal))}

val _ =
  test
    ("augment_aesop wires session-only tactics into public search",
     fn () =>
       null
         (residual
           (aesopLib.AESOP_TAC [])
           ([surface_augmented], surface_augmented)) andalso
       !surface_augmented_called)
