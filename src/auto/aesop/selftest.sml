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
     node =
       tree_node store
         (#level (aesopTree.goal tree parent) + 1) children}
    tree

fun close_tree_goal tree id =
  #tree
    (install_tree_rapp tree id aesopRule.RSafe "close"
      (aesopTree.active_store (aesopTree.goal tree id)) [] [])

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
