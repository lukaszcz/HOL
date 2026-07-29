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
