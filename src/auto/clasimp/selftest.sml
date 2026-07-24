open HolKernel testutils

fun test (name, check) =
  (tprint name;
   if check () then OK () else die "failed")

fun residual tactic goal =
  #1 (Tactical.VALID tactic goal)

fun solves tactic goal =
  null (residual tactic goal)

val solver_ss = simpLib.clear_rules (clasimpLib.clasimp_ss ())
val safe_simp = clasimpLib.safe_asm_full_simp solver_ss []

val _ =
  test
    ("safe solver accepts an alpha-matching assumption",
     fn () =>
       solves safe_simp
         ([``(\x:'a. P x) a : bool``], ``(\y:'a. P y) a : bool``))

val _ =
  test
    ("safe solver proves an alpha-reflexive equality",
     fn () =>
       solves safe_simp
         ([], ``(\x:'a. f x) = (\y:'a. f y)``))

val _ =
  test
    ("safe solver proves truth",
     fn () => solves safe_simp ([], boolSyntax.T))

val _ =
  test
    ("safe solver closes from a false assumption",
     fn () =>
       solves safe_simp
         ([boolSyntax.F], ``clasimp_false_goal:bool``))

val _ =
  test
    ("safe solver does not instantiate an existential witness",
     fn () =>
       case residual safe_simp
         ([``P (clasimp_witness:'a) : bool``], ``?x:'a. P x``) of
           [goal] =>
             boolSyntax.goal_eq
               goal
                 ([``P (clasimp_witness:'a) : bool``], ``?x:'a. P x``)
         | _ => false)

val _ =
  test
    ("clasimpset fixes conditional-rewrite depth at forty",
     fn () =>
       #cond_depth
         (simpLib.traversedata_for_ss (clasimpLib.clasimp_ss ())) =
       SOME 40)

val _ =
  test
    ("clasimpset carries the splitter",
     fn () =>
       let
         val original =
           ``P (if clasimp_split_b then clasimp_split_x:'a
               else clasimp_split_y) : bool``
       in
         case residual
           (simpLib.SIMP_TAC (clasimpLib.clasimp_ss ()) [])
           ([], original) of
             [([], result)] =>
               not (aconv result original) andalso
               not (can (find_term boolSyntax.is_cond) result)
           | _ => false
       end)

val derived_lhs = ``clasimp_derived_lhs:'a``
val derived_rhs = ``clasimp_derived_rhs:'a``
val derived_rule = ASSUME (boolSyntax.mk_eq (derived_lhs, derived_rhs))
val derived_before =
  Conv.QCONV
    (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) []) derived_lhs

val _ =
  BasicProvers.augment_srw_ss
    [simpLib.named_rewrites "clasimp-selftest-derived" [derived_rule]]

val derived_after =
  Conv.QCONV
    (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) []) derived_lhs

val _ =
  test
    ("clasimpset cache recomputes after augment_srw_ss",
     fn () =>
       aconv (snd (boolSyntax.dest_eq (concl derived_before)))
         derived_lhs andalso
       aconv (snd (boolSyntax.dest_eq (concl derived_after)))
         derived_rhs)

val mutual_goal =
  ([``P (a:'a) : bool``, ``a:'a = b``], ``mutual_q:bool``)
val mutual_expected =
  [([``P (b:'a) : bool``, ``a:'a = b``], ``mutual_q:bool``)]

val _ =
  test
    ("asm_full_simp uses later assumptions mutually",
     fn () =>
       ListPair.allEq
         (fn (goal1, goal2) => boolSyntax.goal_eq goal1 goal2)
         (residual
            (clasimpLib.asm_full_simp BasicProvers.bool_ss [])
            mutual_goal,
          mutual_expected))

val chain_goal =
  ([``(f:'a -> 'b) x = g x``, ``(g:'a -> 'b) x = z``,
    ``R ((f:'a -> 'b) x) : bool``], ``chain_s:bool``)
val chain_expected =
  [([``(f:'a -> 'b) x = z``, ``(g:'a -> 'b) x = z``,
     ``R (z:'b) : bool``], ``chain_s:bool``)]

val _ =
  test
    ("asm_full_simp closes a three-assumption mutual chain",
     fn () =>
       ListPair.allEq
         (fn (goal1, goal2) => boolSyntax.goal_eq goal1 goal2)
         (residual
            (clasimpLib.asm_full_simp BasicProvers.bool_ss [])
            chain_goal,
          chain_expected))

fun tactic_fails tactic goal =
  (ignore (Tactical.VALID tactic goal); false)
  handle HOL_ERR _ => true

fun same_thm left right =
  Term.aconv (concl left) (concl right)

fun same_spec
      ({kind = kind1, safe = safe1, prio = prio1} :
        clasetRules.rulespec)
      ({kind = kind2, safe = safe2, prio = prio2} :
        clasetRules.rulespec) =
  kind1 = kind2 andalso safe1 = safe2 andalso prio1 = prio2

val marker_rule_cases :
    (string * thm * clasetRules.rulespec) list =
  [("SIntro", clasetLib.SIntro boolTheory.AND_INTRO_THM,
    {kind = clasetRules.Intro, safe = true, prio = NONE}),
   ("Intro", clasetLib.Intro boolTheory.AND_INTRO_THM,
    {kind = clasetRules.Intro, safe = false, prio = NONE}),
   ("SElim", clasetLib.SElim boolTheory.OR_ELIM_THM,
    {kind = clasetRules.Elim, safe = true, prio = NONE}),
   ("Elim", clasetLib.Elim boolTheory.OR_ELIM_THM,
    {kind = clasetRules.Elim, safe = false, prio = NONE}),
   ("SDest", clasetLib.SDest boolTheory.OR_ELIM_THM,
    {kind = clasetRules.Dest, safe = true, prio = NONE}),
   ("Dest", clasetLib.Dest boolTheory.OR_ELIM_THM,
    {kind = clasetRules.Dest, safe = false, prio = NONE})]

fun claset_marker_routed (_, marker, expected_spec) =
  let
    fun inspect cs _ simp_args =
      case (clasetLib.rules_of cs, simp_args) of
          ([(spec, _)], []) =>
            if same_spec spec expected_spec then Tactical.ALL_TAC
            else Tactical.NO_TAC
        | _ => Tactical.NO_TAC
    val tactic =
      clasimpLib.process_clasimp_args inspect
        clasetLib.empty_cs simpLib.empty_ss [marker]
  in
    not (tactic_fails tactic ([], ``clasimp_marker_goal:bool``))
  end

val _ =
  test
    ("argument processor routes every claset theorem marker",
     fn () => List.all claset_marker_routed marker_rule_cases)

val _ =
  test
    ("argument processor consumes Del in the claset partition",
     fn () =>
       let
         val base =
           clasetLib.add_sintros
             [("clasimp-delete", boolTheory.AND_INTRO_THM)]
             clasetLib.empty_cs
         fun inspect cs _ simp_args =
           if null (clasetLib.rules_of cs) andalso null simp_args
           then Tactical.ALL_TAC
           else Tactical.NO_TAC
         val tactic =
           clasimpLib.process_clasimp_args inspect base
             simpLib.empty_ss [clasetLib.Del "clasimp-delete"]
       in
         not (tactic_fails tactic ([], ``clasimp_del_goal:bool``))
       end)

val _ =
  test
    ("Simp marker adds its theorem to the invocation simpset",
     fn () =>
       let
         fun simplify _ ss simp_args =
           simpLib.SIMP_TAC ss simp_args
         val tactic =
           clasimpLib.process_clasimp_args simplify
             clasetLib.empty_cs simpLib.empty_ss
             [clasetLib.Simp
                (CONJUNCT2 (CONJUNCT2 boolTheory.NOT_CLAUSES))]
       in
         solves tactic ([], ``~F``)
       end)

val generic_simp_markers =
  [markerLib.AC boolTheory.AND_CLAUSES boolTheory.OR_CLAUSES,
   markerLib.Cong boolTheory.AND_CLAUSES,
   markerLib.Split boolTheory.OR_CLAUSES,
   markerLib.Excl "clasimp-selftest",
   markerLib.ExclSF "clasimp-selftest",
   markerLib.FRAG "clasimp-selftest",
   markerLib.mk_Req0 boolTheory.TRUTH,
   markerLib.mk_ReqD boolTheory.TRUTH,
   BoundedRewrites.Once boolTheory.TRUTH,
   BoundedRewrites.Ntimes boolTheory.IMP_CLAUSES 2,
   markerLib.NoAsms,
   markerLib.IgnAsm [QUOTE "clasimp_ignored"]]

val _ =
  test
    ("argument processor preserves every generic simp control",
     fn () =>
       let
         fun inspect cs _ simp_args =
           if null (clasetLib.rules_of cs) andalso
              ListPair.allEq (fn (left, right) => same_thm left right)
                (simp_args, generic_simp_markers)
           then Tactical.ALL_TAC
           else Tactical.NO_TAC
         val tactic =
           clasimpLib.process_clasimp_args inspect
             clasetLib.empty_cs simpLib.empty_ss
             generic_simp_markers
       in
         not (tactic_fails tactic ([], ``clasimp_generic_goal:bool``))
       end)

val _ =
  test
    ("Once reaches the simp argument list without being unwrapped",
     fn () =>
       let
         val once = BoundedRewrites.Once boolTheory.IMP_CLAUSES
         fun inspect _ _ [theorem] =
               let val (payload, bound) =
                 BoundedRewrites.DEST_BOUNDED theorem
               in
                 if bound = 1 andalso
                    same_thm payload boolTheory.IMP_CLAUSES
                 then Tactical.ALL_TAC
                 else Tactical.NO_TAC
               end
           | inspect _ _ _ = Tactical.NO_TAC
         val tactic =
           clasimpLib.process_clasimp_args inspect
             clasetLib.empty_cs simpLib.empty_ss [once]
       in
         not (tactic_fails tactic ([], ``clasimp_once_goal:bool``))
       end)

val _ =
  test
    ("plain theorems are inserted before the clasimp script",
     fn () =>
       let
         val p = ``clasimp_insert_p:bool``
         val fact = DISCH p (ASSUME p)
         fun leave_residue _ _ _ = Tactical.ALL_TAC
         val tactic =
           clasimpLib.process_clasimp_args leave_residue
             clasetLib.empty_cs simpLib.empty_ss [fact]
       in
         case residual tactic ([], ``clasimp_insert_goal:bool``) of
             [([assumption], _)] => Term.aconv assumption (concl fact)
           | _ => false
       end)

val _ =
  test
    ("Iff marker reports its explicit task-ten hook",
     fn () =>
       let
         fun leave_residue _ _ _ = Tactical.ALL_TAC
       in
         (ignore
            (clasimpLib.process_clasimp_args leave_residue
              clasetLib.empty_cs simpLib.empty_ss
              [clasetLib.Iff boolTheory.IMP_CLAUSES]
              ([], ``clasimp_iff_goal:bool``));
          false)
         handle HOL_ERR error =>
           Feedback.message_of error =
             "Iff marker is not yet implemented"
       end)

val _ =
  test
    ("argument processor honors Abbr before partitioning",
     fn () =>
       let
         val name = "clasimp_abbreviated"
         val abbreviated = Term.mk_var (name, Type.bool)
         val proposition = ``clasimp_abbreviation_p:bool``
         val goal =
           ([markerSyntax.mk_abbrev (name, proposition), proposition],
            abbreviated)
         fun accept _ _ _ =
           Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC
         fun tactic controls =
           clasimpLib.process_clasimp_args accept
             clasetLib.empty_cs simpLib.empty_ss controls
       in
         tactic_fails (tactic []) goal andalso
         solves
           (tactic [markerLib.Abbr [QUOTE name]]) goal
       end)

val wrapper_ss =
  simpLib.++
    (simpLib.clear_rules (clasimpLib.clasimp_ss ()),
     simpLib.rewrites
       [CONJUNCT2 (CONJUNCT2 boolTheory.NOT_CLAUSES)])

val wrapper_goal : Abbrev.goal = ([], ``~F``)

val _ =
  test
    ("add_simp_wrapper reaches the FAST unsafe rung",
     fn () =>
       let
         fun fast cs =
           NTactical.DETERM (classicalLib.CS_FAST_TAC cs)
       in
         tactic_fails (fast clasetLib.empty_cs) wrapper_goal andalso
         solves
           (fast
             (clasimpLib.add_simp_wrapper wrapper_ss
               clasetLib.empty_cs))
           wrapper_goal
       end)

val _ =
  test
    ("add_simp_wrapper reaches the bounded depth rung",
     fn () =>
       let
         fun depth cs =
           NTactical.DETERM
             (classicalLib.CS_DEPTH_SOLVE_TAC {dup = false} 1 cs)
       in
         tactic_fails (depth clasetLib.empty_cs) wrapper_goal andalso
         solves
           (depth
             (clasimpLib.add_simp_wrapper wrapper_ss
               clasetLib.empty_cs))
           wrapper_goal
       end)

val _ =
  test
    ("add_safe_simp_wrapper reaches the SAFE rung",
     fn () =>
       let
         fun safe cs =
           NTactical.DETERM (classicalLib.CS_SAFE_TAC cs)
       in
         tactic_fails (safe clasetLib.empty_cs) wrapper_goal andalso
         solves
           (safe
             (clasimpLib.add_safe_simp_wrapper wrapper_ss
               clasetLib.empty_cs))
           wrapper_goal
       end)

val _ =
  test
    ("add_safe_simp_wrapper reaches the CLARIFY rung",
     fn () =>
       let
         fun clarify cs =
           NTactical.DETERM (classicalLib.CS_CLARIFY_TAC cs)
       in
         tactic_fails (clarify clasetLib.empty_cs) wrapper_goal andalso
         solves
           (clarify
             (clasimpLib.add_safe_simp_wrapper wrapper_ss
               clasetLib.empty_cs))
           wrapper_goal
       end)

val _ =
  test
    ("re-adding a simp wrapper overwrites its named slot",
     fn () =>
       let
         val inert_ss =
           simpLib.clear_rules (clasimpLib.clasimp_ss ())
         val unsafe_cs =
           clasimpLib.add_simp_wrapper inert_ss
             (clasimpLib.add_simp_wrapper wrapper_ss
               clasetLib.empty_cs)
         val safe_cs =
           clasimpLib.add_safe_simp_wrapper inert_ss
             (clasimpLib.add_safe_simp_wrapper wrapper_ss
               clasetLib.empty_cs)
         val unsafe =
           NTactical.DETERM (classicalLib.CS_FAST_TAC unsafe_cs)
         val safe =
           NTactical.DETERM (classicalLib.CS_SAFE_TAC safe_cs)
       in
         tactic_fails unsafe wrapper_goal andalso
         tactic_fails safe wrapper_goal
       end)

val _ =
  test
    ("safe simp wrapper preserves rigid engine metavariables",
     fn () =>
       let
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.bool}
             clasetMeta.empty
         val target = combinSyntax.mk_I meta
         val node =
           clasetGoal.create
             {goals = [{params = [], asl = [], w = target}],
              store = store, level = 0}
         val ss =
           simpLib.++
             (simpLib.clear_rules (clasimpLib.clasimp_ss ()),
              simpLib.rewrites [combinTheory.I_THM])
         val cs =
           clasimpLib.add_safe_simp_wrapper ss clasetLib.empty_cs
       in
         case seq.cases (clasetStep.safe_step cs (node, 1)) of
             NONE => false
           | SOME ((_, next), _) =>
               (case clasetGoal.goals next of
                    [{w, ...}] =>
                      Term.aconv w meta andalso
                      not
                        (null
                          (clasetMeta.metas_of
                            (clasetGoal.store next) w))
                  | _ => false)
       end)
