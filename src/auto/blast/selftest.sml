open HolKernel boolSyntax testutils blastTerm
open clasetSeedTheory

infix 9 $

fun test (name, check) =
  (tprint name;
   if check () then OK () else die "failed")

fun unassigned v =
  case !v of
      NONE => true
    | SOME _ => false

val _ =
  test
    ("reserved and real constant heads cannot collide",
     fn () =>
       goal_name = "*Goal*" andalso false_name = "*False*" andalso
       const_name {Thy = "bool", Name = "~"} = "bool$~" andalso
       isGoal (mkGoal (Free "p")) andalso
       not (isGoal (Const (const_name {Thy = "x", Name = "Goal"}, []))))

val _ =
  test
    ("occurs check rejects direct and indirect cycles",
     fn () =>
       let
         val state = newState ()
         val x = ref NONE
         val y = ref NONE
         val direct = not (unify state ([], Var x, Free "f" $ Var x))
         val linked = unify state ([], Var x, Var y)
         val indirect = not (unify state ([], Var y, Free "g" $ Var x))
       in
         direct andalso linked andalso indirect andalso
         trailSize state = 1 andalso unassigned y
       end)

val _ =
  test
    ("occurs check rejects dangling de Bruijn variables",
     fn () =>
       let
         val state = newState ()
         val v = ref NONE
       in
         not (unify state ([], Var v, Bound 0)) andalso
         not (unify state ([], Abs ("x", Var v),
                            Abs ("y", Bound 0))) andalso
         unassigned v andalso trailSize state = 0
       end)

val _ =
  test
    ("Skolem dependencies enforce the eigenvariable condition",
     fn () =>
       let
         val denied_state = newState ()
         val denied = ref NONE
         val allowed_state = newState ()
         val allowed = ref NONE
         val other = ref NONE
       in
         not (unify denied_state
                ([], Var denied, Skolem ("s", [denied]))) andalso
         unassigned denied andalso
         unify allowed_state
           ([], Var allowed, Skolem ("t", [other])) andalso
         trailSize allowed_state = 1
       end)

val _ =
  test
    ("unification decomposes abstractions, applications and type args",
     fn () =>
       let
         val state = newState ()
         val type_var = ref NONE
         val left =
           Abs ("x", Const ("c", [Var type_var]) $ Bound 0)
         val right =
           Abs ("y", Const ("c", [Free "ty"]) $ Bound 0)
       in
         unify state ([], left, right) andalso
         not (unify state
           ([], Const ("c", [Free "a"]), Const ("c", []))) andalso
         not (unify state
           ([], Const ("c", []), Const ("d", [])))
       end)

val _ =
  test
    ("failed unification rolls all branch assignments back",
     fn () =>
       let
         val state = newState ()
         val v = ref NONE
         val left = (Const ("f", []) $ Var v) $ Const ("a", [])
         val right = (Const ("f", []) $ Free "x") $ Const ("b", [])
       in
         not (unify state ([], left, right)) andalso
         unassigned v andalso trailSize state = 0
       end)

val _ =
  test
    ("clearTo restores exactly the requested trail suffix",
     fn () =>
       let
         val state = newState ()
         val x = ref NONE
         val y = ref NONE
         val first = unify state ([], Var x, Free "a")
         val mark = trailSize state
         val second = unify state ([], Var y, Free "b")
         val _ = clearTo state mark
         val x_ok =
           case !x of
               SOME (Free "a") => true
             | _ => false
       in
         first andalso second andalso x_ok andalso unassigned y andalso
         trailSize state = mark
       end)

val _ =
  test
    ("norm chases assignments and beta-normalizes applications",
     fn () =>
       let
         val state = newState ()
         val v = ref NONE
         val _ = unify state ([], Var v, Free "z")
         val beta = Abs ("x", Bound 0) $ Var v
         val typed = Const ("c", [Abs ("x", Bound 0) $ Free "a"])
         val under_abs = Abs ("x", Abs ("y", Bound 0) $ Free "a")
       in
         aconv (norm beta, Free "z") andalso
         aconv (norm typed, Const ("c", [Free "a"])) andalso
         aconv (norm under_abs, under_abs)
       end)

val _ =
  test
    ("norm prunes assigned Skolem dependency references",
     fn () =>
       let
         val state = newState ()
         val assigned = ref NONE
         val live = ref NONE
         val _ = unify state ([], Var assigned, Var live)
       in
         case norm (Skolem ("s", [assigned])) of
             Skolem ("s", [v]) => v = live
           | _ => false
       end)

val _ =
  test
    ("wkNorm performs head beta and eta contraction",
     fn () =>
       let
         val beta = (Abs ("x", Bound 0) $ Free "a") $ Free "b"
         val eta = Abs ("x", Free "f" $ Bound 0)
         val no_eta = Abs ("x", Bound 0 $ Bound 0)
       in
         aconv (wkNorm beta, Free "a" $ Free "b") andalso
         aconv (wkNorm eta, Free "f") andalso
         aconv (wkNorm no_eta, no_eta)
       end)

val _ =
  test
    ("de Bruijn substitution shifts arguments without capture",
     fn () =>
       let
         val body = Abs ("y", Bound 1)
       in
         aconv (subst_bound (Free "a", body), Abs ("y", Free "a"))
         andalso
         aconv (subst_bound (Bound 0, body), Abs ("y", Bound 1))
         andalso loose_bnos (Abs ("x", Bound 1)) = [0]
       end)

val _ =
  test
    ("rule-local variables are assigned off-trail in preference",
     fn () =>
       let
         val state = newState ()
         val branch = ref NONE
         val rule_var = ref NONE
         val ok = unify state ([rule_var], Var branch, Var rule_var)
         val local_ok =
           case !rule_var of
               SOME (Var v) => v = branch
             | _ => false
       in
         ok andalso local_ok andalso unassigned branch andalso
         trailSize state = 0
       end)

val _ =
  test
    ("failed unification restores only trailed branch variables",
     fn () =>
       let
         val state = newState ()
         val rule_var = ref NONE
         val branch = ref NONE
         val left =
           Const ("f", [Var rule_var, Var branch, Const ("a", [])])
         val right =
           Const ("f", [Free "l", Free "b", Const ("c", [])])
         val failed = not (unify state ([rule_var], left, right))
         val local_ok =
           case !rule_var of
               SOME (Free "l") => true
             | _ => false
       in
         failed andalso local_ok andalso unassigned branch andalso
         trailSize state = 0
       end)

fun head_args term =
  case strip_comb term of
      (Const (name, args), actual) => (name, args, actual)
    | _ => raise Fail "head_args"

fun is_head name term =
  case head_args term of (head, _, _) => head = name

fun group_lengths ({premises, ...} : blastRule.tableau_rule) =
  map length premises

fun has_skolem (Skolem _) = true
  | has_skolem (Const (_, args)) = List.exists has_skolem args
  | has_skolem (Abs (_, body)) = has_skolem body
  | has_skolem (left $ right) =
      has_skolem left orelse has_skolem right
  | has_skolem _ = false

fun stored_elim ({origin, ...} : blastRule.tableau_rule) =
  case origin of
      blastRule.Stored {is_elim, ...} => is_elim
    | _ => false

val _ =
  test
    ("goal translation has faithful per-constant type arguments",
     fn () =>
       let
         val alpha = Type.mk_vartype "'a"
         val p = mk_var ("p", bool)
         val f = mk_var ("f", alpha --> bool)
         val (_, bool_args, _) =
           head_args (blastRule.fromGoalTerm (mk_eq (p, p)))
         val (_, fun_args, _) =
           head_args (blastRule.fromGoalTerm (mk_eq (f, f)))
         val fun_type =
           list_comb
             (Const (const_name {Thy = "min", Name = "fun"}, []),
              [Free "'a",
               Const (const_name {Thy = "min", Name = "bool"}, [])])
       in
         case (bool_args, fun_args) of
             ([Const ("min$bool", [])], [encoded]) =>
               aconv (encoded, fun_type)
           | _ => false
       end)

val _ =
  test
    ("rule type variables are shared mutable typargs",
     fn () =>
       let
         val cache = blastRule.newCache ()
         val converted =
           blastRule.convertIntro cache [] boolTheory.EQ_REFL
         val converted_again =
           blastRule.convertIntro cache [] boolTheory.EQ_REFL
         val (_, equality_args, equality_terms) =
           head_args (rand (#pattern converted))
         val (_, other_args, _) =
           head_args (rand (#pattern converted_again))
       in
         case (equality_args, other_args, equality_terms) of
             ([Var variable], [Var other], [Var left, Var right]) =>
               !variable = NONE andalso !other = NONE andalso
               variable <> other andalso left = right
           | _ => false
       end)

val _ =
  test
    ("goal intake uses conclusion then assumptions in head-first order",
     fn () =>
       let
         val p = mk_var ("p", bool)
         val q = mk_var ("q", bool)
         val r = mk_var ("r", bool)
       in
         case blastRule.initialBranch ([p, q], r) of
             [(Const ("*Goal*", []) $ Skolem (rname, []), true),
              (Skolem (pname, []), true),
              (Skolem (qname, []), true)] =>
               pname <> qname andalso pname <> rname andalso
               qname <> rname
           | _ => false
       end)

val _ =
  test
    ("intro conversion goldens cover conjunction disjunction and exists",
     fn () =>
       let
         val cache = blastRule.newCache ()
         val conjunction =
           blastRule.convertIntro cache [] boolTheory.AND_INTRO_THM
         val disjunction =
           blastRule.convertIntro cache [] DISJ_CINTRO_THM
         val exists =
           blastRule.convertIntro cache [] EXISTS_INTRO_THM
       in
         not (stored_elim conjunction) andalso
         group_lengths conjunction = [1, 1] andalso
         group_lengths disjunction = [2] andalso
         group_lengths exists = [1] andalso
         is_head "bool$/\\" (rand (#pattern conjunction)) andalso
         is_head "bool$\\/" (rand (#pattern disjunction)) andalso
         is_head "bool$?" (rand (#pattern exists))
       end)

val _ =
  test
    ("elim conversion goldens cover conjunction disjunction exists and iff",
     fn () =>
       let
         val cache = blastRule.newCache ()
         val conjunction = blastRule.convertElim cache [] CONJ_ELIM_THM
         val disjunction =
           blastRule.convertElim cache [] boolTheory.OR_ELIM_THM
         val exists = blastRule.convertElim cache [] EXISTS_ELIM_THM
         val iff = blastRule.convertElim cache [] IFF_CELIM_THM
       in
         case (conjunction, disjunction, exists, iff) of
             (SOME conjunction', SOME disjunction', SOME exists',
              SOME iff') =>
               stored_elim conjunction' andalso
               group_lengths conjunction' = [2] andalso
               group_lengths disjunction' = [1, 1] andalso
               group_lengths exists' = [1] andalso
               group_lengths iff' = [2, 2] andalso
               is_head "bool$/\\" (#pattern conjunction') andalso
               is_head "bool$\\/" (#pattern disjunction') andalso
               is_head "bool$?" (#pattern exists') andalso
               is_head "min$=" (#pattern iff') andalso
               (case #premises exists' of
                    [[formula]] => has_skolem formula
                  | _ => false)
           | _ => false
       end)

fun pseudo_origin expected ({origin, ...} : blastRule.tableau_rule) =
  case (expected, origin) of
      ("imp", blastRule.ImpIntro) => true
    | ("all", blastRule.AllIntro) => true
    | _ => false

val _ =
  test
    ("goal-directed implication and universal pseudo-rules have exact shapes",
     fn () =>
       let
         val cache = blastRule.newCache ()
         val claset = clasetLib.empty_cs
         val p = mk_var ("p", bool)
         val q = mk_var ("q", bool)
         val alpha = Type.mk_vartype "'a"
         val x = mk_var ("x", alpha)
         val pred = mk_var ("P", alpha --> bool)
         val imp_formula =
           mkGoal (blastRule.fromGoalTerm (mk_imp (p, q)))
         val all_formula =
           mkGoal
             (blastRule.fromGoalTerm
                (mk_forall (x, mk_comb (pred, x))))
         val imp_rules = blastRule.safeRules cache claset [] imp_formula
         val all_rules = blastRule.safeRules cache claset [] all_formula
       in
         case (imp_rules, all_rules) of
             ([imp_rule], [all_rule]) =>
               pseudo_origin "imp" imp_rule andalso
               pseudo_origin "all" all_rule andalso
               (case #premises imp_rule of
                    [[Const ("*Goal*", []) $ Skolem (qname, []),
                      Skolem (pname, [])]] => pname <> qname
                  | _ => false) andalso
               (case #premises all_rule of
                    [[Const ("*Goal*", []) $ (_ $ Skolem (_, []))]] => true
                  | _ => false)
           | _ => false
       end)

val _ =
  test
    ("weak elimination warning is verbatim and the rule is skipped",
     fn () =>
       let
         val p = mk_var ("p", bool)
         val q = mk_var ("q", bool)
         val r = mk_var ("r", bool)
         val weak =
           GENL [p, q, r]
             (DISCH p (DISCH q (DISCH r (ASSUME r))))
         val output = ref ([] : string list)
         fun collect text = output := text :: !output
         val converted =
           Lib.with_flag (Feedback.WARNING_outstream, collect)
             (fn () =>
                blastRule.convertElim (blastRule.newCache ()) [] weak) ()
         val warning = String.concat (rev (!output))
         val message =
           "Ignoring weak elimination rule\n" ^ Parse.thm_to_string weak
         val expected =
           (!Feedback.WARNING_to_string) "blastRule" "convertElim"
             message
       in
         not (Option.isSome converted) andalso warning = expected
       end)

val _ =
  test
    ("too-flexible assertions never query elimination nets",
     fn () =>
       let
         val cache = blastRule.newCache ()
         val variable = Var (ref NONE)
         val negated = Const ("bool$~", []) $ variable
         val claset = clasetLib.the_claset ()
       in
         null (blastRule.safeRules cache claset [] variable) andalso
         null (blastRule.unsafeRules cache claset [] variable) andalso
         null (blastRule.safeRules cache claset [] negated) andalso
         blastRule.conversionCount cache = 0
       end)

val _ =
  test
    ("weight-zero stored rules precede goal-directed pseudo-rules",
     fn () =>
       let
         val p = mk_var ("p", bool)
         val reflexive = GEN p (DISCH p (ASSUME p))
         val claset =
           clasetLib.add_sintros [("imp_reflexive", reflexive)]
             clasetLib.empty_cs
         val formula =
           mkGoal (blastRule.fromGoalTerm (mk_imp (p, p)))
         val rules =
           blastRule.safeRules (blastRule.newCache ()) claset [] formula
       in
         case rules of
             {origin = blastRule.Stored _, ...} ::
             {origin = blastRule.ImpIntro, ...} :: _ => true
           | _ => false
       end)

val _ =
  test
    ("rule acquisition is per-node lazy and cached per formula",
     fn () =>
       let
         val cache = blastRule.newCache ()
         val formula =
           mkGoal
             (blastRule.fromGoalTerm
                (mk_conj (mk_var ("p", bool), mk_var ("q", bool))))
         val initial_count = blastRule.conversionCount cache
         val first =
           blastRule.safeRules cache (clasetLib.the_claset ()) [] formula
         val after_first = blastRule.conversionCount cache
         val second =
           blastRule.safeRules cache (clasetLib.the_claset ()) [] formula
       in
         initial_count = 0 andalso not (null first) andalso
         after_first > initial_count andalso
         blastRule.conversionCount cache = after_first andalso
         length first = length second
       end)

val _ =
  test
    ("duplicating elim replay uses REV_DUP_ELIM_RULE only",
     fn () =>
       let
         val cache = blastRule.newCache ()
         val elim = blastRule.convertElim cache [] CONJ_ELIM_THM
         val intro =
           blastRule.convertIntro cache [] boolTheory.AND_INTRO_THM
       in
         case elim of
             SOME converted =>
               Option.isSome (blastRule.replayTheorem converted true) andalso
               Option.isSome (blastRule.replayTheorem intro false) andalso
               Option.isSome (blastRule.replayTheorem intro true)
           | NONE => false
       end)

val _ =
  test
    ("initial blast formulae all receive the duplication flag",
     fn () =>
       let
         val p = Free "p"
         val q = Free "q"
         val branch = blastSearch.initBranch ([p, q], 3)
       in
         #lim branch = 3 andalso
         case #pairs branch of
             [(safe, [])] =>
               map (fn (formula, _) => formula) safe = [p, q] andalso
               List.all (fn (_, md) => md) safe
           | _ => false
       end)

val _ =
  test
    ("blast search closes propositional golden tautologies",
     fn () =>
       let
         val p = mk_var ("p", bool)
         val q = mk_var ("q", bool)
         val cs = clasetLib.the_claset ()
         val reflexive = ([], mk_imp (p, p))
         val projection =
           ([], mk_imp (mk_conj (p, q), p))
         val commutation =
           ([], mk_imp (mk_disj (p, q), mk_disj (q, p)))
       in
         Option.isSome (blastSearch.tryGoal cs 0 reflexive) andalso
         Option.isSome (blastSearch.tryGoal cs 0 projection) andalso
         Option.isSome (blastSearch.tryGoal cs 0 commutation)
       end)

val _ =
  test
    ("search records the complete six-step vocabulary",
     fn () =>
       let
         val p = mk_var ("p", bool)
         val q = mk_var ("q", bool)
         val x = mk_var ("x", bool)
         val y = mk_var ("y", bool)
         val pred = mk_var ("P", bool --> bool)
         val px = mk_comb (pred, x)
         val py = mk_comb (pred, y)
         val cs = clasetLib.the_claset ()
         val safe = blastSearch.tryGoal cs 0 ([], mk_imp (p, p))
         val subst =
           blastSearch.tryGoal cs 0 ([mk_eq (x, y), px], py)
         val contr =
           blastSearch.tryGoal cs 0 ([p, mk_neg p], q)
         val exists =
           blastSearch.tryGoal cs 1
             ([], mk_exists (x, mk_eq (x, x)))
         fun scripts (SOME proof) = #script proof
           | scripts NONE = []
         val all =
           scripts safe @ scripts subst @
           scripts contr @ scripts exists
         fun has predicate = List.exists predicate all
       in
         has (fn blastSearch.HypSubst => true | _ => false) andalso
         has (fn blastSearch.CloseAssume => true | _ => false) andalso
         has
           (fn blastSearch.CloseContradiction => true | _ => false)
           andalso
         has (fn blastSearch.SafeRule _ => true | _ => false) andalso
         has (fn blastSearch.DeferGoal => true | _ => false) andalso
         has (fn blastSearch.UnsafeRule _ => true | _ => false)
       end)

val _ =
  test
    ("unsafe depth and the deepening cap have exact accounting",
     fn () =>
       let
         val x = mk_var ("x", bool)
         val y = mk_var ("y", bool)
         val body = mk_conj (mk_eq (x, x), mk_eq (y, y))
         val goal = ([], mk_exists (x, mk_exists (y, body)))
         val cs = clasetLib.the_claset ()
         fun deepen limit =
           Lib.with_flag (blastSearch.depth_limit, limit)
             (fn () =>
                blastSearch.deepenGoal cs goal (fn proof => proof)) ()
       in
         !blastSearch.depth_limit = 20 andalso
         not (Option.isSome (blastSearch.tryGoal cs 0 goal)) andalso
         not (Option.isSome (blastSearch.tryGoal cs 1 goal)) andalso
         (case blastSearch.tryGoal cs 2 goal of
              SOME proof => #depth proof = 2
            | NONE => false) andalso
         not (Option.isSome (deepen 1)) andalso
         (case deepen 2 of
              SOME proof => #depth proof = 2
            | NONE => false)
       end)

val _ =
  test
    ("gamma retention is requeued at the back of its level",
     fn () =>
       let
         val h = Free "H"
         val first = (Free "A", false)
         val second = (Free "B", true)
       in
         blastSearch.requeueGamma (h, true) [first, second] true =
           [first, second, (h, true)] andalso
         blastSearch.requeueGamma (h, true) [first, second] false =
           [first, second]
       end)

val _ =
  test
    ("gamma requeue lets the next deferred formula run first",
     fn () =>
       let
         val x = mk_var ("x", bool)
         val b = mk_var ("b", bool)
         val p = mk_var ("P", bool --> bool)
         val q = mk_var ("Q", bool --> bool)
         val allp = mk_forall (x, mk_comb (p, x))
         val allq = mk_forall (x, mk_comb (q, x))
         val qb = mk_comb (q, b)
         val cs =
           clasetLib.add_elims
             [("allE", FORALL_ELIM_THM)] clasetLib.empty_cs
         fun isUnsafe (blastSearch.UnsafeRule _) = true
           | isUnsafe _ = false
       in
         not (Option.isSome
           (blastSearch.tryGoal cs 1 ([allp, allq], qb))) andalso
         (case blastSearch.tryGoal cs 2 ([allp, allq], qb) of
              SOME proof =>
                #depth proof = 2 andalso
                length (List.filter isUnsafe (#script proof)) = 2
            | NONE => false)
       end)

val _ =
  test
    ("recursive premises share a level and nonrecursive ones do not",
     fn () =>
       let
         val pattern = Const ("R", []) $ Var (ref NONE)
       in
         blastSearch.recursivePremise pattern
           [Const ("R", []) $ Free "a"] andalso
         not (blastSearch.recursivePremise pattern
           [Const ("S", []) $ Free "a"])
       end)

val _ =
  test
    ("prune fires without a next-branch clash and stops on a clash",
     fn () =>
       let
         val changed = ref NONE
         val barrier = ref NONE
         val unrelated = ref NONE
         val choices = [(8, 3), (5, 3), (2, 2)]
         val trail = [changed, ref NONE, barrier, ref NONE,
                      ref NONE, ref NONE, ref NONE, ref NONE]
         fun plan branches next_vars =
           blastSearch.prunePlan
             {branches = branches, next_vars = next_vars,
              trail_mark = 10, trail = trail,
              choices = choices}
         val indirect = ref (SOME (Var changed))
       in
         plan 3 [unrelated] = [(2, 2)] andalso
         plan 3 [changed] = choices andalso
         plan 3 [indirect] = choices andalso
         plan 3 [barrier] = [(5, 3), (2, 2)] andalso
         plan 1 [unrelated] = choices
       end)

val _ =
  test
    ("mayUndo and kill-all obey the crafted branch boundary",
     fn () =>
       let
         val old = [ref NONE]
         val newer = old @ [ref NONE]
         fun undo other updated vars =
           blastSearch.mayUndo
             {other_rules = other, updated = updated,
              old_vars = old, new_vars = vars}
       in
         blastSearch.instantiationPenalty 1 = 1 andalso
         blastSearch.instantiationPenalty 3 = 1 andalso
         blastSearch.instantiationPenalty 4 = 2 andalso
         blastSearch.instantiationPenalty 16 = 3 andalso
         undo true false newer andalso
         undo false true newer andalso
         undo false false old andalso
         not (undo false false newer) andalso
         blastSearch.killsAllAlternatives ~1 [[Free "child"]] andalso
         not (blastSearch.killsAllAlternatives ~1 []) andalso
         not (blastSearch.killsAllAlternatives 0 [[Free "child"]])
       end)

val _ =
  test
    ("mayUndo retries an unsafe alternative after PROOF_FAILED",
     fn () =>
       let
         val p = mk_var ("p", bool)
         val q = mk_var ("q", bool)
         val attempts = ref 0
         val cs =
           clasetLib.add_intros
             [("left", boolTheory.OR_INTRO_THM1),
              ("right", boolTheory.OR_INTRO_THM2)]
             clasetLib.empty_cs
         fun accept proof =
           (attempts := !attempts + 1;
            if !attempts = 1 then raise blastSearch.PROOF_FAILED
            else proof)
         val result =
           blastSearch.searchGoal cs 1
             ([p, q], mk_disj (p, q)) accept
       in
         !attempts = 2 andalso Option.isSome result
       end)

val _ =
  test
    ("a sole pure gamma inference is not retried after PROOF_FAILED",
     fn () =>
       let
         val x = mk_var ("x", bool)
         val b = mk_var ("b", bool)
         val pred = mk_var ("P", bool --> bool)
         val pb = mk_comb (pred, b)
         val attempts = ref 0
         val cs =
           clasetLib.add_intros
             [("exists", EXISTS_INTRO_THM)]
             clasetLib.empty_cs
         fun reject _ =
           (attempts := !attempts + 1;
            raise blastSearch.PROOF_FAILED)
         val result =
           blastSearch.searchGoal cs 1
             ([pb], mk_exists (x, mk_comb (pred, x))) reject
       in
         !attempts = 1 andalso not (Option.isSome result)
       end)

val _ =
  test
    ("PROOF_FAILED re-enters the final literal choice point",
     fn () =>
       let
         val p = mk_var ("p", bool)
         val attempts = ref 0
         fun accept proof =
           (attempts := !attempts + 1;
            if !attempts = 1 then raise blastSearch.PROOF_FAILED
            else proof)
         val result =
           blastSearch.searchGoal (clasetLib.the_claset ()) 0
             ([p, p], p) accept
       in
         !attempts = 2 andalso Option.isSome result
       end)

fun reconstructed cs depth goal =
  case blastReconstruct.searchGoal cs depth goal of
      SOME (_, ([], validation)) =>
        SOME (validation [])
    | _ => NONE

fun has_step predicate ({script, ...} : blastSearch.proof) =
  List.exists predicate script

val _ =
  test
    ("reconstruction goldens cover T2 and T3 under Tactical.VALID",
     fn () =>
       let
         val p = mk_var ("p", bool)
         val q = mk_var ("q", bool)
         val assume_goal = ([p], p)
         val contradiction_goal = ([p, mk_neg p], q)
       in
         Option.isSome
           (reconstructed clasetLib.empty_cs 0 assume_goal) andalso
         Option.isSome
           (reconstructed clasetLib.empty_cs 0 contradiction_goal)
       end)

val _ =
  test
    ("stored and pseudo safe rules reconstruct with prefix stripping",
     fn () =>
       let
         val p = mk_var ("p", bool)
         val q = mk_var ("q", bool)
         val x = mk_var ("x", bool)
         val cs =
           clasetLib.add_selims
             [("andE", CONJ_ELIM_THM)] clasetLib.empty_cs
         val stored = ([mk_conj (p, q)], p)
         val pseudo =
           ([], mk_forall (x, mk_imp (x, x)))
       in
         Option.isSome (reconstructed cs 0 stored) andalso
         Option.isSome
           (reconstructed clasetLib.empty_cs 0 pseudo)
       end)

val _ =
  test
    ("T5 and T6 reconstruct a witness fixed by a later T2 close",
     fn () =>
       let
         val x = mk_var ("x", bool)
         val p = mk_var ("P", bool --> bool)
         val a = mk_var ("a", bool)
         val pa = mk_comb (p, a)
         val goal = ([pa], mk_exists (x, mk_comb (p, x)))
         val cs =
           clasetLib.add_intros
             [("existsI", EXISTS_INTRO_THM)] clasetLib.empty_cs
       in
         case blastReconstruct.searchGoal cs 1 goal of
             SOME (proof, ([], validation)) =>
               has_step
                 (fn blastSearch.DeferGoal => true | _ => false)
                 proof andalso
               has_step
                 (fn blastSearch.UnsafeRule _ => true | _ => false)
                 proof andalso
               (ignore (validation []); true)
           | _ => false
       end)

val _ =
  test
    ("gamma duplication moves the repeated major behind old assumptions",
     fn () =>
       let
         val x = mk_var ("x", bool)
         val a = mk_var ("a", bool)
         val p = mk_var ("P", bool --> bool)
         val q = mk_var ("Q", bool --> bool)
         val allp = mk_forall (x, mk_comb (p, x))
         val allq = mk_forall (x, mk_comb (q, x))
         val goal = ([allp, allq], mk_comb (q, a))
         val cs =
           clasetLib.add_elims
             [("allE", FORALL_ELIM_THM)] clasetLib.empty_cs
       in
         case blastReconstruct.searchGoal cs 2 goal of
             SOME (proof, ([], validation)) =>
               has_step
                 (fn blastSearch.UnsafeRule {duplicate = true, ...} =>
                       true
                   | _ => false) proof andalso
               (ignore (validation []); true)
           | _ => false
       end)

val _ =
  test
    ("blast hyp-subst reorders affected assumptions before replay",
     fn () =>
       let
         val x = mk_var ("x", bool)
         val y = mk_var ("y", bool)
         val a = mk_var ("a", bool)
         val p = mk_var ("P", bool --> bool)
         val q = mk_var ("Q", bool --> bool)
         val unchanged =
           mk_conj (mk_comb (p, a), mk_comb (q, a))
         val affected =
           mk_conj (mk_comb (p, x), mk_comb (q, y))
         val goal =
           ([mk_eq (x, y), unchanged, affected], mk_comb (p, y))
         val cs =
           clasetLib.add_selims
             [("andE", CONJ_ELIM_THM)] clasetLib.empty_cs
       in
         case blastReconstruct.searchGoal cs 0 goal of
             SOME (proof, ([], validation)) =>
               has_step
                 (fn blastSearch.HypSubst => true | _ => false)
                 proof andalso
               (ignore (validation []); true)
           | _ => false
       end)

val _ =
  test
    ("hyp-subst affectedness preserves beta-redex branch order",
     fn () =>
       let
         val x = mk_var ("x", bool)
         val y = mk_var ("y", bool)
         val a = mk_var ("a", bool)
         val c = mk_var ("c", bool)
         val u = mk_var ("u", bool)
         val z = mk_var ("z", bool)
         val p = mk_var ("P", bool --> bool --> bool)
         fun pu left right =
           mk_comb (mk_comb (p, left), right)
         val constant_all = mk_forall (u, pu c u)
         val beta_assumption =
           mk_comb (mk_abs (z, constant_all), x)
         val affected_all = mk_forall (u, pu x u)
         val goal =
           ([mk_eq (x, y), beta_assumption, affected_all], pu c a)
         val cs =
           clasetLib.add_elims
             [("allE", FORALL_ELIM_THM)] clasetLib.empty_cs
       in
         Option.isSome (blastSearch.tryGoal cs 2 goal) andalso
         Option.isSome (reconstructed cs 2 goal)
       end)

val _ =
  test
    ("real reconstruction failure backtracks to a valid tableau rule",
     fn () =>
       let
         val p = mk_var ("p", bool)
         val q = mk_var ("q", bool)
         val r = mk_var ("r", bool)
         val bad = Drule.ADD_ASSUM r boolTheory.OR_INTRO_THM1
         val goal = ([p, q], mk_disj (p, q))
         val cs =
           clasetLib.add_intros
             [("good-right", boolTheory.OR_INTRO_THM2),
              ("bad-left", bad)] clasetLib.empty_cs
         val attempts = ref 0
         val messages = ref ([] : string list)
         val old_trace = Feedback.current_trace "blast"
         fun accept proof =
           (attempts := !attempts + 1;
            case blastReconstruct.reconstruct goal proof of
                SOME result => (proof, result)
              | NONE => raise blastSearch.PROOF_FAILED)
         val _ = Feedback.set_trace "blast" 1
         val result =
           Lib.with_flag (Feedback.MESG_outstream,
             fn message => messages := message :: !messages)
             (fn () => blastSearch.searchGoal cs 1 goal accept) ()
         val _ = Feedback.set_trace "blast" old_trace
         val traced =
           List.exists
             (String.isSubstring "PROOF FAILED for depth 1")
             (!messages)
       in
         !attempts = 2 andalso traced andalso
         case result of
             SOME (_, ([], validation)) =>
               (ignore (validation []); true)
           | _ => false
       end)

val _ =
  test
    ("a tableau with only an unreconstructible rule fails cleanly",
     fn () =>
       let
         val p = mk_var ("p", bool)
         val q = mk_var ("q", bool)
         val r = mk_var ("r", bool)
         val bad = Drule.ADD_ASSUM r boolTheory.OR_INTRO_THM1
         val goal = ([p], mk_disj (p, q))
         val cs =
           clasetLib.add_intros
             [("bad-left", bad)] clasetLib.empty_cs
       in
         Option.isSome (blastSearch.tryGoal cs 1 goal) andalso
         not (Option.isSome
           (blastReconstruct.searchGoal cs 1 goal))
       end)
