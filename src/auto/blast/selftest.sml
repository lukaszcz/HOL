open HolKernel boolSyntax testutils blastTerm
open clasetSeedTheory pred_setTheory

fun prove (proposition, tactic) =
  Tactical.TAC_PROOF (([], proposition), tactic)
  handle error =>
    (print ("failed local rule: " ^ Parse.term_to_string proposition ^ "\n");
     raise error)

val REWRITE_TAC = Rewrite.REWRITE_TAC
val PROVE_TAC = BasicProvers.PROVE_TAC

infix THEN
val op THEN = Tactical.THEN

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
         val old_trace = Feedback.current_trace "blast"
         fun collect text = output := text :: !output
         val _ = Feedback.set_trace "blast" 1
         val converted =
           Lib.with_flag (Feedback.WARNING_outstream, collect)
             (fn () =>
                blastRule.convertElim (blastRule.newCache ()) [] weak) ()
         val _ = Feedback.set_trace "blast" old_trace
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
         val alpha = Type.mk_vartype "'a"
         val x = mk_var ("x", alpha)
         val y = mk_var ("y", alpha)
         val pred = mk_var ("P", alpha --> bool)
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
    ("blast generation avoids hidden historical parameters",
     fn () =>
       let
         val z = mk_var ("hidden_z", bool)
         val pred = mk_var ("hidden_pred", bool --> bool)
         val quantified = mk_forall (z, mk_comb (pred, z))
         val node =
           clasetGoal.create
             {goals = [{params = [z], asl = [], w = quantified}],
              store = clasetMeta.empty, level = 0}
       in
         case seq.cases (clasetStep.blast_gen_step (node, 1)) of
             SOME ((record, next), _) =>
               (case (clasetStep.kind_of record,
                      clasetGoal.goals next) of
                    (clasetStep.Gen,
                     [{params = [old, fresh], asl = [], w}]) =>
                      Term.aconv old z andalso
                      not (Term.aconv fresh z) andalso
                      Term.aconv w (mk_comb (pred, fresh)) andalso
                      clasetMeta.is_eigen (clasetGoal.store next) fresh
                  | _ => false)
           | NONE => false
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
         val alpha = Type.mk_vartype "'a"
         val x = mk_var ("x", alpha)
         val y = mk_var ("y", alpha)
         val a = mk_var ("a", alpha)
         val p = mk_var ("P", alpha --> bool)
         val q = mk_var ("Q", alpha --> bool)
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
         val alpha = Type.mk_vartype "'a"
         val x = mk_var ("x", alpha)
         val y = mk_var ("y", alpha)
         val a = mk_var ("a", alpha)
         val c = mk_var ("c", alpha)
         val u = mk_var ("u", alpha)
         val z = mk_var ("z", alpha)
         val p = mk_var ("P", alpha --> alpha --> bool)
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
         val alpha = Type.mk_vartype "'a"
         val x = mk_var ("backtrack_x", alpha)
         val y = mk_var ("backtrack_y", alpha)
         val pred = mk_var ("backtrack_P", alpha --> bool)
         val p = mk_comb (pred, x)
         val py = mk_comb (pred, y)
         val q = mk_var ("backtrack_q", bool)
         val r = mk_var ("backtrack_r", bool)
         val bad = Drule.ADD_ASSUM r boolTheory.OR_INTRO_THM1
         val goal = ([mk_eq (x, y), p, q], mk_disj (py, q))
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
             SOME (proof, ([], validation)) =>
               has_step
                 (fn blastSearch.HypSubst => true | _ => false)
                 proof andalso
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

fun blast_solves tactic goal =
  case total (Tactical.VALID tactic) goal of
      SOME ([], validation) => (ignore (validation []); true)
    | _ => false

fun blast_fails tactic goal =
  not (Option.isSome (total (Tactical.VALID tactic) goal))

val _ =
  test
    ("public BLAST tactics solve golden goals under Tactical.VALID",
     fn () =>
       let
         val p = mk_var ("public_p", bool)
         val x = mk_var ("public_x", bool)
         val y = mk_var ("public_y", bool)
         val body = mk_conj (mk_eq (x, x), mk_eq (y, y))
         val nested =
           ([], mk_exists (x, mk_exists (y, body)))
       in
         blast_solves (tableauLib.BLAST_TAC [])
           ([], mk_imp (p, p)) andalso
         blast_fails (tableauLib.BLAST_DEPTH_TAC 1 []) nested andalso
         blast_solves (tableauLib.BLAST_DEPTH_TAC 2 []) nested
       end)

val _ =
  test
    ("public blast tactics read configuration when they run",
     fn () =>
       let
         val x = mk_var ("late_x", bool)
         val y = mk_var ("late_y", bool)
         val body = mk_conj (mk_eq (x, x), mk_eq (y, y))
         val goal = ([], mk_exists (x, mk_exists (y, body)))
         val theorem =
           Tactical.TAC_PROOF
             (goal, tableauLib.BLAST_DEPTH_TAC 2 [])
         val delayed_deepen = tableauLib.BLAST_TAC []
         val delayed_fixed = tableauLib.BLAST_DEPTH_TAC 0 []
         val scoped =
           clasetLib.add_sintros
             [("late-blast-rule", theorem)]
             (clasetLib.the_claset ())
         val depth_is_late =
           Lib.with_flag (tableauLib.depth_limit, 1)
             (fn () => blast_fails delayed_deepen goal) ()
         val claset_is_late =
           clasetLib.with_claset scoped
             (fn () => blast_solves delayed_fixed goal) ()
       in
         depth_is_late andalso claset_is_late
       end)

val _ =
  test
    ("public deepening explores bounds lazily",
     fn () =>
       case Int.maxInt of
           NONE => true
         | SOME maximum =>
             let
               val p = mk_var ("lazy_depth_p", bool)
             in
               Lib.with_flag (tableauLib.depth_limit, maximum)
                 (fn () =>
                    blast_solves (tableauLib.BLAST_TAC [])
                      ([], mk_imp (p, p))) ()
             end)

val _ =
  test
    ("plain extra lemmas are unsafe intros and markers are processed",
     fn () =>
       let
         val x = mk_var ("extra_x", bool)
         val y = mk_var ("extra_y", bool)
         val body = mk_conj (mk_eq (x, x), mk_eq (y, y))
         val conclusion = mk_exists (x, mk_exists (y, body))
         val goal = ([], conclusion)
         val theorem =
           Tactical.TAC_PROOF
             (goal, tableauLib.BLAST_DEPTH_TAC 2 [])
         val generic =
           [markerLib.Cong boolTheory.TRUTH,
            markerLib.Excl "not-a-blast-rule",
            markerLib.ExclSF "not-a-blast-fragment"]
       in
         blast_fails (tableauLib.BLAST_DEPTH_TAC 1 []) goal andalso
         blast_solves
           (tableauLib.BLAST_DEPTH_TAC 1 [theorem]) goal andalso
         blast_solves
           (tableauLib.BLAST_DEPTH_TAC 0
             [clasetLib.SIntro theorem]) goal andalso
         blast_solves (tableauLib.BLAST_TAC generic)
           ([], mk_imp (conclusion, conclusion))
       end)

val _ =
  test
    ("tryIt records full search and skips reconstruction",
     fn () =>
       let
         val p = mk_var ("debug_p", bool)
         val q = mk_var ("debug_q", bool)
         val r = mk_var ("debug_r", bool)
         val bad = Drule.ADD_ASSUM r boolTheory.OR_INTRO_THM1
         val goal = ([p], mk_disj (p, q))
         val rules =
           [clasetLib.Del "clasetSeed$DISJ_CINTRO_THM", bad]
         val debug = tableauLib.tryIt 1 rules goal
       in
         not (null (#fullTrace debug)) andalso
         (case #result debug of
              SOME proof => not (null (#script proof))
            | NONE => false) andalso
         blast_fails (tableauLib.BLAST_DEPTH_TAC 1 rules) goal
       end)

fun blast_trace_messages level tactic goal =
  let
    val old_trace = Feedback.current_trace "blast"
    val messages = ref ([] : string list)
    val _ = Feedback.set_trace "blast" level
    val result =
      Lib.with_flag (Feedback.MESG_outstream,
        fn message => messages := message :: !messages)
        (fn () => blast_solves tactic goal) ()
    val _ = Feedback.set_trace "blast" old_trace
  in
    (result, !messages)
  end

val _ =
  test
    ("blast trace levels report reconstruction failure stats and states",
     fn () =>
       let
         val p = mk_var ("trace_p", bool)
         val q = mk_var ("trace_q", bool)
         val r = mk_var ("trace_r", bool)
         val bad = Drule.ADD_ASSUM r boolTheory.OR_INTRO_THM1
         val goal = ([p, q], mk_disj (p, q))
         val rules =
           [clasetLib.Del "clasetSeed$DISJ_CINTRO_THM",
            boolTheory.OR_INTRO_THM2, bad]
         val (level1_ok, level1) =
           blast_trace_messages 1
             (tableauLib.BLAST_DEPTH_TAC 1 rules) goal
         val (level2_ok, level2) =
           blast_trace_messages 2
             (tableauLib.BLAST_DEPTH_TAC 1 rules) goal
         val (level3_ok, level3) =
           blast_trace_messages 3
             (tableauLib.BLAST_DEPTH_TAC 1 rules) goal
         fun contains text =
           List.exists (String.isSubstring text)
       in
         level1_ok andalso level2_ok andalso level3_ok andalso
         contains "PROOF FAILED" level1 andalso
         contains "Blast stats:" level2 andalso
         contains "Blast trace at depth" level3
       end)

val _ =
  test
    ("failed level-two stats include complete branch counters",
     fn () =>
       let
         val p = mk_var ("failed_stats_p", bool)
         val (solved, messages) =
           blast_trace_messages 2
             (tableauLib.BLAST_DEPTH_TAC 0 []) ([], p)
         fun contains text =
           List.exists (String.isSubstring text) messages
       in
         not solved andalso contains "Blast stats: no proof" andalso
         contains "branches created 1" andalso
         contains "branches closed 0" andalso
         contains "search " andalso contains "reconstruction "
       end)

val _ =
  test
    ("public blast calls do not leak claset theory or depth state",
     fn () =>
       let
         fun rule_names () =
           map (fn (_, (name, _)) => name)
             (clasetLib.rules_of (clasetLib.the_claset ()))
         val p = mk_var ("state_p", bool)
         val q = mk_var ("state_q", bool)
         val before_rules = rule_names ()
         val before_theory = Theory.current_theory ()
         val before_depth = !tableauLib.depth_limit
         val success =
           blast_solves (tableauLib.BLAST_TAC [])
             ([], mk_imp (p, p))
         val failure =
           blast_fails (tableauLib.BLAST_DEPTH_TAC 0 [])
             ([], mk_disj (p, q))
       in
         success andalso failure andalso
         before_rules = rule_names () andalso
         before_theory = Theory.current_theory () andalso
         before_depth = !tableauLib.depth_limit andalso
         before_depth = 20
       end)

(* -------------------------------------------------------------------------
 * TASK_23: Pelletier 1--46, 52 and 62 (BEGIN corpus).
 *
 * The formulae follow the corrected standard formulations used by
 * Isabelle/HOL's HOL/ex/Classical.thy.  In particular, 28 and 34 are the
 * amended versions, and 62 is the JAR 18 (1997), page 135 correction.
 * ------------------------------------------------------------------------- *)

val pelletier_corpus : (int * Term.term) list =
  [(1, “(P ==> Q) <=> (~Q ==> ~P)”),
   (2, “~~P <=> P”),
   (3, “~(P ==> Q) ==> (Q ==> P)”),
   (4, “(~P ==> Q) <=> (~Q ==> P)”),
   (5, “((P \/ Q) ==> (P \/ R)) ==> (P \/ (Q ==> R))”),
   (6, “P \/ ~P”),
   (7, “P \/ ~~~P”),
   (8, “((P ==> Q) ==> P) ==> P”),
   (9, “((P \/ Q) /\ (~P \/ Q) /\ (P \/ ~Q)) ==>
         ~(~P \/ ~Q)”),
   (10, “(Q ==> R) /\ (R ==> P /\ Q) /\ (P ==> Q \/ R) ==>
          (P <=> Q)”),
   (11, “P <=> P”),
   (12, “((P <=> Q) <=> R) <=> (P <=> (Q <=> R))”),
   (13, “(P \/ (Q /\ R)) <=> ((P \/ Q) /\ (P \/ R))”),
   (14, “(P <=> Q) <=> ((Q \/ ~P) /\ (~Q \/ P))”),
   (15, “(P ==> Q) <=> (~P \/ Q)”),
   (16, “(P ==> Q) \/ (Q ==> P)”),
   (17, “((P /\ (Q ==> R)) ==> ss) <=>
          ((~P \/ Q \/ ss) /\ (~P \/ ~R \/ ss))”),
   (18, “?y:'a. !x. P y ==> P x”),
   (19, “?x:'a. !y z. (P y ==> Q z) ==> (P x ==> Q x)”),
   (20, “(!x:'a y. ?z. !w. P x /\ Q y ==> R z /\ ss w) ==>
          ((?x y. P x /\ Q y) ==> ?z. R z)”),
   (21, “(?x:'a. P ==> Q x) /\ (?x. Q x ==> P) ==>
          ?x. P <=> Q x”),
   (22, “(!x:'a. P <=> Q x) ==> (P <=> !x. Q x)”),
   (23, “(!x:'a. P \/ Q x) <=> (P \/ !x. Q x)”),
   (24, “~(?x:'a. ss x /\ Q x) /\
          (!x. P x ==> Q x \/ R x) /\
          (~(?x. P x) ==> ?x. Q x) /\
          (!x. Q x \/ R x ==> ss x) ==>
          ?x. P x /\ R x”),
   (25, “(?x:'a. P x) /\
          (!x. L x ==> ~(M x /\ R x)) /\
          (!x. P x ==> M x /\ L x) /\
          ((!x. P x ==> Q x) \/ (?x. P x /\ R x)) ==>
          ?x. Q x /\ P x”),
   (26, “((?x:'a. p x) <=> (?x. q x)) /\
          (!x y. p x /\ q y ==> (r x <=> s y)) ==>
          ((!x. p x ==> r x) <=> (!x. q x ==> s x))”),
   (27, “(?x:'a. P x /\ ~Q x) /\
          (!x. P x ==> R x) /\
          (!x. M x /\ L x ==> P x) /\
          ((?x. R x /\ ~Q x) ==> !x. L x ==> ~R x) ==>
          !x. M x ==> ~L x”),
   (28, “(!x:'a. P x ==> !y. Q y) /\
          ((!x. Q x \/ R x) ==> ?x. Q x /\ ss x) /\
          ((?x. ss x) ==> !x. L x ==> M x) ==>
          !x. P x /\ L x ==> M x”),
   (29, “(?x:'a. ff x) /\ (?y. G y) ==>
          (((!x. ff x ==> H x) /\ (!y. G y ==> J y)) <=>
           (!x y. ff x /\ G y ==> H x /\ J y))”),
   (30, “(!x:'a. P x \/ Q x ==> ~R x) /\
          (!x. (Q x ==> ~ss x) ==> P x /\ R x) ==>
          !x. ss x”),
   (31, “~(?x:'a. P x /\ (Q x \/ R x)) /\
          (?x. L x /\ P x) /\
          (!x. ~R x ==> M x) ==>
          ?x. L x /\ M x”),
   (32, “(!x:'a. P x /\ (Q x \/ R x) ==> ss x) /\
          (!x. ss x /\ R x ==> L x) /\
          (!x. M x ==> R x) ==>
          !x. P x /\ M x ==> L x”),
   (33, “(!x:'a. P a /\ (P x ==> P b) ==> P c) <=>
          (!x. (~P a \/ P x \/ P c) /\
               (~P a \/ ~P b \/ P c))”),
   (34, “((?x:'a. !y. p x <=> p y) <=>
           ((?x. q x) <=> (!y. p y))) <=>
          ((?x. !y. q x <=> q y) <=>
           ((?x. p x) <=> (!y. q y)))”),
   (35, “?x:'a y. P x y ==> !u v. P u v”),
   (36, “(!x:'a. ?y. J x y) /\
          (!x. ?y. G x y) /\
          (!x y. J x y \/ G x y ==>
                 !z. J y z \/ G y z ==> H x z) ==>
          !x. ?y. H x y”),
   (37, “(!z:'a. ?w. !x. ?y.
             (P x z ==> P y w) /\ P y z /\
             (P y w ==> ?u. Q u w)) /\
          (!x z. ~P x z ==> ?y. Q y z) /\
          ((?x y. Q x y) ==> !x. R x x) ==>
          !x. ?y. R x y”),
   (38, “(!x:'a. p a /\ (p x ==> ?y. p y /\ r x y) ==>
                   ?z w. p z /\ r x w /\ r w z) <=>
          (!x. (~p a \/ p x \/
                 (?z w. p z /\ r x w /\ r w z)) /\
               (~p a \/ ~(?y. p y /\ r x y) \/
                 (?z w. p z /\ r x w /\ r w z)))”),
   (39, “~(?x:'a. !y. ff y x <=> ~ff y y)”),
   (40, “(?y:'a. !x. ff x y <=> ff x x) ==>
          ~(!x. ?y. !z. ff z y <=> ~ff z x)”),
   (41, “(!z:'a. ?y. !x. f x y <=> (f x z /\ ~f x x)) ==>
          ~(?z. !x. f x z)”),
   (42, “~(?y:'a. !x. p x y <=> ~(?z. p x z /\ p z x))”),
   (43, “(!x:'a y. q x y <=> (!z. p z x <=> p z y)) ==>
          (!x y. q x y <=> q y x)”),
   (44, “(!x:'a. f x ==>
                 ?y. g y /\ h x y /\ (?z. g z /\ ~h x z)) /\
          (?x. j x /\ (!y. g y ==> h x y)) ==>
          ?x. j x /\ ~f x”),
   (45, “(!x:'a. f x /\
                 (!y. g y /\ h x y ==> j x y) ==>
                 !y. g y /\ h x y ==> k y) /\
          ~(?y. l y /\ k y) /\
          (?x. f x /\ (!y. h x y ==> l y) /\
               (!y. g y /\ h x y ==> j x y)) ==>
          ?x. f x /\ ~(?y. g y /\ h x y)”),
   (46, “(!x:'a. f x /\
                 (!y. f y /\ h y x ==> g y) ==> g x) /\
          ((?x. f x /\ ~g x) ==>
           ?x. f x /\ ~g x /\
               (!y. f y /\ ~g y ==> j x y)) /\
          (!x y. f x /\ f y /\ h x y ==> ~j y x) ==>
          !x. f x ==> g x”),
   (52, “(?z w:'a. !x y. P x y <=> (x = z) /\ (y = w)) ==>
          ?w. !y. (?z. !x. P x y <=> (x = z)) <=> (y = w)”),
   (62, “(!x:'a. p a /\ (p x ==> p (f x)) ==> p (f (f x))) <=>
          (!x. (~p a \/ p x \/ p (f (f x))) /\
               (~p a \/ ~p (f x) \/ p (f (f x))))”)]

(* TASK_23: Pelletier 1--46, 52 and 62 (END corpus). *)

val pelletier_budget = Time.fromSeconds 30
val pelletier_solved = ref 0

fun run_pelletier (number, proposition) =
  let
    val name = "BLAST_TAC Pelletier " ^ Int.toString number
    val _ = tprint name
    val start = Time.now ()
    val timed_out = ref false
    val solved =
      Timeout.apply pelletier_budget
        (fn () =>
          case Tactical.VALID (tableauLib.BLAST_TAC [])
                 ([], proposition) of
              ([], validation) => (ignore (validation []); true)
            | _ => false) ()
      handle Timeout.TIMEOUT _ => (timed_out := true; false)
           | HOL_ERR _ => false
    val elapsed = Time.- (Time.now (), start)
  in
    if solved andalso Time.< (elapsed, pelletier_budget) then
      (pelletier_solved := !pelletier_solved + 1; OK ())
    else if !timed_out orelse not (Time.< (elapsed, pelletier_budget)) then
      die (name ^ " exceeded its 30 second budget")
    else
      die (name ^ " did not solve the goal")
  end

val _ = List.app run_pelletier pelletier_corpus

val _ =
  test
    ("BLAST_TAC Pelletier solved-goal count",
     fn () =>
       !pelletier_solved = length pelletier_corpus andalso
       !pelletier_solved = 48)

(* -------------------------------------------------------------------------
 * TASK_24: Table-1 depths, set problems, Halting II, and robustness.
 * ------------------------------------------------------------------------- *)

val blast_regression_budget = Time.fromSeconds 30

fun timed_blast name budget tactic goal =
  let
    val _ = tprint name
    val started = Time.now ()
    val timed_out = ref false
    val solved =
      Timeout.apply budget
        (fn () => blast_solves tactic goal) ()
      handle Timeout.TIMEOUT _ => (timed_out := true; false)
           | HOL_ERR _ => false
    val elapsed = Time.- (Time.now (), started)
  in
    if solved andalso Time.< (elapsed, budget) then OK ()
    else if !timed_out orelse not (Time.< (elapsed, budget)) then
      die (name ^ " exceeded its time budget")
    else
      die (name ^ " did not solve the goal")
  end

fun timed_blast_result name budget tactic goal =
  let
    val _ = tprint name
    val started = Time.now ()
    val solved =
      Timeout.apply budget
        (fn () =>
          case total tactic goal of
              SOME ([], _) => true
            | _ => false) ()
      handle Timeout.TIMEOUT _ => false
  in
    if solved andalso Time.< (Time.- (Time.now (), started), budget) then
      OK ()
    else
      die (name ^ " did not return a proof within its time budget")
  end

fun pelletier_problem number =
  case List.find (fn (candidate, _) => candidate = number)
         pelletier_corpus of
      SOME (_, proposition) => proposition
    | NONE => raise Fail "missing Pelletier problem"

val table1_depths =
  [(24, 4), (26, 3), (28, 3), (34, 7), (38, 4), (43, 5),
   (46, 7), (52, 7), (62, 1)]

val table1_solved = ref 0

fun run_table1_depth (number, depth) =
  let
    val name =
      "BLAST_DEPTH_TAC Pelletier " ^ Int.toString number ^ " at " ^
      Int.toString depth
    val proposition = pelletier_problem number
    val _ =
      timed_blast name blast_regression_budget
        (tableauLib.BLAST_DEPTH_TAC depth []) ([], proposition)
  in
    table1_solved := !table1_solved + 1
  end

val _ = List.app run_table1_depth table1_depths

val _ =
  test
    ("Table-1 published-depth solved-goal count",
     fn () =>
       !table1_solved = length table1_depths andalso
       !table1_solved = 9)

val _ =
  test
    ("Table-1 depth accounting rejects shallower bounds",
     fn () =>
       blast_fails (tableauLib.BLAST_DEPTH_TAC 2 [])
         ([], pelletier_problem 26) andalso
       blast_fails (tableauLib.BLAST_DEPTH_TAC 2 [])
         ([], pelletier_problem 28))

(* These are the classical set rules used only by this selftest.  In
   particular there is deliberately no rule for ~(x IN UNIV): the blast
   paper reports that it greatly enlarges the Singleton search space.  A
   Phase-8 seed change must preserve these regressions when adding one. *)

val SET_EQUAL_I =
  prove
    (“!A B:'a set. A SUBSET B ==> B SUBSET A ==> (A = B)”,
     PROVE_TAC [SUBSET_ANTISYM])

val SET_SUBSET_I =
  prove
    (“!A B:'a set. (!x. x IN A ==> x IN B) ==> A SUBSET B”,
     REWRITE_TAC [SUBSET_DEF])

val SET_SUBSET_D =
  prove
    (“!A B:'a set. !x. A SUBSET B ==> x IN A ==> x IN B”,
     REWRITE_TAC [SUBSET_DEF] THEN PROVE_TAC [])

val SET_SUBSET_CE =
  prove
    (“!A B:'a set. !x R. A SUBSET B ==>
       (x NOTIN A ==> R) ==> (x IN B ==> R) ==> R”,
     REWRITE_TAC [SUBSET_DEF] THEN PROVE_TAC [])

val SET_INTER_I =
  prove
    (“!x A B:'a set. x IN A ==> x IN B ==> x IN A INTER B”,
     REWRITE_TAC [IN_INTER] THEN PROVE_TAC [])

val SET_INTER_E =
  prove
    (“!x A B:'a set. !R. x IN A INTER B ==>
       (x IN A ==> x IN B ==> R) ==> R”,
     REWRITE_TAC [IN_INTER] THEN PROVE_TAC [])

val SET_UNION_CI =
  prove
    (“!x A B:'a set. (x NOTIN B ==> x IN A) ==> x IN A UNION B”,
     REWRITE_TAC [IN_UNION] THEN PROVE_TAC [])

val SET_UNION_E =
  prove
    (“!x A B:'a set. !R. x IN A UNION B ==>
       (x IN A ==> R) ==> (x IN B ==> R) ==> R”,
     REWRITE_TAC [IN_UNION] THEN PROVE_TAC [])

val SET_BIGUNION_I =
  prove
    (“!x (C:'a set set) A. x IN A ==> A IN C ==>
       x IN BIGUNION C”,
     REWRITE_TAC [IN_BIGUNION] THEN PROVE_TAC [])

val SET_BIGUNION_E =
  prove
    (“!x (C:'a set set) R. x IN BIGUNION C ==>
       (!A. x IN A ==> A IN C ==> R) ==> R”,
     REWRITE_TAC [IN_BIGUNION] THEN PROVE_TAC [])

val SET_BIGUNION_IMAGE_I =
  prove
    (“!y (f:'a -> 'b set) C x. x IN C ==> y IN f x ==>
       y IN BIGUNION (IMAGE f C)”,
     REWRITE_TAC [IN_BIGUNION_IMAGE] THEN PROVE_TAC [])

val SET_BIGUNION_IMAGE_E =
  prove
    (“!y (f:'a -> 'b set) C R. y IN BIGUNION (IMAGE f C) ==>
       (!x. x IN C ==> y IN f x ==> R) ==> R”,
     REWRITE_TAC [IN_BIGUNION_IMAGE] THEN PROVE_TAC [])

val SET_BIGINTER_IMAGE_I =
  prove
    (“!y (f:'a -> 'b set) C. (!x. x IN C ==> y IN f x) ==>
       y IN BIGINTER (IMAGE f C)”,
     REWRITE_TAC [IN_BIGINTER_IMAGE])

val SET_BIGINTER_IMAGE_D =
  prove
    (“!y (f:'a -> 'b set) C x. y IN BIGINTER (IMAGE f C) ==>
       x IN C ==> y IN f x”,
     REWRITE_TAC [IN_BIGINTER_IMAGE] THEN PROVE_TAC [])

val SET_BIGINTER_IMAGE_E =
  prove
    (“!y (f:'a -> 'b set) C x R.
       y IN BIGINTER (IMAGE f C) ==>
       (x NOTIN C ==> R) ==> (y IN f x ==> R) ==> R”,
     REWRITE_TAC [IN_BIGINTER_IMAGE] THEN PROVE_TAC [])

val SET_SUBSET_SINGLETON_I =
  prove
    (“!ss:'a set set.
       (!x y. x IN ss ==> y IN ss ==> (x = y)) ==>
       ?z. ss SUBSET {z}”,
     PROVE_TAC [MEMBER_NOT_EMPTY, SUBSET_DEF, IN_SING])

val SET_SINGLETON_I =
  prove
    (“!x:'a. x IN {x}”,
     REWRITE_TAC [IN_SING])

val SET_SINGLETON_E =
  prove
    (“!x y:'a. !R. x IN {y} ==> (x = y ==> R) ==> R”,
     REWRITE_TAC [IN_SING] THEN PROVE_TAC [])

val blast_set_common_rules =
  [clasetLib.SIntro SET_EQUAL_I,
   clasetLib.SIntro SET_SUBSET_I,
   clasetLib.Dest SET_SUBSET_D,
   clasetLib.Elim SET_SUBSET_CE,
   clasetLib.SIntro SET_INTER_I,
   clasetLib.SElim SET_INTER_E,
   clasetLib.SIntro SET_UNION_CI,
   clasetLib.SElim SET_UNION_E,
   clasetLib.SIntro SET_SINGLETON_I,
   clasetLib.SDest SET_SINGLETON_E]

val blast_union_image_rules =
  blast_set_common_rules @
  [clasetLib.Intro SET_BIGUNION_IMAGE_I,
   clasetLib.SElim SET_BIGUNION_IMAGE_E]

val blast_inter_image_rules =
  blast_set_common_rules @
  [clasetLib.SIntro SET_BIGINTER_IMAGE_I,
   clasetLib.Dest SET_BIGINTER_IMAGE_D,
   clasetLib.Elim SET_BIGINTER_IMAGE_E]

val blast_singleton_rules =
  blast_set_common_rules @
  [clasetLib.SIntro SET_SUBSET_SINGLETON_I,
   clasetLib.Intro SET_BIGUNION_I,
   clasetLib.SElim SET_BIGUNION_E]

fun set_rules "Union-image" = blast_union_image_rules
  | set_rules "Inter-image" = blast_inter_image_rules
  | set_rules _ = blast_singleton_rules

val set_table1_problems : (string * int * Term.term) list =
  [("Union-image", 3,
    “BIGUNION (IMAGE (\x. f x UNION g x) C) =
     BIGUNION (IMAGE f C) UNION BIGUNION (IMAGE g C)”),
   ("Inter-image", 3,
    “BIGINTER (IMAGE (\x. f x INTER g x) C) =
     BIGINTER (IMAGE f C) INTER BIGINTER (IMAGE g C)”),
   ("Singleton I", 4,
    “(!x. x IN (ss:'a set set) ==>
          !y. y IN ss ==> x SUBSET y) ==>
     ?z. ss SUBSET {z}”),
   ("Singleton II", 4,
    “(!x. x IN (ss:'a set set) ==> BIGUNION ss SUBSET x) ==>
     ?z. ss SUBSET {z}”)]

val set_table1_solved = ref 0

fun run_set_table1 (name, depth, proposition) =
  let
    val _ =
      timed_blast ("BLAST_DEPTH_TAC " ^ name)
        blast_regression_budget
        (tableauLib.BLAST_DEPTH_TAC depth (set_rules name))
        ([], proposition)
  in
    set_table1_solved := !set_table1_solved + 1
  end

val _ = List.app run_set_table1 set_table1_problems

val _ =
  test
    ("Table-1 set-problem solved-goal count",
     fn () =>
       !set_table1_solved = length set_table1_problems andalso
       !set_table1_solved = 4)

fun selftest_level () =
  case Option.mapPartial Int.fromString
         (OS.Process.getEnv "HOLSELFTESTLEVEL") of
      SOME level => level
    | NONE => 1

val halting_ii =
  “(((?x:'a. A x /\ (!y. C y ==> !z. D x y z)) ==>
      (?w. C w /\ (!y. C y ==> !z. D w y z))) /\
    (!w. C w /\ (!u. C u ==> !v. D w u v) ==>
      !y z.
        (C y /\ P y z ==> Q w y z /\ OO w g) /\
        (C y /\ ~P y z ==> Q w y z /\ OO w b)) /\
    ((?w. C w /\
       (!y. (C y /\ P y y ==> Q w y y /\ OO w g) /\
            (C y /\ ~P y y ==> Q w y y /\ OO w b))) ==>
     (?v. C v /\
       (!y. (C y /\ P y y ==> P v y /\ OO v g) /\
            (C y /\ ~P y y ==> P v y /\ OO v b))))) ==>
   (((?v. C v /\
       (!y. (C y /\ P y y ==> P v y /\ OO v g) /\
            (C y /\ ~P y y ==> P v y /\ OO v b))) ==>
     (?u. C u /\
       (!y. (C y /\ P y y ==> ~P u y) /\
            (C y /\ ~P y y ==> P u y /\ OO u b)))) ==>
    ~(?x. A x /\ (!y. C y ==> !z. D x y z)))”

val halting_solved = ref 0

val _ =
  if selftest_level () >= 2 then
    (test
       ("Halting-II translation matches its preprocessing theorem",
        fn () =>
          Term.aconv halting_ii
            (concl (Drule.SPEC_ALL clasetSeedTheory.HALTING_II_THM)));
     timed_blast_result "BLAST_DEPTH_TAC Halting II"
       (Time.fromSeconds 120)
       (tableauLib.BLAST_DEPTH_TAC 7 [])
       ([], halting_ii);
     halting_solved := 1;
     test
       ("Halting-II solved-goal count",
        fn () => !halting_solved = 1))
  else ()

val _ =
  test
    ("higher-order unification requirement fails cleanly",
     fn () =>
       let
         val goal = ([], “?f:'a -> 'a. f x = x”)
         val started = Time.now ()
         val failed =
           Timeout.apply blast_regression_budget
             (fn () =>
                blast_fails
                  (tableauLib.BLAST_DEPTH_TAC 2 []) goal) ()
           handle Timeout.TIMEOUT _ => false
       in
         failed andalso
         Time.< (Time.- (Time.now (), started),
                 blast_regression_budget)
       end)

val _ =
  test
    ("weak [elim] marker warns and is skipped without aborting",
     fn () =>
       let
         val p = mk_var ("marked_weak_p", bool)
         val q = mk_var ("marked_weak_q", bool)
         val r = mk_var ("marked_weak_r", bool)
         val weak =
           GENL [p, q, r]
             (DISCH p (DISCH q (DISCH r (ASSUME r))))
         val output = ref ([] : string list)
         val old_trace = Feedback.current_trace "blast"
         val started = Time.now ()
         fun collect text = output := text :: !output
         val _ = Feedback.set_trace "blast" 1
         val (solved, skipped) =
           Lib.with_flag (Feedback.WARNING_outstream, collect)
             (fn () =>
                let
                  val (tagged, leftovers) =
                    clasetLib.process_claset_tags
                      [clasetLib.Elim weak] clasetLib.empty_cs
                  val converted =
                    blastRule.convertElim (blastRule.newCache ())
                      [] weak
                  val solved =
                    blast_solves
                      (tableauLib.BLAST_DEPTH_TAC 0
                         [clasetLib.Elim weak])
                      ([p, mk_imp (p, q)], q)
                in
                  (solved, null leftovers andalso
                           length (clasetLib.rules_of tagged) = 1 andalso
                           not (Option.isSome converted))
                end) ()
         val _ = Feedback.set_trace "blast" old_trace
         val warning = String.concat (rev (!output))
       in
         solved andalso skipped andalso
         String.isSubstring "Ignoring weak elimination rule" warning andalso
         Time.< (Time.- (Time.now (), started),
                 blast_regression_budget)
       end)
