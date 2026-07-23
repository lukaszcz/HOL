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
    ("measured clearTo checkpoints every normal rollback item",
     fn () =>
       let
         val state = newState ()
         val x = ref NONE
         val y = ref NONE
         val polls = ref 0
         val _ = unify state ([], Var x, Free "a")
         val _ = unify state ([], Var y, Free "b")
         val _ =
           clearToMeasured (fn () => polls := !polls + 1) state 0
       in
         !polls = 2 andalso unassigned x andalso unassigned y andalso
         trailSize state = 0
       end)

val _ =
  test
    ("interrupted measured clearTo finishes emergency rollback",
     fn () =>
       let
         exception CleanupStop of int ref
         val sentinel = ref 29
         val state = newState ()
         val x = ref NONE
         val y = ref NONE
         val z = ref NONE
         val polls = ref 0
         val _ = unify state ([], Var x, Free "a")
         val _ = unify state ([], Var y, Free "b")
         val _ = unify state ([], Var z, Free "c")
         fun checkpoint () =
           (polls := !polls + 1;
            if !polls = 2 then raise CleanupStop sentinel else ())
       in
         (clearToMeasured checkpoint state 0; false)
         handle CleanupStop actual =>
                  actual = sentinel andalso !polls = 2 andalso
                  unassigned x andalso unassigned y andalso
                  unassigned z andalso trailSize state = 0
              | _ => false
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
    ("goal translation separates typed names and reuses exact metadata",
     fn () =>
       let
         val alpha = Type.mk_vartype "'metadata_a"
         val bool_x = mk_var ("metadata_x", bool)
         val alpha_x = mk_var ("metadata_x", alpha)
         val proposition =
           mk_conj
             (mk_eq (bool_x, bool_x), mk_eq (alpha_x, alpha_x))
       in
         case blastRule.fromGoalTerm proposition of
             (Const ("bool$/\\", []) $
                ((Const ("min$=", [Const ("min$bool", [])]) $
                    Skolem (bool_left, [])) $
                   Skolem (bool_right, []))) $
               ((Const ("min$=", [Free "'metadata_a"]) $
                   Skolem (alpha_left, [])) $
                  Skolem (alpha_right, [])) =>
               bool_left = bool_right andalso
               alpha_left = alpha_right andalso
               bool_left <> alpha_left
           | _ => false
       end)

fun polymorphic_pair term =
  case term of
      (Const ("bool$/\\", []) $
         ((Const ("min$=", [Var left_type]) $ Var left_first) $
            Var left_second)) $
        ((Const ("min$=", [Var right_type]) $ Var right_first) $
           Var right_second) =>
          SOME
            (left_type, left_first, left_second,
             right_type, right_first, right_second)
    | _ => NONE

fun polymorphic_equality term =
  case term of
      (Const ("min$=", [Var equality_type]) $ Var first) $ Var second =>
        SOME (equality_type, first, second)
    | _ => NONE

val _ =
  test
    ("rule translation shares repeated types and typed term variables",
     fn () =>
       let
         val alpha = Type.mk_vartype "'metadata_rule_a"
         val beta = Type.mk_vartype "'metadata_rule_b"
         val alpha_x = mk_var ("metadata_rule_x", alpha)
         val beta_x = mk_var ("metadata_rule_x", beta)
         val proposition =
           mk_conj
             (mk_eq (alpha_x, alpha_x), mk_eq (beta_x, beta_x))
         val theorem =
           GENL [alpha_x, beta_x]
             (DISCH proposition (ASSUME proposition))
         val converted =
           blastRule.convertIntro (blastRule.newCache ()) [] theorem
         val pattern = polymorphic_pair (rand (#pattern converted))
         val premise =
           case #premises converted of
               [[left], [right]] =>
                 (case (polymorphic_equality (rand left),
                        polymorphic_equality (rand right)) of
                      (SOME (alpha_type, alpha_first, alpha_second),
                       SOME (beta_type, beta_first, beta_second)) =>
                        SOME
                          (alpha_type, alpha_first, alpha_second,
                           beta_type, beta_first, beta_second)
                    | _ => NONE)
             | _ => NONE
       in
         case (pattern, premise) of
             (SOME (alpha_type, alpha_first, alpha_second,
                    beta_type, beta_first, beta_second),
              SOME (alpha_type', alpha_first', alpha_second',
                    beta_type', beta_first', beta_second')) =>
               alpha_type = alpha_type' andalso
               beta_type = beta_type' andalso
               alpha_type <> beta_type andalso
               alpha_first = alpha_second andalso
               beta_first = beta_second andalso
               alpha_first = alpha_first' andalso
               alpha_second = alpha_second' andalso
               beta_first = beta_first' andalso
               beta_second = beta_second' andalso
               alpha_first <> beta_first
           | _ => false
       end)

val _ =
  test
    ("bound lookup preserves alpha-equivalence and de Bruijn scope",
     fn () =>
       let
         fun quantified (left_name, right_name) =
           let
             val left = mk_var (left_name, bool)
             val right = mk_var (right_name, bool)
           in
             mk_forall
               (left, mk_forall (right, mk_eq (right, left)))
           end
         val first =
           blastRule.fromGoalTerm (quantified ("left", "right"))
         val renamed =
           blastRule.fromGoalTerm (quantified ("x", "y"))
       in
         aconv (first, renamed) andalso
         case first of
             Const ("bool$!", _) $
               Abs (_, Const ("bool$!", _) $
                 Abs (_, (Const ("min$=", _) $ Bound 0) $ Bound 1)) =>
               true
           | _ => false
       end)

val _ =
  test
    ("separate translations allocate fresh names but reuse local names",
     fn () =>
       let
         val x = mk_var ("metadata_fresh_x", bool)
         fun names () =
           case blastRule.fromGoalTerm (mk_eq (x, x)) of
               (Const ("min$=", _) $ Skolem (left, [])) $
                 Skolem (right, []) => SOME (left, right)
             | _ => NONE
       in
         case (names (), names ()) of
             (SOME (first_left, first_right),
              SOME (second_left, second_right)) =>
               first_left = first_right andalso
               second_left = second_right andalso
               first_left <> second_left
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
         #hidden_assumptions conjunction = [NONE, NONE] andalso
         #hidden_assumptions disjunction = [NONE] andalso
         #hidden_assumptions exists = [NONE] andalso
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
         val p = mk_var ("hidden_golden_p", bool)
         val q = mk_var ("hidden_golden_q", bool)
         val r = mk_var ("hidden_golden_r", bool)
         val hidden_theorem =
           prove
             (list_mk_forall
                ([p, q, r],
                 mk_imp
                   (mk_conj (mk_neg p, q),
                    mk_imp (mk_imp (q, mk_imp (mk_neg r, p)), r))),
              PROVE_TAC [boolTheory.EXCLUDED_MIDDLE])
         val hidden = blastRule.convertElim cache [] hidden_theorem
       in
         case (conjunction, disjunction, exists, iff, hidden) of
             (SOME conjunction', SOME disjunction', SOME exists',
              SOME iff', SOME hidden') =>
               stored_elim conjunction' andalso
               group_lengths conjunction' = [2] andalso
               group_lengths disjunction' = [1, 1] andalso
               group_lengths exists' = [1] andalso
               group_lengths iff' = [2, 2] andalso
               #hidden_assumptions conjunction' = [NONE] andalso
               #hidden_assumptions disjunction' = [NONE, NONE] andalso
               #hidden_assumptions exists' = [NONE] andalso
               #hidden_assumptions iff' = [NONE, NONE] andalso
               #hidden_assumptions hidden' = [SOME 1] andalso
               is_head "bool$/\\" (#pattern conjunction') andalso
               is_head "bool$\\/" (#pattern disjunction') andalso
               is_head "bool$?" (#pattern exists') andalso
               is_head "min$=" (#pattern iff') andalso
               (case #premises exists' of
                    [[formula]] => has_skolem formula
                  | _ => false) andalso
               (case #premises hidden' of
                    [[goal_formula, visible]] =>
                      isGoal goal_formula andalso
                      not (isGoal visible)
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
               #hidden_assumptions imp_rule = [NONE] andalso
               #hidden_assumptions all_rule = [NONE] andalso
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

fun rule_vars ({pattern, premises, ...} : blastRule.tableau_rule) =
  add_terms_vars (List.concat premises, add_term_vars (pattern, []))

val _ =
  test
    ("cached rule templates survive destructive unification",
     fn () =>
       let
         val cache = blastRule.newCache ()
         val claset = clasetLib.the_claset ()
         val formula =
           mkGoal
             (blastRule.fromGoalTerm
                (mk_conj (mk_var ("p", bool), mk_var ("q", bool))))
         val initial_count = blastRule.conversionCount cache
         val first =
           blastRule.safeRules cache claset [] formula
         val after_first = blastRule.conversionCount cache
         val (first_rule, first_vars) =
           case first of
               rule :: _ => (rule, rule_vars rule)
             | [] => raise Fail "no conjunction rule"
         val instantiated =
           unify (newState ())
             (first_vars, #pattern first_rule, formula)
         val contaminated =
           List.exists (fn variable => not (unassigned variable))
             first_vars
         val second = blastRule.safeRules cache claset [] formula
         val after_second = blastRule.conversionCount cache
         val second_vars =
           case second of
               rule :: _ => rule_vars rule
             | [] => []
       in
         initial_count = 0 andalso not (null first) andalso
         after_first > initial_count andalso
         after_second = after_first andalso
         blastRule.hitCount cache = 1 andalso
         length first = length second andalso
         instantiated andalso contaminated andalso
         not (null first_vars) andalso
         List.all unassigned second_vars andalso
         List.all
           (fn variable => not (mem_var (variable, second_vars)))
           first_vars
       end)

fun skolem_dependencies term =
  case term of
      Const (_, args) => List.concat (map skolem_dependencies args)
    | Skolem (_, arguments) =>
        arguments @
        List.concat
          (map
             (fn variable =>
                case !variable of
                    NONE => []
                  | SOME value => skolem_dependencies value)
             arguments)
    | Var variable =>
        (case !variable of
             NONE => []
           | SOME value => skolem_dependencies value)
    | Abs (_, body) => skolem_dependencies body
    | left $ right =>
        skolem_dependencies left @ skolem_dependencies right
    | _ => []

fun rule_skolem_dependencies
      ({pattern, premises, ...} : blastRule.tableau_rule) =
  List.concat
    (map skolem_dependencies (pattern :: List.concat premises))

val _ =
  test
    ("cached rules freshen locals but preserve branch dependencies",
     fn () =>
       let
         val cache = blastRule.newCache ()
         val branch = ref NONE
         val alpha = Type.mk_vartype "'cache_a"
         val x = mk_var ("cache_x", alpha)
         val y = mk_var ("cache_y", alpha)
         val pred = mk_var ("cache_P", alpha --> bool)
         val universal = mk_forall (y, mk_comb (pred, y))
         val specializing =
           GENL [pred, x]
             (DISCH universal (SPEC x (ASSUME universal)))
         val formula =
           mkGoal (blastRule.fromGoalTerm (mk_comb (pred, x)))
         val claset =
           clasetLib.add_sintros [("cache_specializing", specializing)]
             clasetLib.empty_cs
         val first =
           case blastRule.safeRules cache claset [branch] formula of
               [rule] => rule
             | _ => raise Fail "expected one specializing rule"
         val second =
           case blastRule.safeRules cache claset [branch] formula of
               [rule] => rule
             | _ => raise Fail "expected cached specializing rule"
         val first_locals =
           List.filter (fn variable => variable <> branch)
             (rule_vars first)
         val second_locals =
           List.filter (fn variable => variable <> branch)
             (rule_vars second)
         val first_dependencies = rule_skolem_dependencies first
         val second_dependencies = rule_skolem_dependencies second
       in
         not (null first_locals) andalso
         length first_locals = length second_locals andalso
         List.all
           (fn variable => not (mem_var (variable, second_locals)))
           first_locals andalso
         first_dependencies = [branch] andalso
         second_dependencies = [branch]
       end)

val _ =
  test
    ("separate rule caches neither reuse conversions nor templates",
     fn () =>
       let
         val first_cache = blastRule.newCache ()
         val second_cache = blastRule.newCache ()
         val formula =
           mkGoal
             (blastRule.fromGoalTerm
                (mk_conj (mk_var ("p", bool), mk_var ("q", bool))))
         val claset = clasetLib.the_claset ()
         val first_rule =
           case blastRule.safeRules first_cache claset [] formula of
               rule :: _ => rule
             | [] => raise Fail "no first-session conjunction rule"
         val first_vars = rule_vars first_rule
         val instantiated =
           unify (newState ())
             (first_vars, #pattern first_rule, formula)
         val second_rule =
           case blastRule.safeRules second_cache claset [] formula of
               rule :: _ => rule
             | [] => raise Fail "no second-session conjunction rule"
         val second_vars = rule_vars second_rule
       in
         instantiated andalso
         blastRule.conversionCount first_cache > 0 andalso
         blastRule.conversionCount second_cache > 0 andalso
         blastRule.hitCount first_cache = 0 andalso
         blastRule.hitCount second_cache = 0 andalso
         List.exists
           (fn variable => not (unassigned variable)) first_vars andalso
         List.all unassigned second_vars andalso
         List.all
           (fn variable => not (mem_var (variable, second_vars)))
           first_vars
       end)

val _ =
  test
    ("each search run starts cold and then reuses its rule cache",
     fn () =>
       let
         val p = mk_var ("cache_search_p", bool)
         val q = mk_var ("cache_search_q", bool)
         val goal = ([p, p], q)
         val claset = clasetLib.the_claset ()
         fun run () =
           #statistics
             (blastSearch.searchGoalWithStats claset 0 goal
                (fn proof => proof))
         val first = run ()
         val second = run ()
       in
         #rule_cache_hits first > 0 andalso
         #rule_cache_hits second > 0 andalso
         #rule_conversions first > 0 andalso
         #rule_conversions second > 0 andalso
         #rule_cache_hits first = #rule_cache_hits second andalso
         #rule_conversions first = #rule_conversions second
       end)

val _ =
  test
    ("successful hyp-subst has exact inference statistics",
     fn () =>
       let
         val alpha = Type.mk_vartype "'instrument_subst"
         val x = mk_var ("instrument_subst_x", alpha)
         val y = mk_var ("instrument_subst_y", alpha)
         val p = mk_var ("instrument_subst_p", alpha --> bool)
         val px = mk_comb (p, x)
         val py = mk_comb (p, y)
         val report =
           blastSearch.searchGoalWithStats clasetLib.empty_cs 0
             ([mk_eq (x, y), px], py) (fn proof => proof)
         val statistics = #statistics report
       in
         (case #result report of
              SOME proof =>
                List.exists
                  (fn blastSearch.HypSubst _ => true | _ => false)
                  (#script proof)
            | NONE => false) andalso
         #configured_depth statistics = 0 andalso
         #maximum_resource_cost statistics = 0 andalso
         #inferences_performed statistics = 2 andalso
         #branches_created statistics = 1 andalso
         #branches_closed statistics = 1 andalso
         #choices_pruned statistics = 0
       end)

val _ =
  test
    ("admitted pseudo-safe rule has exact inference statistics",
     fn () =>
       let
         val p = mk_var ("instrument_safe_p", bool)
         val report =
           blastSearch.searchGoalWithStats clasetLib.empty_cs 0
             ([], mk_imp (p, p)) (fn proof => proof)
         val statistics = #statistics report
       in
         (case #result report of
              SOME proof =>
                List.exists
                  (fn blastSearch.SafeRule _ => true | _ => false)
                  (#script proof)
            | NONE => false) andalso
         #configured_depth statistics = 0 andalso
         #maximum_resource_cost statistics = 0 andalso
         #inferences_performed statistics = 2 andalso
         #branches_created statistics = 1 andalso
         #branches_closed statistics = 1 andalso
         #choices_pruned statistics = 0
       end)

val _ =
  test
    ("safe fanout counts one inference and one extra branch",
     fn () =>
       let
         val p = mk_var ("instrument_fanout_p", bool)
         val q = mk_var ("instrument_fanout_q", bool)
         val cs =
           clasetLib.add_sintros
             [("andI", boolTheory.AND_INTRO_THM)] clasetLib.empty_cs
         val report =
           blastSearch.searchGoalMeasured
             {debug = true, stop = fn () => false}
             cs 0 ([], mk_conj (p, q)) (fn proof => proof)
         val statistics = #statistics report
       in
         #completion report = blastSearch.Completed andalso
         not (Option.isSome (#result report)) andalso
         length (#fullTrace report) > 1 andalso
         #configured_depth statistics = 0 andalso
         #maximum_resource_cost statistics = 0 andalso
         #inferences_performed statistics = 1 andalso
         #branches_created statistics = 2 andalso
         #branches_closed statistics = 0 andalso
         #choices_pruned statistics = 0
       end)

val _ =
  test
    ("safe nonclosing bound rejection is not counted",
     fn () =>
       let
         val q = mk_var ("instrument_safe_bound_q", bool)
         val branch = ref NONE
         val nonclosing = DISCH q boolTheory.TRUTH
         val cs =
           clasetLib.add_sintros [("nonclosing", nonclosing)]
             clasetLib.empty_cs
         val report =
           blastSearch.searchTermsMeasured
             {debug = false, stop = fn () => false} cs 0
             [mkGoal (Var branch)] (fn proof => proof)
         val statistics = #statistics report
       in
         #completion report = blastSearch.Completed andalso
         not (Option.isSome (#result report)) andalso
         #configured_depth statistics = 0 andalso
         #maximum_resource_cost statistics = 0 andalso
         #inferences_performed statistics = 0 andalso
         #branches_created statistics = 1 andalso
         #branches_closed statistics = 0 andalso
         #choices_pruned statistics = 0
       end)

val _ =
  test
    ("depth-0 unsafe nonclosing rule rejection is not counted",
     fn () =>
       let
         val x = mk_var ("instrument_unsafe_bound_x", bool)
         val p = mk_var ("instrument_unsafe_bound_p", bool --> bool)
         val cs =
           clasetLib.add_intros
             [("exists", EXISTS_INTRO_THM)] clasetLib.empty_cs
         val report =
           blastSearch.searchGoalWithStats cs 0
             ([], mk_exists (x, mk_comb (p, x)))
             (fn proof => proof)
         val statistics = #statistics report
       in
         not (Option.isSome (#result report)) andalso
         #configured_depth statistics = 0 andalso
         #maximum_resource_cost statistics = 0 andalso
         #inferences_performed statistics = 0 andalso
         #branches_created statistics = 1 andalso
         #branches_closed statistics = 0 andalso
         #choices_pruned statistics = 0
       end)

val _ =
  test
    ("closing safe rule may exceed the configured resource bound",
     fn () =>
       let
         val branch = ref NONE
         val cs =
           clasetLib.add_sintros [("truth", boolTheory.TRUTH)]
             clasetLib.empty_cs
         val report =
           blastSearch.searchTermsMeasured
             {debug = false, stop = fn () => false} cs 0
             [mkGoal (Var branch)] (fn proof => proof)
         val statistics = #statistics report
       in
         #completion report = blastSearch.Completed andalso
         Option.isSome (#result report) andalso
         #configured_depth statistics = 0 andalso
         #maximum_resource_cost statistics = 1 andalso
         #inferences_performed statistics = 1 andalso
         #branches_created statistics = 1 andalso
         #branches_closed statistics = 1 andalso
         #choices_pruned statistics = 0
       end)

fun zero_measured_work depth (statistics : blastSearch.statistics) =
  #configured_depth statistics = depth andalso
  #maximum_resource_cost statistics = 0 andalso
  #inferences_performed statistics = 0 andalso
  #branches_created statistics = 1 andalso
  #branches_closed statistics = 0 andalso
  #choices_pruned statistics = 0 andalso
  #rule_cache_hits statistics = 0 andalso
  #rule_conversions statistics = 0 andalso
  #emergency_cleanup_assignments statistics = 0 andalso
  #remaining_trail_assignments statistics = 0 andalso
  #cooperative_checkpoints statistics > 0 andalso
  #candidate_rules_enumerated statistics = 0 andalso
  #candidate_conversions_attempted statistics = 0 andalso
  #safe_rule_attempts statistics = 0 andalso
  #unsafe_rule_attempts statistics = 0 andalso
  #rule_unification_attempts statistics = 0 andalso
  #rule_unification_successes statistics = 0 andalso
  #equality_substitution_attempts statistics = 0 andalso
  #equality_substitution_successes statistics = 0 andalso
  #literal_close_attempts statistics = 0 andalso
  #literal_close_successes statistics = 0

val _ =
  test
    ("initial cooperative stop prevents goal and term search work",
     fn () =>
       let
         val p = mk_var ("instrument_initial_stop_p", bool)
         val goal = ([], p)
         val formulas = map #1 (blastRule.initialBranch goal)

         fun goal_run debug =
           let
             val polls = ref 0
             val reconstructions = ref 0
             fun stop () = (polls := !polls + 1; true)
             val report =
               blastSearch.searchGoalMeasured {debug = debug, stop = stop}
                 clasetLib.empty_cs 3 goal
                 (fn proof =>
                    (reconstructions := !reconstructions + 1; proof))
           in
             !polls > 0 andalso
             #cooperative_checkpoints (#statistics report) = !polls andalso
             !reconstructions = 0 andalso
             #completion report = blastSearch.Interrupted andalso
             not (Option.isSome (#result report)) andalso
             #fullTrace report = [] andalso
             zero_measured_work 3 (#statistics report)
           end

         fun terms_run debug =
           let
             val polls = ref 0
             val reconstructions = ref 0
             fun stop () = (polls := !polls + 1; true)
             val report =
               blastSearch.searchTermsMeasured {debug = debug, stop = stop}
                 clasetLib.empty_cs 3 formulas
                 (fn proof =>
                    (reconstructions := !reconstructions + 1; proof))
           in
             !polls > 0 andalso
             #cooperative_checkpoints (#statistics report) = !polls andalso
             !reconstructions = 0 andalso
             #completion report = blastSearch.Interrupted andalso
             not (Option.isSome (#result report)) andalso
             #fullTrace report = [] andalso
             zero_measured_work 3 (#statistics report)
           end
       in
         goal_run false andalso goal_run true andalso
         terms_run false andalso terms_run true
       end)

val _ =
  test
    ("goal and term measured entry points have equivalent completion",
     fn () =>
       let
         val goal = ([], boolSyntax.T)
         val cs =
           clasetLib.add_sintros [("truth", boolTheory.TRUTH)]
             clasetLib.empty_cs

         fun check debug
               (report : blastSearch.proof blastSearch.measured_result)
               reconstructions =
           let
             val statistics = #statistics report
           in
             !reconstructions = 1 andalso
             #completion report = blastSearch.Completed andalso
             Option.isSome (#result report) andalso
             (debug = not (null (#fullTrace report))) andalso
             #configured_depth statistics = 0 andalso
             #maximum_resource_cost statistics = 0 andalso
             #inferences_performed statistics = 1 andalso
             #branches_created statistics = 1 andalso
             #branches_closed statistics = 1 andalso
             #choices_pruned statistics = 0 andalso
             #rule_cache_hits statistics = 0 andalso
             #rule_conversions statistics = 1 andalso
             #cooperative_checkpoints statistics > 0 andalso
             #candidate_rules_enumerated statistics = 1 andalso
             #candidate_conversions_attempted statistics = 1 andalso
             #safe_rule_attempts statistics = 1 andalso
             #unsafe_rule_attempts statistics = 0 andalso
             #rule_unification_attempts statistics = 1 andalso
             #rule_unification_successes statistics = 1 andalso
             #equality_substitution_attempts statistics = 1 andalso
             #equality_substitution_successes statistics = 0 andalso
             #literal_close_attempts statistics = 0 andalso
             #literal_close_successes statistics = 0
           end

         fun goal_run debug =
           let
             val reconstructions = ref 0
             val report =
               blastSearch.searchGoalMeasured
                 {debug = debug, stop = fn () => false}
                 cs 0 goal
                 (fn proof =>
                    (reconstructions := !reconstructions + 1; proof))
           in
             check debug report reconstructions
           end

         fun terms_run debug =
           let
             val reconstructions = ref 0
             val formulas = map #1 (blastRule.initialBranch goal)
             val report =
               blastSearch.searchTermsMeasured
                 {debug = debug, stop = fn () => false}
                 cs 0 formulas
                 (fn proof =>
                    (reconstructions := !reconstructions + 1; proof))
           in
             check debug report reconstructions
           end
       in
         goal_run false andalso goal_run true andalso
         terms_run false andalso terms_run true
       end)

val _ =
  test
    ("cooperative interruption is distinct from completed exhaustion",
     fn () =>
       let
         val p = mk_var ("instrument_interrupt_p", bool)
         val q = mk_var ("instrument_interrupt_q", bool)
         val polls = ref 0
         val cs =
           clasetLib.add_sintros
             [("andI", boolTheory.AND_INTRO_THM)] clasetLib.empty_cs
         fun stop () = (polls := !polls + 1; true)
         val interrupted =
           blastSearch.searchGoalMeasured {debug = true, stop = stop}
             cs 0 ([], mk_conj (p, q)) (fn proof => proof)
         val completed =
           blastSearch.searchGoalMeasured
             {debug = true, stop = fn () => false}
             cs 0 ([], mk_conj (p, q)) (fn proof => proof)
         val partial = #statistics interrupted
         val final = #statistics completed
       in
         #completion interrupted = blastSearch.Interrupted andalso
         !polls > 0 andalso
         #completion completed = blastSearch.Completed andalso
         not (Option.isSome (#result interrupted)) andalso
         not (Option.isSome (#result completed)) andalso
         #inferences_performed partial <= #inferences_performed final andalso
         #branches_created partial <= #branches_created final andalso
         #branches_closed partial <= #branches_closed final andalso
         #cooperative_checkpoints partial = !polls andalso
         #candidate_conversions_attempted partial <=
           #candidate_rules_enumerated partial andalso
         length (#fullTrace completed) > 1
       end)

val _ =
  test
    ("cooperative stop exceptions preserve their exact constructors",
     fn () =>
       let
         val p = mk_var ("instrument_stop_exception_p", bool)
         exception StopSentinel of int ref
         val sentinel = ref 17
         fun raises stop expected =
           (ignore
              (blastSearch.searchGoalMeasured
                 {debug = false, stop = stop}
                 clasetLib.empty_cs 0 ([], p) (fn proof => proof));
            false)
           handle StopSentinel actual =>
                    expected = 1 andalso actual = sentinel
                | blastSearch.PROOF_FAILED => expected = 2
                | _ => false
       in
         raises (fn () => raise StopSentinel sentinel) 1 andalso
         raises (fn () => raise blastSearch.PROOF_FAILED) 2
       end)

fun zero_phase_statistics (statistics : blastSearch.statistics) =
  #cooperative_checkpoints statistics = 0 andalso
  #candidate_rules_enumerated statistics = 0 andalso
  #candidate_conversions_attempted statistics = 0 andalso
  #safe_rule_attempts statistics = 0 andalso
  #unsafe_rule_attempts statistics = 0 andalso
  #rule_unification_attempts statistics = 0 andalso
  #rule_unification_successes statistics = 0 andalso
  #equality_substitution_attempts statistics = 0 andalso
  #equality_substitution_successes statistics = 0 andalso
  #literal_close_attempts statistics = 0 andalso
  #literal_close_successes statistics = 0

val _ =
  test
    ("statistics-only search does no measured phase monitoring",
     fn () =>
       let
         val report =
           blastSearch.searchGoalWithStats clasetLib.empty_cs 0
             ([boolSyntax.T], boolSyntax.T) (fn proof => proof)
       in
         Option.isSome (#result report) andalso
         zero_phase_statistics (#statistics report)
       end)

fun script_view (proof : blastSearch.proof) =
  let
    fun origin (blastRule.Stored {is_elim, theorem}) =
          (if is_elim then "elim:" else "intro:") ^
          Parse.term_to_string (concl theorem)
      | origin blastRule.ImpIntro = "imp"
      | origin blastRule.AllIntro = "all"
    fun option NONE = "-"
      | option (SOME position) = Int.toString position
    fun hidden rule =
      String.concatWith "," (map option (#hidden_assumptions rule))
    fun step (blastSearch.HypSubst {equality}) =
          "subst:" ^ Int.toString equality
      | step (blastSearch.CloseAssume {assumption}) =
          "assume:" ^ Int.toString assumption
      | step (blastSearch.CloseContradiction {negative, positive}) =
          "contradiction:" ^ Int.toString negative ^ ":" ^
          Int.toString positive
      | step (blastSearch.SafeRule {rule, updated, major}) =
          "safe:" ^ Bool.toString updated ^ ":" ^ origin (#origin rule) ^
          ":" ^ option major ^ ":" ^ hidden rule
      | step blastSearch.DeferGoal = "defer"
      | step
          (blastSearch.UnsafeRule
            {rule, updated, duplicate, major}) =
          "unsafe:" ^ Bool.toString updated ^ ":" ^
          Bool.toString duplicate ^ ":" ^ origin (#origin rule) ^ ":" ^
          option major ^ ":" ^ hidden rule
  in
    map step (#script proof)
  end

fun selector_view ({script, ...} : blastSearch.proof) =
  let
    fun option NONE = "-"
      | option (SOME position) = Int.toString position
    fun step (blastSearch.HypSubst {equality}) =
          "subst:" ^ Int.toString equality
      | step (blastSearch.CloseAssume {assumption}) =
          "assume:" ^ Int.toString assumption
      | step (blastSearch.CloseContradiction {negative, positive}) =
          "contr:" ^ Int.toString negative ^ ":" ^
          Int.toString positive
      | step (blastSearch.SafeRule {major, ...}) =
          "safe:" ^ option major
      | step blastSearch.DeferGoal = "defer"
      | step (blastSearch.UnsafeRule {major, duplicate, ...}) =
          "unsafe:" ^ option major ^ ":" ^ Bool.toString duplicate
  in
    map step script
  end

fun same_proof_options
      (NONE : blastSearch.proof option, NONE : blastSearch.proof option) = true
  | same_proof_options (SOME left, SOME right) =
      script_view left = script_view right andalso
      #branches_created left = #branches_created right andalso
      #branches_closed left = #branches_closed right andalso
      #choices_pruned left = #choices_pruned right
  | same_proof_options _ = false

fun same_old_statistics
      (left : blastSearch.statistics, right : blastSearch.statistics) =
  #configured_depth left = #configured_depth right andalso
  #maximum_resource_cost left = #maximum_resource_cost right andalso
  #inferences_performed left = #inferences_performed right andalso
  #branches_created left = #branches_created right andalso
  #branches_closed left = #branches_closed right andalso
  #choices_pruned left = #choices_pruned right andalso
  #rule_cache_hits left = #rule_cache_hits right andalso
  #rule_conversions left = #rule_conversions right

fun same_phase_statistics
      (left : blastSearch.statistics, right : blastSearch.statistics) =
  #cooperative_checkpoints left = #cooperative_checkpoints right andalso
  #candidate_rules_enumerated left =
    #candidate_rules_enumerated right andalso
  #candidate_conversions_attempted left =
    #candidate_conversions_attempted right andalso
  #safe_rule_attempts left = #safe_rule_attempts right andalso
  #unsafe_rule_attempts left = #unsafe_rule_attempts right andalso
  #rule_unification_attempts left =
    #rule_unification_attempts right andalso
  #rule_unification_successes left =
    #rule_unification_successes right andalso
  #equality_substitution_attempts left =
    #equality_substitution_attempts right andalso
  #equality_substitution_successes left =
    #equality_substitution_successes right andalso
  #literal_close_attempts left = #literal_close_attempts right andalso
  #literal_close_successes left = #literal_close_successes right

fun same_cleanup_statistics
      (left : blastSearch.statistics, right : blastSearch.statistics) =
  #emergency_cleanup_assignments left =
    #emergency_cleanup_assignments right andalso
  #remaining_trail_assignments left =
    #remaining_trail_assignments right

fun trace_variables trace =
  List.concat
    (map
       (fn branches =>
          List.concat
            (map (fn (branch : blastSearch.branch) => #vars branch)
               branches))
       trace)

fun trace_has_assignment trace =
  List.exists (fn variable => Option.isSome (!variable))
    (trace_variables trace)

fun trace_is_unassigned trace =
  List.all (fn variable => not (Option.isSome (!variable)))
    (trace_variables trace)

fun same_list compare ([], []) = true
  | same_list compare (left :: lefts, right :: rights) =
      compare (left, right) andalso same_list compare (lefts, rights)
  | same_list compare _ = false

type alpha_comparator =
  {term : blastTerm.term * blastTerm.term -> bool,
   variable : blastTerm.var * blastTerm.var -> bool}

fun new_alpha_comparator () : alpha_comparator =
  let
    val variables = ref ([] : (blastTerm.var * blastTerm.var) list)
    val skolems = ref ([] : (string * string) list)

    fun bijection equal table (left, right) =
      case List.find (fn (known, _) => equal (left, known)) (!table) of
          SOME (_, known) => equal (right, known)
        | NONE =>
            if List.exists
                 (fn (_, known) => equal (right, known)) (!table)
            then false
            else (table := (left, right) :: !table; true)

    fun variable (left, right) =
      bijection (op =) variables (left, right) andalso
      (case (!left, !right) of
           (NONE, NONE) => true
         | (SOME left_term, SOME right_term) =>
             term (left_term, right_term)
         | _ => false)
    and term (Const (left, left_args), Const (right, right_args)) =
          left = right andalso same_list term (left_args, right_args)
      | term (Skolem (left, left_deps), Skolem (right, right_deps)) =
          bijection (op =) skolems (left, right) andalso
          same_list variable (left_deps, right_deps)
      | term (Free left, Free right) = left = right
      | term (Var left, Var right) = variable (left, right)
      | term (Bound left, Bound right) = left = right
      | term (Abs (_, left), Abs (_, right)) = term (left, right)
      | term (left_f $ left_x, right_f $ right_x) =
          term (left_f, right_f) andalso term (left_x, right_x)
      | term _ = false
  in
    {term = term, variable = variable}
  end

fun same_rule_lists_alpha (left_rules, right_rules) =
  let
    val compare = new_alpha_comparator ()
    fun same_origin
          (blastRule.Stored {is_elim = left, theorem = left_thm},
           blastRule.Stored {is_elim = right, theorem = right_thm}) =
          left = right andalso
          Term.aconv (concl left_thm) (concl right_thm)
      | same_origin (blastRule.ImpIntro, blastRule.ImpIntro) = true
      | same_origin (blastRule.AllIntro, blastRule.AllIntro) = true
      | same_origin _ = false
    fun same_rule (left : blastRule.tableau_rule,
                   right : blastRule.tableau_rule) =
      same_origin (#origin left, #origin right) andalso
      #term compare (#pattern left, #pattern right) andalso
      #hidden_assumptions left = #hidden_assumptions right andalso
      same_list
        (fn (left_premise, right_premise) =>
           same_list (#term compare) (left_premise, right_premise))
        (#premises left, #premises right)
  in
    same_list same_rule (left_rules, right_rules)
  end

fun same_traces_alpha (left_trace, right_trace) =
  let
    val compare = new_alpha_comparator ()
    fun same_pair ((left, left_md), (right, right_md)) =
      left_md = right_md andalso #term compare (left, right)
    fun same_level ((left_safe, left_unsafe),
                    (right_safe, right_unsafe)) =
      same_list same_pair (left_safe, right_safe) andalso
      same_list same_pair (left_unsafe, right_unsafe)
    fun same_branch
          (left : blastSearch.branch, right : blastSearch.branch) =
      #lim left = #lim right andalso
      same_list (#variable compare) (#vars left, #vars right) andalso
      same_list (#term compare) (#lits left, #lits right) andalso
      same_list same_level (#pairs left, #pairs right)
    fun same_state (left, right) =
      same_list same_branch (left, right)
  in
    same_list same_state (left_trace, right_trace)
  end

val _ =
  test
    ("ordinary Stats and measured searches are observationally equivalent",
     fn () =>
       let
         val p = mk_var ("phase_equiv_p", bool)
         val q = mk_var ("phase_equiv_q", bool)
         val disj_cs =
           clasetLib.add_intros
             [("left", boolTheory.OR_INTRO_THM1),
              ("right", boolTheory.OR_INTRO_THM2)]
             clasetLib.empty_cs

         fun run cs depth goal reject_first =
           let
             fun continuation attempts proof =
               (attempts := !attempts + 1;
                if reject_first andalso !attempts = 1 then
                  raise blastSearch.PROOF_FAILED
                else proof)
             val ordinary_attempts = ref 0
             val stats_attempts = ref 0
             val measured_attempts = ref 0
             val ordinary =
               blastSearch.searchGoal cs depth goal
                 (continuation ordinary_attempts)
             val stats =
               blastSearch.searchGoalWithStats cs depth goal
                 (continuation stats_attempts)
             val measured =
               blastSearch.searchGoalMeasured
                 {debug = false, stop = fn () => false}
                 cs depth goal (continuation measured_attempts)
           in
             #completion measured = blastSearch.Completed andalso
             !ordinary_attempts = !stats_attempts andalso
             !stats_attempts = !measured_attempts andalso
             same_proof_options (ordinary, #result stats) andalso
             same_proof_options (#result stats, #result measured) andalso
             same_old_statistics
               (#statistics stats, #statistics measured) andalso
             #emergency_cleanup_assignments (#statistics stats) = 0 andalso
             #emergency_cleanup_assignments (#statistics measured) = 0
           end
       in
         run clasetLib.empty_cs 0 ([p], p) false andalso
         run clasetLib.empty_cs 0 ([], p) false andalso
         run disj_cs 1 ([p, q], mk_disj (p, q)) true
       end)

val _ =
  test
    ("deterministic generated queries preserve measured candidate order",
     fn () =>
       let
         val p = mk_var ("phase_random_p", bool)
         val q = mk_var ("phase_random_q", bool)
         val r = mk_var ("phase_random_r", bool)
         val witness = mk_var ("phase_random_witness", bool)
         val consequent = mk_var ("phase_random_consequent", bool)
         val atoms = [p, q, r]
         val cs = clasetLib.the_claset ()
         (* The intermediate product stays below a 31-bit Int.maxInt. *)
         fun next seed = (seed * 25173 + 13849) mod 32768
         fun formula 0 seed =
               (List.nth (atoms, seed mod length atoms), next seed)
           | formula depth seed =
               let
                 val seed1 = next seed
                 val (left, seed2) = formula (depth - 1) seed1
                 val (right, seed3) = formula (depth - 1) seed2
                 val result =
                   case seed mod 4 of
                       0 => mk_imp (left, right)
                     | 1 => mk_conj (left, right)
                     | 2 => mk_disj (left, right)
                     | _ => mk_neg left
               in
                 (result, seed3)
               end
         fun check 0 _ = true
           | check count seed =
               let
                 val (query, seed') = formula 3 seed
                 (* This assumption is satisfiable by setting witness true;
                    the fresh consequent can independently be false. *)
                 val goal = ([mk_disj (query, witness)], consequent)
                 val stats =
                   blastSearch.searchGoalWithStats cs 2 goal
                     (fn proof => proof)
                 val measured =
                   blastSearch.searchGoalMeasured
                     {debug = true, stop = fn () => false}
                     cs 2 goal (fn proof => proof)
                 val repeated =
                   blastSearch.searchGoalMeasured
                     {debug = true, stop = fn () => false}
                     cs 2 goal (fn proof => proof)
                 val measured_stats = #statistics measured
                 val repeated_stats = #statistics repeated
               in
                 not (Option.isSome (#result stats)) andalso
                 #completion measured = blastSearch.Completed andalso
                 not (Option.isSome (#result measured)) andalso
                 #completion repeated = blastSearch.Completed andalso
                 not (Option.isSome (#result repeated)) andalso
                 #inferences_performed measured_stats > 0 andalso
                 #candidate_rules_enumerated measured_stats > 0 andalso
                 not (null (#fullTrace measured)) andalso
                 same_proof_options (#result stats, #result measured) andalso
                 same_proof_options
                   (#result measured, #result repeated) andalso
                 same_old_statistics
                   (#statistics stats, measured_stats) andalso
                 same_old_statistics
                   (measured_stats, repeated_stats) andalso
                 same_phase_statistics
                   (measured_stats, repeated_stats) andalso
                 same_cleanup_statistics
                   (measured_stats, repeated_stats) andalso
                 same_traces_alpha
                   (#fullTrace measured, #fullTrace repeated) andalso
                 check (count - 1) seed'
               end
       in
         check 24 1
       end)

val _ =
  test
    ("measured rule conversion and cache hits preserve ordinary outputs",
     fn () =>
       let
         val p = mk_var ("phase_rule_p", bool)
         val q = mk_var ("phase_rule_q", bool)
         val formula =
           mkGoal (blastRule.fromGoalTerm (mk_conj (p, q)))
         val cs =
           clasetLib.add_sintros
             [("andI", boolTheory.AND_INTRO_THM)] clasetLib.empty_cs
         val ordinary_cache = blastRule.newCache ()
         val measured_cache = blastRule.newCache ()
         val polls = ref 0
         val candidates = ref 0
         val conversions = ref 0
         val monitor : blastRule.monitor =
           {checkpoint = fn () => polls := !polls + 1,
            candidate = fn () => candidates := !candidates + 1,
            conversion = fn () => conversions := !conversions + 1}
         val ordinary =
           blastRule.safeRules ordinary_cache cs [] formula
         val measured =
           blastRule.safeRulesMeasured monitor measured_cache cs [] formula
         val measured_hit =
           blastRule.safeRulesMeasured monitor measured_cache cs [] formula

       in
         same_rule_lists_alpha (ordinary, measured) andalso
         same_rule_lists_alpha (measured, measured_hit) andalso
         !polls > 0 andalso !candidates = 1 andalso !conversions = 1 andalso
         blastRule.conversionCount ordinary_cache =
           blastRule.conversionCount measured_cache andalso
         blastRule.hitCount measured_cache = 1
       end)

val _ =
  test
    ("rule alpha comparison preserves sharing, types and dependencies",
     fn () =>
       let
         fun rule pattern premises : blastRule.tableau_rule =
           {origin = blastRule.ImpIntro,
            pattern = pattern, premises = premises,
            hidden_assumptions = map (fn _ => NONE) premises}
         val shared_left = ref NONE
         val shared_right = ref NONE
         val broken_right = ref NONE
         val sharing_left =
           [rule (Const ("sharing", []) $ Var shared_left)
              [[Var shared_left]]]
         val sharing_right =
           [rule (Const ("sharing", []) $ Var shared_right)
              [[Var broken_right]]]
         val typed_left =
           [rule (Const ("typed", [Free "'a", Free "'b"])) []]
         val typed_swapped =
           [rule (Const ("typed", [Free "'b", Free "'a"])) []]
         val dependency_left = ref NONE
         val dependency_right = ref NONE
         val dependency_other = ref NONE
         val dependencies =
           [rule
              (Skolem ("left_skolem",
                 [dependency_left, dependency_left])) []]
         val renamed_dependencies =
           [rule
              (Skolem ("right_skolem",
                 [dependency_right, dependency_right])) []]
         val wrong_identity =
           [rule
              (Skolem ("right_skolem",
                 [dependency_right, dependency_other])) []]
         val wrong_count =
           [rule (Skolem ("right_skolem", [dependency_right])) []]
         val hidden_left : blastRule.tableau_rule list =
           [{origin = blastRule.ImpIntro,
             pattern = Const ("hidden", []), premises = [[]],
             hidden_assumptions = [NONE]}]
         val hidden_right : blastRule.tableau_rule list =
           [{origin = blastRule.ImpIntro,
             pattern = Const ("hidden", []), premises = [[]],
             hidden_assumptions = [SOME 0]}]
       in
         same_rule_lists_alpha (dependencies, renamed_dependencies) andalso
         not (same_rule_lists_alpha (sharing_left, sharing_right)) andalso
         not (same_rule_lists_alpha (typed_left, typed_swapped)) andalso
         not (same_rule_lists_alpha (dependencies, wrong_identity)) andalso
         not (same_rule_lists_alpha (dependencies, wrong_count)) andalso
         not (same_rule_lists_alpha (hidden_left, hidden_right))
       end)

val _ =
  test
    ("hidden provenance is identical on ordinary measured and cache paths",
     fn () =>
       let
         val p = mk_var ("hidden_parity_p", bool)
         val q = mk_var ("hidden_parity_q", bool)
         val r = mk_var ("hidden_parity_r", bool)
         val theorem =
           prove
             (list_mk_forall
                ([p, q, r],
                 mk_imp
                   (mk_conj (mk_neg p, q),
                    mk_imp (mk_imp (q, mk_imp (mk_neg r, p)), r))),
              PROVE_TAC [boolTheory.EXCLUDED_MIDDLE])
         val cs =
           clasetLib.add_selims [("hidden-parity", theorem)]
             clasetLib.empty_cs
         val formula =
           blastRule.fromGoalTerm (mk_conj (mk_neg p, q))
         val ordinary_cache = blastRule.newCache ()
         val measured_cache = blastRule.newCache ()
         val monitor : blastRule.monitor =
           {checkpoint = fn () => (), candidate = fn () => (),
            conversion = fn () => ()}
         val ordinary =
           blastRule.safeRules ordinary_cache cs [] formula
         val ordinary_hit =
           blastRule.safeRules ordinary_cache cs [] formula
         val measured =
           blastRule.safeRulesMeasured monitor measured_cache cs [] formula
         val measured_hit =
           blastRule.safeRulesMeasured monitor measured_cache cs [] formula
         fun hidden (rules : blastRule.tableau_rule list) =
           map #hidden_assumptions rules
       in
         hidden ordinary = [[SOME 0]] andalso
         hidden ordinary_hit = hidden ordinary andalso
         hidden measured = hidden ordinary andalso
         hidden measured_hit = hidden ordinary andalso
         same_rule_lists_alpha (ordinary, ordinary_hit) andalso
         same_rule_lists_alpha (ordinary, measured) andalso
         same_rule_lists_alpha (measured, measured_hit) andalso
         blastRule.hitCount ordinary_cache = 1 andalso
         blastRule.hitCount measured_cache = 1
       end)

val _ =
  test
    ("conversion/query equivalence matrix covers all rule families",
     fn () =>
       let
         val p = mk_var ("phase_matrix_p", bool)
         val q = mk_var ("phase_matrix_q", bool)
         val r = mk_var ("phase_matrix_r", bool)
         val alpha = Type.mk_vartype "'phase_matrix"
         val x = mk_var ("phase_matrix_x", alpha)
         val pred = mk_var ("phase_matrix_pred", alpha --> bool)
         val qp = mk_conj (q, p)
         val qp_assumption = ASSUME qp
         val conjunctive_intro =
           GENL [p, q]
             (DISCH qp
                (CONJ (CONJUNCT2 qp_assumption)
                   (CONJUNCT1 qp_assumption)))
         val major = mk_disj (p, q)
         val side = mk_conj (r, p)
         val conjunctive_elim =
           GENL [p, q, r]
             (DISCH major
                (DISCH side (CONJUNCT1 (ASSUME side))))
         val specializing =
           GENL [pred, x]
             (DISCH (mk_forall (x, mk_comb (pred, x)))
                (SPEC x
                   (ASSUME (mk_forall (x, mk_comb (pred, x))))))
         val safe_intro_cs =
           clasetLib.add_sintros
             [("matrix_canonical_intro", boolTheory.AND_INTRO_THM),
              ("matrix_conjunctive_intro", conjunctive_intro)]
             clasetLib.empty_cs
         val safe_elim_cs =
           clasetLib.add_selims
             [("matrix_canonical_elim", boolTheory.OR_ELIM_THM),
              ("matrix_conjunctive_elim", conjunctive_elim)]
             clasetLib.empty_cs
         val unsafe_intro_cs =
           clasetLib.add_intros
             [("matrix_left", boolTheory.OR_INTRO_THM1),
              ("matrix_right", boolTheory.OR_INTRO_THM2)]
             clasetLib.empty_cs
         val quantified_cs =
           clasetLib.add_sintros
             [("matrix_specialize", specializing)] clasetLib.empty_cs
         val polymorphic_cs =
           clasetLib.add_sintros
             [("matrix_refl", boolTheory.EQ_REFL)] clasetLib.empty_cs
         val conjunction =
           mkGoal (blastRule.fromGoalTerm (mk_conj (p, q)))
         val disjunction =
           mkGoal (blastRule.fromGoalTerm (mk_disj (p, q)))
         val assertion = blastRule.fromGoalTerm major
         val equality =
           mkGoal (blastRule.fromGoalTerm (mk_eq (x, x)))
         val specialized =
           mkGoal (blastRule.fromGoalTerm (mk_comb (pred, x)))
         val implication =
           mkGoal (blastRule.fromGoalTerm (mk_imp (p, q)))
         val universal =
           mkGoal
             (blastRule.fromGoalTerm
                (mk_forall (x, mk_comb (pred, x))))

         fun origin (blastRule.Stored {is_elim, theorem}) =
               (if is_elim then "elim:" else "intro:") ^
               Parse.term_to_string (concl theorem)
           | origin blastRule.ImpIntro = "pseudo:imp"
           | origin blastRule.AllIntro = "pseudo:all"
         fun origin_kind text =
           if String.isPrefix "elim:" text then "elim"
           else if String.isPrefix "intro:" text then "intro"
           else text
         fun rule_origin
               ({origin, ...} : blastRule.tableau_rule) = origin
         fun views rules = map (origin o rule_origin) rules

         fun check
               {safe, cs, formula, candidates, rule_count,
                origin_kinds, ...} =
           let
             val ordinary_cache = blastRule.newCache ()
             val measured_cache = blastRule.newCache ()
             val polls = ref 0
             val seen_candidates = ref 0
             val seen_conversions = ref 0
             val monitor : blastRule.monitor =
               {checkpoint = fn () => polls := !polls + 1,
                candidate =
                  fn () => seen_candidates := !seen_candidates + 1,
                conversion =
                  fn () => seen_conversions := !seen_conversions + 1}
             fun ordinary () =
               if safe then
                 blastRule.safeRules ordinary_cache cs [] formula
               else blastRule.unsafeRules ordinary_cache cs [] formula
             fun measured () =
               if safe then
                 blastRule.safeRulesMeasured monitor measured_cache cs []
                   formula
               else
                 blastRule.unsafeRulesMeasured monitor measured_cache cs []
                   formula
             val ordinary_miss = ordinary ()
             val ordinary_hit = ordinary ()
             val measured_miss = measured ()
             val measured_hit = measured ()
             val expected_view = views ordinary_miss
           in
             length ordinary_miss = rule_count andalso
             views measured_miss = expected_view andalso
             views ordinary_hit = expected_view andalso
             views measured_hit = expected_view andalso
             map origin_kind expected_view = origin_kinds andalso
             same_rule_lists_alpha (ordinary_miss, measured_miss) andalso
             same_rule_lists_alpha (ordinary_hit, measured_hit) andalso
             same_rule_lists_alpha (ordinary_miss, ordinary_hit) andalso
             same_rule_lists_alpha (measured_miss, measured_hit) andalso
             !polls > 0 andalso !seen_candidates = candidates andalso
             !seen_conversions = candidates andalso
             blastRule.conversionCount ordinary_cache = candidates andalso
             blastRule.conversionCount measured_cache = candidates andalso
             blastRule.hitCount ordinary_cache = 1 andalso
             blastRule.hitCount measured_cache = 1
           end

         val cases =
           [{name = "safe intro canonical/noncanonical conjunction",
             safe = true, cs = safe_intro_cs, formula = conjunction,
             candidates = 2, rule_count = 2,
             origin_kinds = ["intro", "intro"]},
            {name = "safe elim canonical/noncanonical conjunction",
             safe = true, cs = safe_elim_cs, formula = assertion,
             candidates = 2, rule_count = 2,
             origin_kinds = ["elim", "elim"]},
            {name = "unsafe intro ordering", safe = false,
             cs = unsafe_intro_cs, formula = disjunction,
             candidates = 2, rule_count = 2,
             origin_kinds = ["intro", "intro"]},
            {name = "quantified specialization", safe = true,
             cs = quantified_cs, formula = specialized,
             candidates = 1, rule_count = 1,
             origin_kinds = ["intro"]},
            {name = "typed polymorphic rule", safe = true,
             cs = polymorphic_cs, formula = equality,
             candidates = 1, rule_count = 1,
             origin_kinds = ["intro"]},
            {name = "implication pseudo-rule", safe = true,
             cs = clasetLib.empty_cs, formula = implication,
             candidates = 0, rule_count = 1,
             origin_kinds = ["pseudo:imp"]},
            {name = "universal pseudo-rule", safe = true,
             cs = clasetLib.empty_cs, formula = universal,
             candidates = 0, rule_count = 1,
             origin_kinds = ["pseudo:all"]}]
       in
         List.all check cases
       end)

val _ =
  test
    ("completed measured searches have exact phase counters",
     fn () =>
       let
         val p = mk_var ("phase_exact_p", bool)
         val alpha = Type.mk_vartype "'phase_exact"
         val x = mk_var ("phase_exact_x", alpha)
         val y = mk_var ("phase_exact_y", alpha)
         val pred = mk_var ("phase_exact_pred", alpha --> bool)
         val existential = mk_var ("phase_exact_ex", bool)
         val predicate = mk_var ("phase_exact_ep", bool --> bool)

         fun measured cs depth goal =
           blastSearch.searchGoalMeasured
             {debug = false, stop = fn () => false}
             cs depth goal (fn proof => proof)

         val literal =
           #statistics (measured clasetLib.empty_cs 0 ([p], p))
         val equality =
           #statistics
             (measured clasetLib.empty_cs 0
                ([mk_eq (x, y), mk_comb (pred, x)],
                 mk_comb (pred, y)))
         val unsafe =
           #statistics
             (measured
                (clasetLib.add_intros
                   [("exists", EXISTS_INTRO_THM)] clasetLib.empty_cs)
                1 ([], mk_exists
                         (existential,
                          mk_comb (predicate, existential))))
       in
         #cooperative_checkpoints literal > 0 andalso
         #candidate_rules_enumerated literal = 0 andalso
         #candidate_conversions_attempted literal = 0 andalso
         #safe_rule_attempts literal = 0 andalso
         #unsafe_rule_attempts literal = 0 andalso
         #rule_unification_attempts literal = 0 andalso
         #rule_unification_successes literal = 0 andalso
         #equality_substitution_attempts literal = 1 andalso
         #equality_substitution_successes literal = 0 andalso
         #literal_close_attempts literal = 1 andalso
         #literal_close_successes literal = 1 andalso
         #cooperative_checkpoints equality > 0 andalso
         #equality_substitution_attempts equality = 3 andalso
         #equality_substitution_successes equality = 1 andalso
         #literal_close_attempts equality = 3 andalso
         #literal_close_successes equality = 1 andalso
         #cooperative_checkpoints unsafe > 0 andalso
         #candidate_rules_enumerated unsafe = 4 andalso
         #candidate_conversions_attempted unsafe = 4 andalso
         #safe_rule_attempts unsafe = 0 andalso
         #unsafe_rule_attempts unsafe = 1 andalso
         #rule_unification_attempts unsafe = 1 andalso
         #rule_unification_successes unsafe = 1
       end)

val _ =
  test
    ("rule attempt counters start after the preparation checkpoint",
     fn () =>
       let
         val truth_cs =
           clasetLib.add_sintros
             [("truth", boolTheory.TRUTH)] clasetLib.empty_cs
         val existential = mk_var ("phase_boundary_ex", bool)
         val predicate = mk_var ("phase_boundary_pred", bool --> bool)
         val exists_cs =
           clasetLib.add_intros
             [("exists", EXISTS_INTRO_THM)] clasetLib.empty_cs

         fun run cutoff cs depth terms =
           let
             val polls = ref 0
             fun stop () =
               (polls := !polls + 1; !polls >= cutoff)
           in
             blastSearch.searchTermsMeasured
               {debug = false, stop = stop} cs depth terms
               (fn proof => proof)
           end

         fun attempts safe statistics =
           if safe then #safe_rule_attempts statistics
           else #unsafe_rule_attempts statistics

         fun boundary safe cs depth terms =
           let
             fun seek cutoff =
               if cutoff > 1000 then NONE
               else
                 let
                   val report = run cutoff cs depth terms
                 in
                   if attempts safe (#statistics report) > 0 then
                     SOME (cutoff, report)
                   else seek (cutoff + 1)
                 end
           in
             case seek 1 of
                 NONE => false
               | SOME (cutoff, after) =>
                   let
                     val prior = run (cutoff - 1) cs depth terms
                     val prior_stats = #statistics prior
                     val after_stats = #statistics after
                   in
                     #completion prior = blastSearch.Interrupted andalso
                     #completion after = blastSearch.Interrupted andalso
                     attempts safe prior_stats = 0 andalso
                     #rule_unification_attempts prior_stats = 0 andalso
                     attempts safe after_stats = 1 andalso
                     #rule_unification_attempts after_stats = 1 andalso
                     #rule_unification_successes after_stats = 0
                   end
           end
       in
         boundary true truth_cs 0
           [mkGoal (Const (const_name {Thy = "bool", Name = "T"}, []))]
         andalso
         boundary false exists_cs 1
           [mkGoal
              (blastRule.fromGoalTerm
                 (mk_exists
                    (existential, mk_comb (predicate, existential))))]
       end)

val _ =
  test
    ("bounded inner interruption returns a coherent partial snapshot",
     fn () =>
       let
         val polls = ref 0
         val branch = ref NONE
         val truth_cs =
           clasetLib.add_sintros
             [("truth", boolTheory.TRUTH)] clasetLib.empty_cs
         val report =
           blastSearch.searchTermsMeasured
             {debug = true,
              stop = fn () =>
                (polls := !polls + 1; Option.isSome (!branch))}
             truth_cs 0 [mkGoal (Var branch)] (fn proof => proof)
         val statistics = #statistics report
       in
         #completion report = blastSearch.Interrupted andalso
         not (Option.isSome (#result report)) andalso
         not (Option.isSome (!branch)) andalso !polls > 0 andalso
         #cooperative_checkpoints statistics = !polls andalso
         #candidate_conversions_attempted statistics <=
           #candidate_rules_enumerated statistics andalso
         #rule_unification_successes statistics <=
           #rule_unification_attempts statistics
       end)

val _ =
  test
    ("interrupted measured unification rolls back branch assignments",
     fn () =>
       let
         val branch = ref NONE
         val cs =
           clasetLib.add_sintros
             [("truth", boolTheory.TRUTH)] clasetLib.empty_cs
         fun stop () = Option.isSome (!branch)
         val report =
           blastSearch.searchTermsMeasured {debug = true, stop = stop}
             cs 0 [mkGoal (Var branch)] (fn proof => proof)
         val statistics = #statistics report
       in
         #completion report = blastSearch.Interrupted andalso
         not (Option.isSome (!branch)) andalso
         #emergency_cleanup_assignments statistics = 1 andalso
         #remaining_trail_assignments statistics = 0 andalso
         not (null (#fullTrace report)) andalso
         #cooperative_checkpoints statistics > 0 andalso
         #safe_rule_attempts statistics = 1 andalso
         #rule_unification_attempts statistics = 1 andalso
         #rule_unification_successes statistics = 1 andalso
         #inferences_performed statistics = 0 andalso
         #branches_closed statistics = 0
       end)

val _ =
  test
    ("goal interruption abandons a large engine-owned trail exactly",
     fn () =>
       let
         val trail_length = 256
         fun variables 0 = []
           | variables count =
               mk_var
                 ("owned_interrupt_" ^ Int.toString count, bool) ::
               variables (count - 1)
         val variables = variables trail_length
         val body =
           List.foldr
             (fn (variable, rest) => mk_conj (variable, rest))
             boolSyntax.T variables
         val proposition =
           List.foldr
             (fn (variable, rest) => mk_exists (variable, rest))
             body variables
         val goal = ([], proposition)
         val cs =
           clasetLib.add_sintros
             [("owned-and", boolTheory.AND_INTRO_THM),
              ("owned-truth", boolTheory.TRUTH)]
             (clasetLib.add_intros
                [("owned-exists", EXISTS_INTRO_THM)]
                clasetLib.empty_cs)
         val completed_polls = ref 0
         val completed_continuations = ref 0
         val completed =
           blastSearch.searchGoalMeasured
             {debug = false,
              stop = fn () =>
                (completed_polls := !completed_polls + 1; false)}
             cs trail_length goal
             (fn proof =>
                (completed_continuations :=
                   !completed_continuations + 1;
                 proof))
         val cutoff = !completed_polls

         fun interrupted_run () =
           let
             val polls = ref 0
             val continuations = ref 0
             val report =
               blastSearch.searchGoalMeasured
                 {debug = false,
                  stop = fn () =>
                    (polls := !polls + 1; !polls >= cutoff)}
                 cs trail_length goal
                 (fn proof =>
                    (continuations := !continuations + 1; proof))
           in
             (report, !polls, !continuations)
           end

         val (interrupted, interrupted_polls,
              interrupted_continuations) = interrupted_run ()
         val completed_statistics = #statistics completed
         val interrupted_statistics = #statistics interrupted
         val repeats = List.tabulate (4, fn _ => interrupted_run ())

         fun same_run (report, polls, continuations) =
           let
             val statistics = #statistics report
           in
             #completion report = blastSearch.Interrupted andalso
             not (Option.isSome (#result report)) andalso
             #fullTrace report = [] andalso polls = cutoff andalso
             continuations = 0 andalso
             same_old_statistics
               (interrupted_statistics, statistics) andalso
             same_phase_statistics
               (interrupted_statistics, statistics) andalso
             same_cleanup_statistics
               (interrupted_statistics, statistics)
           end
       in
         #completion completed = blastSearch.Completed andalso
         Option.isSome (#result completed) andalso
         !completed_continuations = 1 andalso cutoff > 0 andalso
         #completion interrupted = blastSearch.Interrupted andalso
         not (Option.isSome (#result interrupted)) andalso
         #fullTrace interrupted = [] andalso
         interrupted_polls = cutoff andalso
         interrupted_continuations = 0 andalso
         same_old_statistics
           (completed_statistics, interrupted_statistics) andalso
         same_phase_statistics
           (completed_statistics, interrupted_statistics) andalso
         #remaining_trail_assignments interrupted_statistics =
           trail_length andalso
         #emergency_cleanup_assignments interrupted_statistics = 0 andalso
         List.all same_run repeats
       end)

val _ =
  test
    ("debug goal interruption retains a coherent owned-state trace",
     fn () =>
       let
         val witness = mk_var ("owned_debug_witness", bool)
         val goal = ([], mk_exists (witness, witness))
         val cs =
           clasetLib.add_sintros
             [("owned-debug-truth", boolTheory.TRUTH)]
             (clasetLib.add_intros
                [("owned-debug-exists", EXISTS_INTRO_THM)]
                clasetLib.empty_cs)
         val completed_polls = ref 0
         val completed =
           blastSearch.searchGoalMeasured
             {debug = true,
              stop = fn () =>
                (completed_polls := !completed_polls + 1; false)}
             cs 1 goal (fn proof => proof)
         val cutoff = !completed_polls
         val interrupted_polls = ref 0
         val continuations = ref 0
         val interrupted =
           blastSearch.searchGoalMeasured
             {debug = true,
              stop = fn () =>
                (interrupted_polls := !interrupted_polls + 1;
                 !interrupted_polls >= cutoff)}
             cs 1 goal
             (fn proof =>
                (continuations := !continuations + 1; proof))
         val completed_statistics = #statistics completed
         val interrupted_statistics = #statistics interrupted
       in
         #completion completed = blastSearch.Completed andalso
         Option.isSome (#result completed) andalso cutoff > 0 andalso
         #completion interrupted = blastSearch.Interrupted andalso
         not (Option.isSome (#result interrupted)) andalso
         !interrupted_polls = cutoff andalso !continuations = 0 andalso
         not (null (#fullTrace interrupted)) andalso
         trace_has_assignment (#fullTrace interrupted) andalso
         length (#fullTrace completed) =
           length (#fullTrace interrupted) + 1 andalso
         same_old_statistics
           (completed_statistics, interrupted_statistics) andalso
         same_phase_statistics
           (completed_statistics, interrupted_statistics) andalso
         #remaining_trail_assignments interrupted_statistics = 1 andalso
         #emergency_cleanup_assignments interrupted_statistics = 0
       end)

val _ =
  test
    ("goal continuation exceptions restore reachable owned assignments",
     fn () =>
       let
         exception GoalContinuationStop of int ref
         val sentinel = ref 37
         val witness = mk_var ("owned_continuation_witness", bool)
         val goal = ([], mk_exists (witness, witness))
         val cs =
           clasetLib.add_sintros
             [("owned-continuation-truth", boolTheory.TRUTH)]
             (clasetLib.add_intros
                [("owned-continuation-exists", EXISTS_INTRO_THM)]
                clasetLib.empty_cs)
         val saved = ref NONE
         val assigned_at_entry = ref false
         fun reject proof =
           (saved := SOME proof;
            assigned_at_entry := trace_has_assignment (#trace proof);
            raise GoalContinuationStop sentinel)

         fun restored () =
           case !saved of
               SOME proof => trace_is_unassigned (#trace proof)
             | NONE => false
       in
         (ignore
            (blastSearch.searchGoalMeasured
               {debug = false, stop = fn () => false}
               cs 1 goal reject);
          false)
         handle GoalContinuationStop actual =>
                  actual = sentinel andalso !assigned_at_entry andalso
                  restored ()
              | _ => false
       end)

val _ =
  test
    ("goal stop exceptions at live owned state restore and rethrow",
     fn () =>
       let
         exception GoalStop of int ref
         val sentinel = ref 41
         val witness = mk_var ("owned_stop_witness", bool)
         val goal = ([], mk_exists (witness, witness))
         val cs =
           clasetLib.add_sintros
             [("owned-stop-truth", boolTheory.TRUTH)]
             (clasetLib.add_intros
                [("owned-stop-exists", EXISTS_INTRO_THM)]
                clasetLib.empty_cs)
         val calibration_polls = ref 0
         val calibration =
           blastSearch.searchGoalMeasured
             {debug = true,
              stop = fn () =>
                (calibration_polls := !calibration_polls + 1; false)}
             cs 1 goal (fn proof => proof)
         val cutoff = !calibration_polls
         val polls = ref 0
         val continuations = ref 0
         fun stop () =
           (polls := !polls + 1;
            if !polls >= cutoff then raise GoalStop sentinel else false)
       in
         #completion calibration = blastSearch.Completed andalso
         #remaining_trail_assignments (#statistics calibration) = 1 andalso
         (ignore
            (blastSearch.searchGoalMeasured {debug = true, stop = stop}
               cs 1 goal
               (fn proof =>
                  (continuations := !continuations + 1; proof)));
          false)
         handle GoalStop actual =>
                  actual = sentinel andalso !polls = cutoff andalso
                  !continuations = 0
              | _ => false
       end)

val _ =
  test
    ("inner stop-predicate exceptions preserve identity",
     fn () =>
       let
         exception InnerStop of int ref
         val sentinel = ref 23
         val branch = ref NONE
         val seen_assignment = ref false
         val cs =
           clasetLib.add_sintros
             [("truth", boolTheory.TRUTH)] clasetLib.empty_cs
         fun stop () =
           if Option.isSome (!branch) then
             (seen_assignment := true; raise InnerStop sentinel)
           else false
       in
         (ignore
            (blastSearch.searchTermsMeasured {debug = false, stop = stop}
               cs 0 [mkGoal (Var branch)] (fn proof => proof));
          false)
         handle InnerStop actual =>
                  actual = sentinel andalso !seen_assignment andalso
                  not (Option.isSome (!branch))
              | _ => false
       end)

val _ =
  test
    ("continuation exceptions restore caller-owned assignments",
     fn () =>
       let
         exception ReconstructionStop of int ref
         val sentinel = ref 31
         val branch = ref NONE
         val entered = ref false
         val cs =
           clasetLib.add_sintros
             [("truth", boolTheory.TRUTH)] clasetLib.empty_cs
         fun reject _ =
           (entered := Option.isSome (!branch);
            raise ReconstructionStop sentinel)
       in
         (ignore
            (blastSearch.searchTermsMeasured
               {debug = false, stop = fn () => false}
               cs 0 [mkGoal (Var branch)] reject);
          false)
         handle ReconstructionStop actual =>
                  actual = sentinel andalso !entered andalso
                  not (Option.isSome (!branch))
              | _ => false
       end)

val _ =
  test
    ("PROOF_FAILED event interruption keeps a coherent snapshot",
     fn () =>
       let
         val p = mk_var ("instrument_partial_backtrack_p", bool)
         val polls = ref 0
         val attempts = ref 0
         fun stop () =
           (polls := !polls + 1; !attempts = 1)
         fun reject proof =
           (attempts := !attempts + 1;
            if !attempts = 1 then raise blastSearch.PROOF_FAILED
            else proof)
         val report =
           blastSearch.searchGoalMeasured {debug = false, stop = stop}
             clasetLib.empty_cs 0 ([p, p], p) reject
         val statistics = #statistics report
         val coherent =
           !polls = #cooperative_checkpoints statistics andalso
           !attempts = 1 andalso
           #inferences_performed statistics >= 1 andalso
           #branches_closed statistics >= 1 andalso
           #literal_close_attempts statistics >=
             #literal_close_successes statistics andalso
           #literal_close_successes statistics >= 1
       in
         coherent andalso
         #completion report = blastSearch.Interrupted andalso
         not (Option.isSome (#result report)) andalso
         #fullTrace report = [] andalso
         #configured_depth statistics = 0 andalso
         #maximum_resource_cost statistics = 0 andalso
         #branches_created statistics = 1 andalso
         #choices_pruned statistics = 0
       end)

val _ =
  test
    ("successful backtracking search has exact complete instrumentation",
     fn () =>
       let
         val p = mk_var ("instrument_backtrack_p", bool)
         val q = mk_var ("instrument_backtrack_q", bool)
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
         val report =
           blastSearch.searchGoalWithStats cs 1
             ([p, q], mk_disj (p, q)) accept
         val statistics = #statistics report
       in
         !attempts = 2 andalso Option.isSome (#result report) andalso
         #configured_depth statistics = 1 andalso
         #maximum_resource_cost statistics = 1 andalso
         #inferences_performed statistics = 4 andalso
         #branches_created statistics = 1 andalso
         #branches_closed statistics = 2 andalso
         #choices_pruned statistics = 0
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
         has (fn blastSearch.HypSubst _ => true | _ => false) andalso
         has (fn blastSearch.CloseAssume _ => true | _ => false) andalso
         has
           (fn blastSearch.CloseContradiction _ => true | _ => false)
           andalso
         has (fn blastSearch.SafeRule _ => true | _ => false) andalso
         has (fn blastSearch.DeferGoal => true | _ => false) andalso
         has (fn blastSearch.UnsafeRule _ => true | _ => false)
       end)

val _ =
  test
    ("duplicate initial occurrences survive literal-choice backtracking",
     fn () =>
       let
         val p = mk_var ("provenance_duplicate_p", bool)
         val goal = ([p, p], p)
         val views = ref ([] : string list list)
         fun accept proof =
           case blastReconstruct.reconstruct goal proof of
               SOME ([], validation) =>
                 (ignore (validation []);
                  views := selector_view proof :: !views;
                  if length (!views) = 1 then
                    raise blastSearch.PROOF_FAILED
                  else proof)
             | _ => raise blastSearch.PROOF_FAILED
         val result =
           blastSearch.searchGoal clasetLib.empty_cs 0 goal accept
       in
         Option.isSome result andalso
         rev (!views) = [["assume:1"], ["assume:2"]]
       end)

val _ =
  test
    ("DeferGoal gives constructed negation its exact occurrence",
     fn () =>
       let
         val x = mk_var ("provenance_defer_x", bool)
         val a = mk_var ("provenance_defer_a", bool)
         val pred = mk_var ("provenance_defer_P", bool --> bool)
         val pa = mk_comb (pred, a)
         val goal = ([pa], mk_exists (x, mk_comb (pred, x)))
       in
         case blastReconstruct.searchGoal
           (clasetLib.the_claset ()) 1 goal of
             SOME (proof, ([], validation)) =>
               selector_view proof =
                 ["defer", "unsafe:1:true", "assume:2"] andalso
               (ignore (validation []); true)
           | _ => false
       end)

val _ =
  test
    ("hidden elimination antecedent shifts exact child selectors",
     fn () =>
       let
         val p = mk_var ("provenance_hidden_p", bool)
         val q = mk_var ("provenance_hidden_q", bool)
         val r = mk_var ("provenance_hidden_r", bool)
         val theorem =
           prove
             (list_mk_forall
                ([p, q, r],
                 mk_imp
                   (mk_conj (mk_neg p, q),
                    mk_imp (mk_imp (q, mk_imp (mk_neg r, p)), r))),
              PROVE_TAC [boolTheory.EXCLUDED_MIDDLE])
         val cs =
           clasetLib.add_selims [("provenance-hidden", theorem)]
             (clasetLib.the_claset ())
         val goal = ([p, mk_conj (mk_neg p, q)], r)
       in
         case blastReconstruct.searchGoal cs 0 goal of
             SOME (proof, ([], validation)) =>
               selector_view proof =
                 ["defer", "safe:3", "assume:5"] andalso
               (ignore (validation []); true)
           | _ => false
       end)

val _ =
  test
    ("nonduplicate elimination deletes and renumbers its major",
     fn () =>
       let
         val p = mk_var ("provenance_delete_p", bool)
         val q = mk_var ("provenance_delete_q", bool)
         val r = mk_var ("provenance_delete_r", bool)
         val goal = ([r, mk_conj (p, q)], p)
         val cs =
           clasetLib.add_selims [("provenance-and", CONJ_ELIM_THM)]
             clasetLib.empty_cs
       in
         case blastReconstruct.searchGoal cs 0 goal of
             SOME (proof, ([], validation)) =>
               selector_view proof = ["safe:2", "assume:2"] andalso
               (ignore (validation []); true)
           | _ => false
       end)

val _ =
  test
    ("multi-child elimination clones tokens in stable child order",
     fn () =>
       let
         val p = mk_var ("provenance_children_p", bool)
         val q = mk_var ("provenance_children_q", bool)
         val r = mk_var ("provenance_children_r", bool)
         val goal =
           ([mk_disj (p, q), mk_imp (p, r), mk_imp (q, r)], r)
       in
         case blastReconstruct.searchGoal
           (clasetLib.the_claset ()) 0 goal of
             SOME (proof, ([], validation)) =>
               selector_view proof =
                 ["defer", "safe:2", "safe:3", "contr:1:2",
                  "contr:3:1", "safe:3", "safe:4", "contr:1:3",
                  "contr:4:1", "contr:3:1"] andalso
               #branches_created proof > 1 andalso
               (ignore (validation []); true)
           | _ => false
       end)

val _ =
  test
    ("duplicate elimination retains and moves back its exact major",
     fn () =>
       let
         val x = mk_var ("provenance_gamma_x", bool)
         val a = mk_var ("provenance_gamma_a", bool)
         val pred = mk_var ("provenance_gamma_P", bool --> bool)
         val universal = mk_forall (x, mk_comb (pred, x))
         val goal = ([universal], mk_comb (pred, a))
         val cs =
           clasetLib.add_elims
             [("provenance-all", FORALL_ELIM_THM)]
             clasetLib.empty_cs
       in
         case blastReconstruct.searchGoal cs 1 goal of
             SOME (proof, ([], validation)) =>
               let
                 val report =
                   blastReconstruct.reconstructWithMeasured
                     {observe = NONE, stop = fn () => false}
                     cs goal proof
               in
                 selector_view proof =
                   ["unsafe:1:true", "assume:1"] andalso
                 #completion report = blastReconstruct.Completed andalso
                 Option.isSome (#result report) andalso
                 #duplicate_child_moves (#statistics report) = 1 andalso
                 (ignore (validation []); true)
               end
           | _ => false
       end)

val _ =
  test
    ("exact reverse duplicate elim preserves selected occurrence and order",
     fn () =>
       let
         val major_atom = mk_var ("static_duplicate_major", bool)
         val target = mk_var ("static_duplicate_target", bool)
         val major_x = mk_disj (major_atom, major_atom)
         val major_y = major_x
         val theorem =
           Drule.SPECL [target, major_atom, major_atom]
             boolTheory.OR_ELIM_THM
         val reversed = clasetRules.REV_DUP_ELIM_RULE theorem
         val reversed_premises =
           clasetRules.rule_premises_of clasetRules.Elim reversed
         val goal = ([major_x, major_y, target], target)
         val node = clasetGoal.from_goal goal
         fun drain sequence =
           case seq.cases sequence of
               NONE => []
             | SOME (value, rest) => value :: drain rest
         val direct =
           drain
             (clasetStep.blast_rule_step_at clasetLib.empty_cs
               {theorem = reversed, elim = true, major = SOME 2}
               (node, 1))
         val enumerated =
           drain
             (clasetStep.blast_rule_step clasetLib.empty_cs
               {theorem = reversed, elim = true} (node, 1))
         val invalid_direct =
           seq.null
             (clasetStep.blast_rule_step_at clasetLib.empty_cs
               {theorem = reversed, elim = true, major = SOME 4}
               (node, 1))

         fun move_children count initial =
           let
             fun move position current =
               if position > count then current
               else
                 case seq.cases
                   (clasetStep.blast_move_back_step 1
                     (current, position))
                 of
                     SOME ((_, next), _) => move (position + 1) next
                   | NONE => raise Fail "duplicate move-back"
           in
             move 1 initial
           end

         val cache = blastRule.newCache ()
         val converted =
           case blastRule.convertElim cache [] theorem of
               SOME rule => rule
             | NONE =>
                 valOf
                   (blastRule.convertElim cache []
                     boolTheory.OR_ELIM_THM)
         val tableau_rule : blastRule.tableau_rule =
           {origin = blastRule.Stored {is_elim = true, theorem = theorem},
            pattern = #pattern converted,
            premises = #premises converted,
            hidden_assumptions = #hidden_assumptions converted}
         fun proof_at position : blastSearch.proof =
           {script =
              [blastSearch.UnsafeRule
                 {rule = tableau_rule, updated = false,
                  duplicate = true, major = SOME position},
               blastSearch.CloseAssume {assumption = 3},
               blastSearch.CloseAssume {assumption = 3}],
            trace = [], depth = 1, branches_created = 2,
            branches_closed = 2, choices_pruned = 0}
         val proof = proof_at 2
         val invalid_proof = proof_at 4
         val report =
           blastReconstruct.reconstructWithMeasuredDetailed
             {observe = NONE, observe_stored_rule = NONE,
              stop = fn () => false}
             clasetLib.empty_cs goal proof
         val invalid_report =
           blastReconstruct.reconstructWithMeasuredDetailed
             {observe = NONE, observe_stored_rule = NONE,
              stop = fn () => false}
             clasetLib.empty_cs goal invalid_proof

         fun prefix_order premise =
           let val (antecedents, residual) = strip_imp premise
           in
             length antecedents = 2 andalso
             ListPair.allEq (fn (left, right) => Term.aconv left right)
               (antecedents, [major_atom, major_x]) andalso
             Term.aconv residual target
           end

         fun render_all current =
           List.tabulate
             (length (clasetGoal.goals current),
              fn index => clasetGoal.render current (index + 1))

         fun same_goal ((left_asl, left_w), (right_asl, right_w)) =
           length left_asl = length right_asl andalso
           ListPair.allEq (fn (left, right) => Term.aconv left right)
             (left_asl, right_asl) andalso
           Term.aconv left_w right_w

         fun same_goal_list (left, right) =
           length left = length right andalso
           ListPair.allEq same_goal (left, right)

         fun direct_shape (record, next) =
           let
             val before_goals = render_all next
             val moved_goals = render_all (move_children 2 next)
             val expected_before =
               [([major_x, major_atom, major_x, target], target),
                ([major_x, major_atom, major_x, target], target)]
             val expected_moved =
               [([major_atom, major_x, target, major_x], target),
                ([major_atom, major_x, target, major_x], target)]
           in
             clasetStep.consumed_of record = SOME 2 andalso
             clasetGoal.replay_length next = 1 andalso
             same_goal_list (before_goals, expected_before) andalso
             same_goal_list (moved_goals, expected_moved) andalso
             let
               val (validated, _) =
                 Tactical.VALID
                   (fn _ =>
                     (before_goals, clasetStep.validation_of record))
                   goal
               val grounded =
                 clasetReplay.ground (clasetGoal.store next)
                   (clasetGoal.replay next)
               val (replayed, _) =
                 Tactical.VALID (clasetReplay.REPLAY_TAC grounded) goal
             in
               same_goal_list (validated, before_goals) andalso
               same_goal_list (replayed, before_goals)
             end
           end
       in
         (if Term.aconv major_x major_y then ()
          else raise Fail "duplicate equal majors") ;
         (if
         (case reversed_premises of
              [major, first_minor, second_minor] =>
                Term.aconv major major_x andalso
                Term.aconv first_minor second_minor andalso
                prefix_order first_minor andalso
                prefix_order second_minor
            | _ => false) then () else raise Fail "duplicate premises") ;
         (if (case direct of [result] => direct_shape result | _ => false)
          then ()
          else raise Fail
            ("duplicate direct " ^ Int.toString (length direct))) ;
         (if map (clasetStep.consumed_of o #1) enumerated =
               [SOME 1, SOME 2] andalso invalid_direct
          then () else raise Fail "duplicate occurrence enumeration") ;
         (if selector_view proof =
           ["unsafe:2:true", "assume:3", "assume:3"]
          then () else raise Fail "duplicate selector") ;
         (if #completion report = blastReconstruct.Completed
          then () else raise Fail "duplicate completion") ;
         (if #unsafe_rule_steps (#statistics report) = 1
          then () else raise Fail "duplicate unsafe") ;
         (if #stored_rule_transitions (#statistics report) = 1
          then () else raise Fail "duplicate transition") ;
         (if #duplicate_child_moves (#statistics report) = 2
          then () else raise Fail "duplicate moves") ;
         (if #close_assume_steps (#statistics report) = 2
          then () else raise Fail "duplicate closes") ;
         (if #grounding_attempts (#statistics report) = 1
          then () else raise Fail "duplicate grounding") ;
         (if #kernel_replay_attempts (#statistics report) = 1
          then () else raise Fail "duplicate kernel") ;
         (if #completion invalid_report = blastReconstruct.Completed andalso
             not (Option.isSome (#result invalid_report)) andalso
             #kernel_replay_attempts (#statistics invalid_report) = 0
          then () else raise Fail "duplicate selector recovery") ;
         (case #result report of
              SOME ([], validation) =>
                Term.aconv (concl (validation [])) target
            | _ => false)
       end)

val _ =
  test
    ("literal polarity records exact negative and positive representatives",
     fn () =>
       let
         val p = mk_var ("provenance_polarity_p", bool)
         val q = mk_var ("provenance_polarity_q", bool)
         val goal = ([p, mk_neg p], q)
       in
         case blastReconstruct.searchGoal clasetLib.empty_cs 0 goal of
             SOME (proof, ([], validation)) =>
               selector_view proof = ["contr:2:1"] andalso
               (ignore (validation []); true)
           | _ => false
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
    ("Blast exact reconstruction rejects a corrupted assumption selector",
     fn () =>
       let
         val p = mk_var ("corrupt_assume_p", bool)
         val q = mk_var ("corrupt_assume_q", bool)
         val goal = ([q, p, p], p)
         fun corrupt_step (blastSearch.CloseAssume _) =
               blastSearch.CloseAssume {assumption = 1}
           | corrupt_step step = step
         fun corrupt (proof : blastSearch.proof) : blastSearch.proof =
           {script = map corrupt_step (#script proof),
            trace = #trace proof, depth = #depth proof,
            branches_created = #branches_created proof,
            branches_closed = #branches_closed proof,
            choices_pruned = #choices_pruned proof}
       in
         case blastSearch.tryGoal clasetLib.empty_cs 0 goal of
             SOME (proof : blastSearch.proof) =>
               let
                 val corrupted = corrupt proof
                 val exact_script =
                   case #script proof of
                       [blastSearch.CloseAssume {assumption = 2}] => true
                     | _ => false
                 val original = blastReconstruct.reconstruct goal proof
                 val rejected =
                   blastReconstruct.reconstruct goal corrupted
                 val measured =
                   blastReconstruct.reconstructMeasured
                     {observe = NONE, stop = fn () => false}
                     goal corrupted
                 val reentry_attempts = ref 0
                 val reentry_views = ref ([] : string list list)
                 fun reject candidate =
                   let
                     val bad = corrupt candidate
                     val ordinary =
                       blastReconstruct.reconstruct goal bad
                     val diagnostic =
                       blastReconstruct.reconstructMeasured
                         {observe = NONE, stop = fn () => false}
                         goal bad
                     val _ = reentry_attempts := !reentry_attempts + 1
                     val _ =
                       reentry_views :=
                         selector_view candidate :: !reentry_views
                     val _ =
                       if not (Option.isSome ordinary) andalso
                          not (Option.isSome (#result diagnostic)) andalso
                          #kernel_replay_attempts
                            (#statistics diagnostic) = 0
                       then ()
                       else raise Fail "corrupt selector replay recovered"
                   in
                     raise blastSearch.PROOF_FAILED
                   end
                 val reentered =
                   blastSearch.searchGoal clasetLib.empty_cs 0 goal reject
               in
                 exact_script andalso
                 (case original of
                      SOME ([], validation) =>
                        (ignore (validation []); true)
                    | _ => false) andalso
                 not (Option.isSome rejected) andalso
                 #completion measured = blastReconstruct.Completed andalso
                 not (Option.isSome (#result measured)) andalso
                 #kernel_replay_attempts (#statistics measured) = 0 andalso
                 not (Option.isSome reentered) andalso
                 !reentry_attempts = 4 andalso
                 rev (!reentry_views) =
                   [["assume:2"], ["assume:3"],
                    ["assume:2"], ["assume:3"]]
               end
           | NONE => false
       end)

fun legacy_reconstruction_statistics_shape
      ({cooperative_checkpoints, phase_entries, phase_exits,
        replay_recursions, alternative_pulls, typed_steps,
        hyp_subst_steps, close_assume_steps, close_contradiction_steps,
        safe_rule_steps, defer_goal_steps, unsafe_rule_steps,
        stored_rule_setups, stored_rule_transitions,
        duplicate_child_moves, finish_open_goal_checks,
        grounding_attempts, kernel_replay_attempts,
        finish_residual_goal_checks} : blastReconstruct.statistics) =
  cooperative_checkpoints + phase_entries + phase_exits +
  replay_recursions + alternative_pulls + typed_steps +
  hyp_subst_steps + close_assume_steps + close_contradiction_steps +
  safe_rule_steps + defer_goal_steps + unsafe_rule_steps +
  stored_rule_setups + stored_rule_transitions +
  duplicate_child_moves + finish_open_goal_checks +
  grounding_attempts + kernel_replay_attempts +
  finish_residual_goal_checks >= 0

fun legacy_reconstruction_result_shape
      ({completion, current_phase, result, statistics} :
         blastReconstruct.measured_result) =
  (case completion of
       blastReconstruct.Completed => true
     | blastReconstruct.Interrupted => true) andalso
  (case current_phase of NONE => true | SOME _ => true) andalso
  (case result of NONE => true | SOME _ => true) andalso
  legacy_reconstruction_statistics_shape statistics

fun reconstruction_ticking_clock () =
  let
    val tick = ref 0
  in
    fn () =>
      let
        val current = !tick
        val _ = tick := current + 1
      in
        Time.fromSeconds (Int.toLarge current)
      end
  end

val reconstruct_v2_using_kernel =
  blastReconstruct.reconstructWithMeasuredTimedDetailedV2UsingKernel

val reconstruct_v3_using_kernel =
  blastReconstruct.reconstructWithMeasuredTimedDetailedV3UsingKernel

val reconstruct_v4_using_kernel =
  blastReconstruct.reconstructWithMeasuredTimedDetailedV4UsingKernel

val reconstruct_v3 =
  blastReconstruct.reconstructWithMeasuredTimedDetailedV3

val reconstruct_v3_using_transition =
  blastReconstruct.reconstructWithMeasuredTimedDetailedV3UsingTransition

val reconstruct_v4 =
  blastReconstruct.reconstructWithMeasuredTimedDetailedV4

val reconstruct_v4_using_transition =
  blastReconstruct.reconstructWithMeasuredTimedDetailedV4UsingTransition

fun same_reconstruction_result (goal : Abbrev.goal) (left, right) =
  case (left, right) of
      (SOME ([], left_validation), SOME ([], right_validation)) =>
        let
          val left_theorem = left_validation []
          val right_theorem = right_validation []
        in
          Term.aconv (concl left_theorem) (#2 goal) andalso
          Term.aconv (concl right_theorem) (#2 goal) andalso
          ListPair.allEq (fn (left, right) => Term.aconv left right)
            (hyp left_theorem, hyp right_theorem)
        end
    | (NONE, NONE) => true
    | _ => false

fun same_measured_reconstruction goal
      (left : blastReconstruct.measured_result,
       right : blastReconstruct.measured_result) =
  #completion left = #completion right andalso
  #current_phase left = #current_phase right andalso
  #statistics left = #statistics right andalso
  same_reconstruction_result goal (#result left, #result right)

fun same_outer_reconstruction_statistics
      (left : blastReconstruct.statistics,
       right : blastReconstruct.detailed_statistics) =
  #cooperative_checkpoints right =
    #cooperative_checkpoints left + #stored_rule_checkpoints right andalso
  #phase_entries left = #phase_entries right andalso
  #phase_exits left = #phase_exits right andalso
  #replay_recursions left = #replay_recursions right andalso
  #alternative_pulls left = #alternative_pulls right andalso
  #typed_steps left = #typed_steps right andalso
  #hyp_subst_steps left = #hyp_subst_steps right andalso
  #close_assume_steps left = #close_assume_steps right andalso
  #close_contradiction_steps left =
    #close_contradiction_steps right andalso
  #safe_rule_steps left = #safe_rule_steps right andalso
  #defer_goal_steps left = #defer_goal_steps right andalso
  #unsafe_rule_steps left = #unsafe_rule_steps right andalso
  #stored_rule_setups left = #stored_rule_setups right andalso
  #stored_rule_transitions left = #stored_rule_transitions right andalso
  #duplicate_child_moves left = #duplicate_child_moves right andalso
  #finish_open_goal_checks left = #finish_open_goal_checks right andalso
  #grounding_attempts left = #grounding_attempts right andalso
  #kernel_replay_attempts left = #kernel_replay_attempts right andalso
  #finish_residual_goal_checks left =
    #finish_residual_goal_checks right

fun same_detailed_reconstruction goal
      (left : blastReconstruct.detailed_measured_result,
       right : blastReconstruct.detailed_measured_result) =
  #completion left = #completion right andalso
  #current_phase left = #current_phase right andalso
  #current_stored_rule left = #current_stored_rule right andalso
  #statistics left = #statistics right andalso
  same_reconstruction_result goal (#result left, #result right)

fun same_timed_reconstruction goal
      (left : blastReconstruct.timed_detailed_measured_result,
       right : blastReconstruct.timed_detailed_measured_result) =
  #completion left = #completion right andalso
  #current_phase left = #current_phase right andalso
  #current_stored_rule left = #current_stored_rule right andalso
  #statistics left = #statistics right andalso
  #classical_times left = #classical_times right andalso
  #attempt_wall_time left = #attempt_wall_time right andalso
  same_reconstruction_result goal (#result left, #result right)

fun same_v2_reconstruction goal
      (left : blastReconstruct.timed_detailed_measured_result_v2,
       right : blastReconstruct.timed_detailed_measured_result_v2) =
  same_timed_reconstruction goal (#base left, #base right) andalso
  #minor_unification_times left = #minor_unification_times right andalso
  #outer_reconstruction_times left = #outer_reconstruction_times right

fun same_v3_reconstruction goal
      (left : blastReconstruct.timed_detailed_measured_result_v3,
       right : blastReconstruct.timed_detailed_measured_result_v3) =
  same_v2_reconstruction goal (#base left, #base right) andalso
  #minor_unification_times left = #minor_unification_times right andalso
  #alternative_pull_times left = #alternative_pull_times right

fun same_v4_reconstruction goal
      (left : blastReconstruct.timed_detailed_measured_result_v4,
       right : blastReconstruct.timed_detailed_measured_result_v4) =
  same_v2_reconstruction goal (#base left, #base right) andalso
  #minor_unification_times left = #minor_unification_times right andalso
  #alternative_pull_times left = #alternative_pull_times right

fun exact_static_prefix_counts
      (statistics : blastReconstruct.detailed_statistics) =
  #typed_steps statistics = 3 andalso
  #safe_rule_steps statistics = 1 andalso
  #close_assume_steps statistics = 2 andalso
  #stored_rule_setups statistics = 1 andalso
  #stored_rule_transitions statistics = 1 andalso
  #stored_rule_attempt_selections statistics = 1 andalso
  #stored_rule_freshening_setups statistics = 1 andalso
  #stored_rule_minor_unifications statistics = 1 andalso
  #stored_rule_major_unifications statistics = 0 andalso
  #stored_rule_instantiations statistics = 1 andalso
  #stored_rule_child_store_constructions statistics = 1 andalso
  #stored_rule_direct_result_constructions statistics = 1 andalso
  #stored_rule_lazy_yields statistics = 1 andalso
  #stored_rule_direct_child_replacements statistics = 1 andalso
  #stored_rule_replay_record_constructions statistics = 1 andalso
  #stored_rule_record_insertions statistics = 1 andalso
  #stored_rule_intro_attempts statistics = 1 andalso
  #stored_rule_elim_attempts statistics = 0 andalso
  #stored_rule_safe_attempts statistics = 1 andalso
  #stored_rule_unsafe_attempts statistics = 0 andalso
  #grounding_attempts statistics = 1 andalso
  #kernel_replay_attempts statistics = 1

val _ =
  test
    ("static-prefix tableau has all reconstruction API parity",
     fn () =>
       let
         val p = mk_var ("static_reconstruct_p", bool)
         val x = mk_var ("static_reconstruct_x", bool)
         val c = mk_var ("static_reconstruct_C", bool --> bool)
         val g = mk_var ("static_reconstruct_G", bool --> bool)
         val structured =
           mk_forall
             (x, mk_imp (mk_comb (c, x), mk_comb (g, x)))
         val goal = ([p, structured], mk_conj (p, structured))
         val search_cs = clasetLib.the_claset ()
         val empty_cs = clasetLib.empty_cs
         val proof =
           case blastSearch.tryGoal search_cs 1 goal of
               SOME value => value
             | NONE => raise Fail "static-prefix tableau"
         val controls = {observe = NONE, stop = fn () => false}
         fun detailed_controls () =
           {clock = reconstruction_ticking_clock (),
            observe = NONE, observe_stored_rule = NONE,
            stop = fn () => false}
         fun kernel_replay grounded input =
           Tactical.VALID (clasetReplay.REPLAY_TAC grounded) input
         val v2_kernel_calls = ref 0
         val v3_kernel_calls = ref 0
         val v4_kernel_calls = ref 0
         fun observed_kernel calls grounded input =
           (calls := !calls + 1;
            kernel_replay grounded input)
         val v3_transition_calls = ref 0
         val v4_transition_calls = ref 0
         fun transition_v3 sequence =
           (v3_transition_calls := !v3_transition_calls + 1;
            clasetStep.timed_rule_cases_v3 sequence)
         fun transition_v4 sequence =
           (v4_transition_calls := !v4_transition_calls + 1;
            clasetStep.timed_rule_cases_v4 sequence)
         val r0_with =
           blastReconstruct.reconstructWith empty_cs goal proof
         val r0_empty = blastReconstruct.reconstruct goal proof
         val r1_with =
           blastReconstruct.reconstructWithMeasured controls
             empty_cs goal proof
         val r1_empty =
           blastReconstruct.reconstructMeasured controls goal proof
         val detailed =
           {observe = NONE, observe_stored_rule = NONE,
            stop = fn () => false}
         val r2_with =
           blastReconstruct.reconstructWithMeasuredDetailed detailed
             empty_cs goal proof
         val r2_empty =
           blastReconstruct.reconstructMeasuredDetailed detailed goal proof
         val r3_with =
           blastReconstruct.reconstructWithMeasuredTimedDetailed
             (detailed_controls ()) empty_cs goal proof
         val r3_empty =
           blastReconstruct.reconstructMeasuredTimedDetailed
             (detailed_controls ()) goal proof
         val r4_with =
           blastReconstruct.reconstructWithMeasuredTimedDetailedV2
             (detailed_controls ()) empty_cs goal proof
         val r4_kernel =
           blastReconstruct.reconstructWithMeasuredTimedDetailedV2UsingKernel
             {clock = reconstruction_ticking_clock (),
              kernel_replay = observed_kernel v2_kernel_calls,
              observe = NONE,
              observe_stored_rule = NONE, stop = fn () => false}
             empty_cs goal proof
         val r4_empty =
           blastReconstruct.reconstructMeasuredTimedDetailedV2
             (detailed_controls ()) goal proof
         val r5_with =
           blastReconstruct.reconstructWithMeasuredTimedDetailedV3
             (detailed_controls ()) empty_cs goal proof
         val r5_kernel =
           blastReconstruct.reconstructWithMeasuredTimedDetailedV3UsingKernel
             {clock = reconstruction_ticking_clock (),
              kernel_replay = observed_kernel v3_kernel_calls,
              observe = NONE,
              observe_stored_rule = NONE, stop = fn () => false}
             empty_cs goal proof
         val r5_transition =
           reconstruct_v3_using_transition
             {clock = reconstruction_ticking_clock (),
              kernel_replay = kernel_replay,
              transition = transition_v3, observe = NONE,
              observe_stored_rule = NONE, stop = fn () => false}
             empty_cs goal proof
         val r5_empty =
           blastReconstruct.reconstructMeasuredTimedDetailedV3
             (detailed_controls ()) goal proof
         val r6_with =
           blastReconstruct.reconstructWithMeasuredTimedDetailedV4
             (detailed_controls ()) empty_cs goal proof
         val r6_kernel =
           blastReconstruct.reconstructWithMeasuredTimedDetailedV4UsingKernel
             {clock = reconstruction_ticking_clock (),
              kernel_replay = observed_kernel v4_kernel_calls,
              observe = NONE,
              observe_stored_rule = NONE, stop = fn () => false}
             empty_cs goal proof
         val r6_transition =
           reconstruct_v4_using_transition
             {clock = reconstruction_ticking_clock (),
              kernel_replay = kernel_replay,
              transition = transition_v4, observe = NONE,
              observe_stored_rule = NONE, stop = fn () => false}
             empty_cs goal proof
         val r6_empty =
           blastReconstruct.reconstructMeasuredTimedDetailedV4
             (detailed_controls ()) goal proof

         fun result_ok (SOME ([], validation)) =
               (ignore (validation []); true)
           | result_ok _ = false
         fun timed_ok
               (report :
                  blastReconstruct.timed_detailed_measured_result) =
           #completion report = blastReconstruct.Completed andalso
           result_ok (#result report)
         val timed_reports =
           [r3_with, r3_empty,
            #base r4_with, #base r4_kernel, #base r4_empty,
            #base (#base r5_with), #base (#base r5_kernel),
            #base (#base r5_transition), #base (#base r5_empty),
            #base (#base r6_with), #base (#base r6_kernel),
            #base (#base r6_transition), #base (#base r6_empty)]
         val r3_times = #classical_times r3_with
         val r5_pulls = #alternative_pull_times r5_with
         val r6_pulls = #alternative_pull_times r6_with
         fun phase_sum
               (times : blastReconstruct.classical_phase_times) =
           List.foldl Time.+ Time.zeroTime
             [#attempt_selection_time times,
              #freshening_setup_time times,
              #minor_unification_time times,
              #elimination_major_unification_time times,
              #rule_instantiation_time times,
              #child_store_construction_time times,
              #direct_result_construction_time times,
              #lazy_result_yield_time times,
              #direct_child_replacement_time times,
              #replay_record_construction_time times,
              #record_insertion_time times]
         fun check name condition =
           if condition then true
           else (print ("\nreconstruction parity: " ^ name ^ "\n"); false)
       in
         check "script" (length (#script proof) = 3) andalso
         check "r0 results" (result_ok r0_with andalso result_ok r0_empty)
         andalso check "r0 pair"
           (same_reconstruction_result goal (r0_with, r0_empty)) andalso
         check "r1 pair"
           (same_measured_reconstruction goal (r1_with, r1_empty)) andalso
         check "r2 pair"
           (same_detailed_reconstruction goal (r2_with, r2_empty)) andalso
         check "r3 pair"
           (same_timed_reconstruction goal (r3_with, r3_empty)) andalso
         check "r4 empty" (same_v2_reconstruction goal
           (r4_with, r4_empty)) andalso
         check "r4 kernel" (same_v2_reconstruction goal
           (r4_with, r4_kernel)) andalso
         check "r5 empty" (same_v3_reconstruction goal
           (r5_with, r5_empty)) andalso
         check "r5 kernel" (same_v3_reconstruction goal
           (r5_with, r5_kernel)) andalso
         check "r5 transition" (same_v3_reconstruction goal
           (r5_with, r5_transition)) andalso
         check "r6 empty" (same_v4_reconstruction goal
           (r6_with, r6_empty)) andalso
         check "r6 kernel" (same_v4_reconstruction goal
           (r6_with, r6_kernel)) andalso
         check "r6 transition" (same_v4_reconstruction goal
           (r6_with, r6_transition)) andalso
         check "outer current"
           (#completion r1_with = blastReconstruct.Completed andalso
            #current_phase r1_with = #current_phase r1_empty andalso
            #current_phase r1_with = #current_phase r2_with) andalso
         check "outer statistics"
           (same_outer_reconstruction_statistics
             (#statistics r1_with, #statistics r2_with)) andalso
         check "detailed terminal"
           (#current_stored_rule r2_with = #current_stored_rule r3_with
            andalso #statistics r2_with = #statistics r3_with) andalso
         check "exact owner counts"
           (exact_static_prefix_counts (#statistics r2_with)) andalso
         check "timed results" (List.all timed_ok timed_reports) andalso
         check "timed owner counts"
           (List.all (exact_static_prefix_counts o #statistics)
             timed_reports) andalso
         check "timed statistics"
           (List.all
             (fn report => #statistics report = #statistics r2_with)
             timed_reports) andalso
         check "timed terminal"
           (List.all
             (fn report =>
               #current_phase report = #current_phase r2_with andalso
               #current_stored_rule report = #current_stored_rule r2_with)
             timed_reports) andalso
         check "phase sum"
           (phase_sum r3_times = #classical_time r3_times) andalso
         check "v3 pulls"
           (#classical_elapsed_snapshots r5_pulls =
              2 * (#completed_pulls r5_pulls + #failed_pulls r5_pulls +
                   #interrupted_pulls r5_pulls) andalso
            #sequence_statistics_reads r5_pulls > 0) andalso
         check "v4 pulls"
           (#classical_elapsed_snapshots r6_pulls =
              2 * (#completed_pulls r6_pulls + #failed_pulls r6_pulls +
                   #interrupted_pulls r6_pulls) andalso
            #sequence_statistics_reads r6_pulls = 0 andalso
            #summary_statistics_reads r6_pulls = 1 andalso
            #retained_trace_allocations r6_pulls = 0) andalso
         check "kernel seams"
           (!v2_kernel_calls = 1 andalso !v3_kernel_calls = 1 andalso
            !v4_kernel_calls = 1) andalso
         check "transition seams"
           (!v3_transition_calls = 1 andalso !v4_transition_calls = 1)
       end)

val _ =
  test
    ("quantified stored major reaches every reconstruction seam",
     fn () =>
       let
         val outer = mk_var ("quantified_reconstruct_x", Type.ind)
         val inner = mk_var ("quantified_reconstruct_y", Type.ind)
         val predicate =
           mk_var
             ("quantified_reconstruct_R",
              Type.ind --> Type.ind --> bool)
         val marker =
           mk_var
             ("quantified_reconstruct_S", Type.ind --> bool)
         val nested =
           mk_forall
             (inner,
              Term.list_mk_comb (predicate, [outer, inner]))
         val source =
           mk_forall
             (outer, mk_conj (nested, mk_comb (marker, outer)))
         val target = mk_forall (inner, mk_comb (marker, inner))
         val goal = ([source], target)
         val cs = clasetLib.the_claset ()
         val proof =
           case blastSearch.tryGoal cs 3 goal of
               SOME result => result
             | NONE => raise Fail "quantified reconstruction tableau"
         val controls = {observe = NONE, stop = fn () => false}
         fun detailed_controls () =
           {clock = reconstruction_ticking_clock (),
            observe = NONE, observe_stored_rule = NONE,
            stop = fn () => false}
         fun kernel grounded input =
           Tactical.VALID (clasetReplay.REPLAY_TAC grounded) input
         fun v3_transition sequence =
           clasetStep.timed_rule_cases_v3 sequence
         fun v4_transition sequence =
           clasetStep.timed_rule_cases_v4 sequence
         val r0_with =
           blastReconstruct.reconstructWith cs goal proof
         val r0_empty = blastReconstruct.reconstruct goal proof
         val r1_with =
           blastReconstruct.reconstructWithMeasured controls cs goal proof
         val r1_empty =
           blastReconstruct.reconstructMeasured controls goal proof
         val detailed =
           {observe = NONE, observe_stored_rule = NONE,
            stop = fn () => false}
         val r2_with =
           blastReconstruct.reconstructWithMeasuredDetailed detailed
             cs goal proof
         val r2_empty =
           blastReconstruct.reconstructMeasuredDetailed detailed goal proof
         val r3_with =
           blastReconstruct.reconstructWithMeasuredTimedDetailed
             (detailed_controls ()) cs goal proof
         val r3_empty =
           blastReconstruct.reconstructMeasuredTimedDetailed
             (detailed_controls ()) goal proof
         val r4_with =
           blastReconstruct.reconstructWithMeasuredTimedDetailedV2
             (detailed_controls ()) cs goal proof
         val r4_kernel =
           blastReconstruct.reconstructWithMeasuredTimedDetailedV2UsingKernel
             {clock = reconstruction_ticking_clock (),
              kernel_replay = kernel, observe = NONE,
              observe_stored_rule = NONE, stop = fn () => false}
             cs goal proof
         val r4_empty =
           blastReconstruct.reconstructMeasuredTimedDetailedV2
             (detailed_controls ()) goal proof
         val r5_with =
           blastReconstruct.reconstructWithMeasuredTimedDetailedV3
             (detailed_controls ()) cs goal proof
         val r5_kernel =
           blastReconstruct.reconstructWithMeasuredTimedDetailedV3UsingKernel
             {clock = reconstruction_ticking_clock (),
              kernel_replay = kernel, observe = NONE,
              observe_stored_rule = NONE, stop = fn () => false}
             cs goal proof
         val r5_transition =
           reconstruct_v3_using_transition
             {clock = reconstruction_ticking_clock (),
              kernel_replay = kernel, transition = v3_transition,
              observe = NONE, observe_stored_rule = NONE,
              stop = fn () => false}
             cs goal proof
         val r5_empty =
           blastReconstruct.reconstructMeasuredTimedDetailedV3
             (detailed_controls ()) goal proof
         val r6_with =
           blastReconstruct.reconstructWithMeasuredTimedDetailedV4
             (detailed_controls ()) cs goal proof
         val r6_kernel =
           blastReconstruct.reconstructWithMeasuredTimedDetailedV4UsingKernel
             {clock = reconstruction_ticking_clock (),
              kernel_replay = kernel, observe = NONE,
              observe_stored_rule = NONE, stop = fn () => false}
             cs goal proof
         val r6_transition =
           reconstruct_v4_using_transition
             {clock = reconstruction_ticking_clock (),
              kernel_replay = kernel, transition = v4_transition,
              observe = NONE, observe_stored_rule = NONE,
              stop = fn () => false}
             cs goal proof
         val r6_empty =
           blastReconstruct.reconstructMeasuredTimedDetailedV4
             (detailed_controls ()) goal proof
         val results =
           [r0_with, r0_empty, #result r1_with, #result r1_empty,
            #result r2_with, #result r2_empty,
            #result r3_with, #result r3_empty,
            #result (#base r4_with), #result (#base r4_kernel),
            #result (#base r4_empty),
            #result (#base (#base r5_with)),
            #result (#base (#base r5_kernel)),
            #result (#base (#base r5_transition)),
            #result (#base (#base r5_empty)),
            #result (#base (#base r6_with)),
            #result (#base (#base r6_kernel)),
            #result (#base (#base r6_transition)),
            #result (#base (#base r6_empty))]
         fun exact (SOME ([], validation)) =
               let val theorem = validation []
               in
                 Term.aconv (concl theorem) target andalso
                 HOLset.equal
                   (Thm.hypset theorem,
                    HOLset.fromList Term.compare [source])
               end
           | exact _ = false
       in
         length (#script proof) = 5 andalso
         length results = 19 andalso List.all exact results
       end)

fun same_fine_v3_v4
      (left : blastReconstruct.minor_unification_times_v3)
      (right : blastReconstruct.minor_unification_times_v4) =
  #calls left = #calls right andalso
  #failures left = #failures right andalso
  #normalization_setup_events left = #normalization_setup_events right
  andalso #persistent_store_lookup_walk_events left =
    #persistent_store_lookup_walk_events right andalso
  #structural_decomposition_recursion_events left =
    #structural_decomposition_recursion_events right andalso
  #pattern_occurs_allow_decision_events left =
    #pattern_occurs_allow_decision_events right andalso
  #persistent_binding_update_events left =
    #persistent_binding_update_events right andalso
  #binding_operation_failures left = #binding_operation_failures right
  andalso #traversal_other_events left = #traversal_other_events right
  andalso #normalization_setup_time left = #normalization_setup_time right
  andalso #persistent_store_lookup_walk_time left =
    #persistent_store_lookup_walk_time right andalso
  #structural_decomposition_recursion_time left =
    #structural_decomposition_recursion_time right andalso
  #pattern_occurs_allow_decision_time left =
    #pattern_occurs_allow_decision_time right andalso
  #persistent_binding_update_time left =
    #persistent_binding_update_time right andalso
  #traversal_other_time left = #traversal_other_time right andalso
  #traversal_decomposition_binding_time left =
    #traversal_decomposition_binding_time right andalso
  #failure_cleanup_time left = #failure_cleanup_time right andalso
  #minor_unification_time left = #minor_unification_time right andalso
  #max_normalization_setup_time left =
    #max_normalization_setup_time right andalso
  #max_persistent_store_lookup_walk_time left =
    #max_persistent_store_lookup_walk_time right andalso
  #max_structural_decomposition_recursion_time left =
    #max_structural_decomposition_recursion_time right andalso
  #max_pattern_occurs_allow_decision_time left =
    #max_pattern_occurs_allow_decision_time right andalso
  #max_persistent_binding_update_time left =
    #max_persistent_binding_update_time right andalso
  #max_traversal_other_time left = #max_traversal_other_time right andalso
  #max_traversal_decomposition_binding_time left =
    #max_traversal_decomposition_binding_time right andalso
  #max_failure_cleanup_time left = #max_failure_cleanup_time right andalso
  #max_minor_unification_time left = #max_minor_unification_time right

fun same_pulls_v3_v4
      (left : blastReconstruct.alternative_pull_times)
      (right : blastReconstruct.alternative_pull_times_v4) =
  #completed_pulls left = #completed_pulls right andalso
  #failed_pulls left = #failed_pulls right andalso
  #interrupted_pulls left = #interrupted_pulls right andalso
  #classical_elapsed_snapshots left = #classical_elapsed_snapshots right
  andalso #completed_pull_time left = #completed_pull_time right andalso
  #failed_pull_time left = #failed_pull_time right andalso
  #interrupted_pull_time left = #interrupted_pull_time right andalso
  #alternative_pull_time left = #alternative_pull_time right andalso
  #alternative_residual_time left = #alternative_residual_time right
  andalso #max_completed_pull_time left = #max_completed_pull_time right
  andalso #max_failed_pull_time left = #max_failed_pull_time right andalso
  #max_interrupted_pull_time left = #max_interrupted_pull_time right
  andalso #max_alternative_pull_time left =
    #max_alternative_pull_time right

fun classical_phase_time_sum
      (times : blastReconstruct.classical_phase_times) =
  List.foldl Time.+ Time.zeroTime
    [#attempt_selection_time times,
     #freshening_setup_time times,
     #minor_unification_time times,
     #elimination_major_unification_time times,
     #rule_instantiation_time times,
     #child_store_construction_time times,
     #direct_result_construction_time times,
     #lazy_result_yield_time times,
     #direct_child_replacement_time times,
     #replay_record_construction_time times,
     #record_insertion_time times]

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
    ("measured reconstruction reports exact completed close counters",
     fn () =>
       let
         val p = mk_var ("measured_close_p", bool)
         val goal = ([p], p)
       in
         case blastSearch.tryGoal clasetLib.empty_cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 val report =
                   blastReconstruct.reconstructMeasured
                     {observe = NONE, stop = fn () => false}
                     goal proof
                 val statistics = #statistics report
               in
                 #completion report = blastReconstruct.Completed andalso
                 legacy_reconstruction_result_shape report andalso
                 Option.isSome (#result report) andalso
                 #current_phase report =
                   SOME
                     {boundary = blastReconstruct.Exit,
                      phase = blastReconstruct.ReplayRecursion} andalso
                 #cooperative_checkpoints statistics = 16 andalso
                 #phase_entries statistics = 8 andalso
                 #phase_exits statistics = 8 andalso
                 #replay_recursions statistics = 2 andalso
                 #alternative_pulls statistics = 1 andalso
                 #typed_steps statistics = 1 andalso
                 #close_assume_steps statistics = 1 andalso
                 #finish_open_goal_checks statistics = 1 andalso
                 #grounding_attempts statistics = 1 andalso
                 #kernel_replay_attempts statistics = 1 andalso
                 #finish_residual_goal_checks statistics = 1
               end
       end)

val _ =
  test
    ("measured close-contradiction has exact kernel-valid parity",
     fn () =>
       let
         val alpha = Type.mk_vartype "'measured_contradiction"
         val x = mk_var ("measured_contradiction_x", alpha)
         val a = mk_var ("measured_contradiction_a", alpha)
         val z = mk_var ("measured_contradiction_z", alpha)
         val f =
           mk_var
             ("measured_contradiction_f", alpha --> bool)
         val p = mk_var ("measured_contradiction_p", bool)
         val eta = mk_abs (x, mk_comb (f, x))
         val q = mk_eq (eta, f)
         val target = mk_comb (mk_abs (z, q), a)
         val goal = ([p, mk_neg p], target)
         fun exact theorem =
           Term.term_eq (concl theorem) (#2 goal) andalso
           HOLset.equal
             (Thm.hypset theorem,
              HOLset.fromList Term.compare (#1 goal))
       in
         case blastSearch.tryGoal clasetLib.empty_cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 val ordinary = blastReconstruct.reconstruct goal proof
                 val report =
                   blastReconstruct.reconstructMeasured
                     {observe = NONE, stop = fn () => false}
                     goal proof
                 val statistics = #statistics report
               in
                 case (ordinary, #completion report, #result report) of
                     (SOME ([], ordinary_validation),
                      blastReconstruct.Completed,
                      SOME ([], measured_validation)) =>
                       has_step
                         (fn blastSearch.CloseContradiction _ => true
                           | _ => false) proof andalso
                       #cooperative_checkpoints statistics = 16 andalso
                       #phase_entries statistics = 8 andalso
                       #phase_exits statistics = 8 andalso
                       #replay_recursions statistics = 2 andalso
                       #alternative_pulls statistics = 1 andalso
                       #typed_steps statistics = 1 andalso
                       #close_assume_steps statistics = 0 andalso
                       #close_contradiction_steps statistics = 1 andalso
                       #finish_open_goal_checks statistics = 1 andalso
                       #grounding_attempts statistics = 1 andalso
                       #kernel_replay_attempts statistics = 1 andalso
                       #finish_residual_goal_checks statistics = 1 andalso
                       exact (ordinary_validation []) andalso
                       exact (measured_validation [])
                   | _ => false
               end
       end)

val _ =
  test
    ("measured reconstruction interruption returns its exact boundary",
     fn () =>
       let
         val p = mk_var ("measured_interrupt_p", bool)
         val goal = ([p], p)
       in
         case blastSearch.tryGoal clasetLib.empty_cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 val report =
                   blastReconstruct.reconstructMeasured
                     {observe = NONE, stop = fn () => true}
                     goal proof
                 val statistics = #statistics report
               in
                 #completion report = blastReconstruct.Interrupted andalso
                 not (Option.isSome (#result report)) andalso
                 #current_phase report =
                   SOME
                     {boundary = blastReconstruct.Enter,
                      phase = blastReconstruct.ReplayRecursion} andalso
                 #cooperative_checkpoints statistics = 1 andalso
                 #phase_entries statistics = 1 andalso
                 #phase_exits statistics = 0 andalso
                 #replay_recursions statistics = 1
               end
       end)

val _ =
  test
    ("measured reconstruction does not swallow stop HOL_ERR values",
     fn () =>
       let
         val p = mk_var ("measured_exception_p", bool)
         val goal = ([p], p)
       in
         case blastSearch.tryGoal clasetLib.empty_cs 0 goal of
             NONE => false
           | SOME proof =>
               ((ignore
                   (blastReconstruct.reconstructMeasured
                     {observe = NONE,
                      stop =
                        fn () =>
                          raise mk_HOL_ERR "measured-stop-sentinel"
                            "stop" "propagate"}
                     goal proof);
                 false)
                handle HOL_ERR error =>
                         Feedback.top_structure_of error =
                           "measured-stop-sentinel"
                     | _ => false)
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
    ("measured stored replay exposes transition entry to observers",
     fn () =>
       let
         val p = mk_var ("measured_stored_p", bool)
         val q = mk_var ("measured_stored_q", bool)
         val goal = ([mk_conj (p, q)], p)
         val cs =
           clasetLib.add_selims
             [("andE", CONJ_ELIM_THM)] clasetLib.empty_cs
         val stop_now = ref false
         fun observe
               ({boundary, phase} : blastReconstruct.observation) =
           case (boundary, phase) of
               (blastReconstruct.Enter,
                blastReconstruct.StoredRuleTransition) =>
                  stop_now := true
             | _ => ()
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 val report =
                   blastReconstruct.reconstructWithMeasured
                     {observe = SOME observe, stop = fn () => !stop_now}
                     cs goal proof
                 val statistics = #statistics report
               in
                 #completion report = blastReconstruct.Interrupted andalso
                 #current_phase report =
                   SOME
                     {boundary = blastReconstruct.Enter,
                      phase = blastReconstruct.StoredRuleTransition} andalso
                 #safe_rule_steps statistics = 1 andalso
                 #stored_rule_setups statistics = 1 andalso
                 #stored_rule_transitions statistics = 1
               end
       end)

val _ =
  test
    ("detailed stored replay has exact completed parity and counters",
     fn () =>
       let
         val p = mk_var ("measured_detailed_p", bool)
         val q = mk_var ("measured_detailed_q", bool)
         val goal = ([mk_conj (p, q)], p)
         val cs =
           clasetLib.add_selims
             [("andE", CONJ_ELIM_THM)] clasetLib.empty_cs
         val observations =
           ref ([] : blastReconstruct.stored_rule_observation list)
         fun observe event = observations := event :: !observations
         val legacy_polls = ref 0
         val detailed_polls = ref 0
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 val ordinary =
                   blastReconstruct.reconstructWith cs goal proof
                 val legacy =
                   blastReconstruct.reconstructWithMeasured
                     {observe = NONE,
                      stop =
                        fn () =>
                          (legacy_polls := !legacy_polls + 1; false)}
                     cs goal proof
                 val measured =
                   blastReconstruct.reconstructWithMeasuredDetailed
                     {observe = NONE,
                      observe_stored_rule = SOME observe,
                      stop =
                        fn () =>
                          (detailed_polls := !detailed_polls + 1; false)}
                     cs goal proof
                 val legacy_statistics = #statistics legacy
                 val statistics = #statistics measured
               in
                 case (ordinary, #completion measured,
                       #result measured,
                       #current_stored_rule measured) of
                     (SOME ([], ordinary_validation),
                      blastReconstruct.Completed,
                      SOME ([], measured_validation),
                      SOME
                        {script_position = 1,
                         step_kind = blastReconstruct.SafeRuleStep,
                         duplicate = false,
                         rule =
                           {boundary = clasetStep.RuleExit,
                            phase = clasetStep.RecordInsertion,
                            goal_position = 1,
                            rule_kind = clasetStep.ElimRule,
                            assumption_position = SOME 1}}) =>
                       length (!observations) = 22 andalso
                       legacy_reconstruction_result_shape legacy andalso
                       #completion legacy = blastReconstruct.Completed
                       andalso
                       Option.isSome (#result legacy) andalso
                       !legacy_polls =
                         #cooperative_checkpoints legacy_statistics
                       andalso
                       !detailed_polls =
                         #cooperative_checkpoints statistics andalso
                       #cooperative_checkpoints statistics =
                         #cooperative_checkpoints legacy_statistics +
                         #stored_rule_checkpoints statistics andalso
                       #phase_entries statistics =
                         #phase_entries legacy_statistics andalso
                       #phase_exits statistics =
                         #phase_exits legacy_statistics andalso
                       #stored_rule_checkpoints statistics = 22 andalso
                       #stored_rule_phase_entries statistics = 11 andalso
                       #stored_rule_phase_exits statistics = 11 andalso
                       #stored_rule_attempt_selections statistics = 1
                       andalso
                       #stored_rule_freshening_setups statistics = 1
                       andalso
                       #stored_rule_minor_unifications statistics = 1
                       andalso
                       #stored_rule_major_unifications statistics = 1
                       andalso
                       #stored_rule_instantiations statistics = 1
                       andalso
                       #stored_rule_child_store_constructions statistics = 1
                       andalso
                       #stored_rule_direct_result_constructions statistics = 1
                       andalso
                       #stored_rule_lazy_yields statistics = 1 andalso
                       #stored_rule_direct_child_replacements statistics = 1
                       andalso
                       #stored_rule_replay_record_constructions statistics = 1
                       andalso
                       #stored_rule_record_insertions statistics = 1
                       andalso
                       #stored_rule_intro_attempts statistics = 0 andalso
                       #stored_rule_elim_attempts statistics = 1 andalso
                       #stored_rule_safe_attempts statistics = 1 andalso
                       #stored_rule_unsafe_attempts statistics = 0 andalso
                       (ignore (ordinary_validation []);
                        ignore (measured_validation []);
                        true)
                   | _ => false
               end
       end)

val _ =
  test
    ("timed detailed replay accounts exact selected alternative",
     fn () =>
       let
         val p = mk_var ("timed_detailed_p", bool)
         val q = mk_var ("timed_detailed_q", bool)
         val r = mk_var ("timed_detailed_r", bool)
         val goal = ([r, mk_conj (p, q)], p)
         val cs =
           clasetLib.add_selims
             [("timed-detailed-andE", CONJ_ELIM_THM)]
             clasetLib.empty_cs
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 val untimed_observations =
                   ref ([] : blastReconstruct.stored_rule_observation list)
                 val timed_observations =
                   ref ([] : blastReconstruct.stored_rule_observation list)
                 val untimed =
                   blastReconstruct.reconstructWithMeasuredDetailed
                     {observe = NONE,
                      observe_stored_rule =
                        SOME
                          (fn event =>
                            untimed_observations :=
                              event :: !untimed_observations),
                      stop = fn () => false}
                     cs goal proof
                 val timed =
                   blastReconstruct.reconstructWithMeasuredTimedDetailed
                     {clock = reconstruction_ticking_clock (),
                      observe = NONE,
                      observe_stored_rule =
                        SOME
                          (fn event =>
                            timed_observations :=
                              event :: !timed_observations),
                      stop = fn () => false}
                     cs goal proof
                 val statistics = #statistics timed
                 val times = #classical_times timed
               in
                 #completion untimed = #completion timed andalso
                 #completion timed = blastReconstruct.Completed andalso
                 #statistics untimed = statistics andalso
                 rev (!untimed_observations) =
                   rev (!timed_observations) andalso
                 (case (#result untimed, #result timed) of
                      (SOME ([], untimed_validation),
                       SOME ([], timed_validation)) =>
                        (ignore (untimed_validation []);
                         ignore (timed_validation []); true)
                    | _ => false) andalso
                 #stored_rule_attempt_selections statistics = 1 andalso
                 #stored_rule_major_unifications statistics = 1 andalso
                 #stored_rule_instantiations statistics = 1 andalso
                 #attempt_selection_time times = Time.fromSeconds 1
                 andalso
                 #freshening_setup_time times = Time.fromSeconds 1
                 andalso
                 #minor_unification_time times = Time.fromSeconds 1
                 andalso
                 #elimination_major_unification_time times =
                   Time.fromSeconds 1 andalso
                 #classical_time times = Time.fromSeconds 11 andalso
                 classical_phase_time_sum times =
                   #classical_time times andalso
                 #attempt_wall_time timed = Time.fromSeconds 23
               end
       end)

val _ =
  test
    ("timed detailed Enter and Exit stops preserve exact protocol",
     fn () =>
       let
         val p = mk_var ("timed_boundary_p", bool)
         val q = mk_var ("timed_boundary_q", bool)
         val goal = ([mk_conj (p, q)], p)
         val cs =
           clasetLib.add_selims
             [("timed-boundary-andE", CONJ_ELIM_THM)]
             clasetLib.empty_cs

         fun run cutoff =
           case blastSearch.tryGoal cs 0 goal of
               NONE => NONE
             | SOME proof =>
                 let
                   val stop_now = ref false
                   fun observe
                         ({rule = {boundary, phase, ...}, ...} :
                            blastReconstruct.stored_rule_observation) =
                     if boundary = cutoff andalso
                        phase = clasetStep.RuleInstantiation then
                       stop_now := true
                     else ()
                 in
                   SOME
                     (blastReconstruct.reconstructWithMeasuredTimedDetailed
                       {clock = reconstruction_ticking_clock (),
                        observe = NONE,
                        observe_stored_rule = SOME observe,
                        stop = fn () => !stop_now}
                       cs goal proof)
                 end
       in
         case (run clasetStep.RuleEnter, run clasetStep.RuleExit) of
             (SOME enter, SOME exit) =>
               let
                 val enter_statistics = #statistics enter
                 val exit_statistics = #statistics exit
                 val enter_times = #classical_times enter
                 val exit_times = #classical_times exit
               in
                 #completion enter = blastReconstruct.Interrupted
                 andalso
                 #completion exit = blastReconstruct.Interrupted andalso
                 not (Option.isSome (#result enter)) andalso
                 not (Option.isSome (#result exit)) andalso
                 #stored_rule_phase_entries enter_statistics = 5
                 andalso
                 #stored_rule_phase_exits enter_statistics = 4 andalso
                 #stored_rule_phase_entries exit_statistics = 5
                 andalso
                 #stored_rule_phase_exits exit_statistics = 5 andalso
                 #classical_time enter_times = Time.fromSeconds 4
                 andalso
                 #rule_instantiation_time enter_times =
                   Time.zeroTime andalso
                 #classical_time exit_times = Time.fromSeconds 5
                 andalso
                 #rule_instantiation_time exit_times =
                   Time.fromSeconds 1 andalso
                 #attempt_wall_time enter = Time.fromSeconds 9 andalso
                 #attempt_wall_time exit = Time.fromSeconds 11
               end
           | _ => false
       end)

val _ =
  test
    ("timed-v2 reconstruction is exclusive bounded and API-equivalent",
     fn () =>
       let
         val p = mk_var ("timed_v2_reconstruct_p", bool)
         val q = mk_var ("timed_v2_reconstruct_q", bool)
         val r = mk_var ("timed_v2_reconstruct_r", bool)
         val goal = ([r, mk_conj (p, q)], p)
         val cs =
           clasetLib.add_selims
             [("timed-v2-reconstruct-andE", CONJ_ELIM_THM)]
             clasetLib.empty_cs
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 val untimed_observations = ref []
                 val timed_observations = ref []
                 val untimed =
                   blastReconstruct.reconstructWithMeasuredDetailed
                     {observe = NONE,
                      observe_stored_rule =
                        SOME
                          (fn event =>
                            untimed_observations :=
                              event :: !untimed_observations),
                      stop = fn () => false}
                     cs goal proof
                 val timed =
                   blastReconstruct.reconstructWithMeasuredTimedDetailedV2
                     {clock = reconstruction_ticking_clock (),
                      observe = NONE,
                      observe_stored_rule =
                        SOME
                          (fn event =>
                            timed_observations :=
                              event :: !timed_observations),
                      stop = fn () => false}
                     cs goal proof
                 val base = #base timed
                 val classical = #classical_times base
                 val minor = #minor_unification_times timed
                 val outer = #outer_reconstruction_times timed
                 val minor_subtotal =
                   Time.+
                     (#normalization_setup_time minor,
                      Time.+
                        (#traversal_decomposition_binding_time minor,
                         #failure_cleanup_time minor))
                 val outer_subtotal =
                   Time.+
                     (#alternative_enumeration_time outer,
                      Time.+
                        (#replay_continuation_time outer,
                         #other_outer_time outer))
               in
                 #completion untimed = #completion base andalso
                 #statistics untimed = #statistics base andalso
                 rev (!untimed_observations) =
                   rev (!timed_observations) andalso
                 (case (#result untimed, #result base) of
                      (SOME ([], untimed_validation),
                       SOME ([], timed_validation)) =>
                        (ignore (untimed_validation []);
                         ignore (timed_validation []); true)
                    | _ => false) andalso
                 #calls minor =
                   #stored_rule_minor_unifications (#statistics base)
                 andalso
                 #failure_cleanup_time minor = Time.zeroTime andalso
                 minor_subtotal = #minor_unification_time minor andalso
                 #minor_unification_time minor =
                   #minor_unification_time classical andalso
                 classical_phase_time_sum classical =
                   #classical_time classical andalso
                 outer_subtotal = #outer_reconstruction_time outer
                 andalso
                 Time.+
                   (#outer_reconstruction_time outer,
                    #classical_time classical) =
                   #attempt_wall_time base andalso
                 not
                   (Time.< (#minor_unification_time minor,
                            #max_minor_unification_time minor))
               end
       end)

val _ =
  test
    ("timed-v2 interruption and callback exceptions retain boundaries",
     fn () =>
       let
         exception TimedV2Callback of int ref
         val sentinel = ref 149
         val p = mk_var ("timed_v2_interrupt_p", bool)
         val q = mk_var ("timed_v2_interrupt_q", bool)
         val goal = ([mk_conj (p, q)], p)
         val cs =
           clasetLib.add_selims
             [("timed-v2-interrupt-andE", CONJ_ELIM_THM)]
             clasetLib.empty_cs
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 val stop_now = ref false
                 fun cutoff
                       ({rule = {boundary, phase, ...}, ...} :
                          blastReconstruct.stored_rule_observation) =
                   if boundary = clasetStep.RuleEnter andalso
                      phase = clasetStep.RuleInstantiation then
                     stop_now := true
                   else ()
                 val interrupted =
                   blastReconstruct.reconstructWithMeasuredTimedDetailedV2
                     {clock = reconstruction_ticking_clock (),
                      observe = NONE, observe_stored_rule = SOME cutoff,
                      stop = fn () => !stop_now}
                     cs goal proof
                 val base = #base interrupted
                 val outer = #outer_reconstruction_times interrupted
                 val reconstruct_v2 =
                   blastReconstruct.reconstructWithMeasuredTimedDetailedV2
                 val exception_ok =
                   ((ignore
                       (reconstruct_v2
                          {clock = reconstruction_ticking_clock (),
                           observe = NONE,
                           observe_stored_rule =
                             SOME
                               (fn _ =>
                                 raise TimedV2Callback sentinel),
                           stop = fn () => false}
                          cs goal proof);
                     false)
                    handle TimedV2Callback actual => actual = sentinel
                         | _ => false)
               in
                 #completion base = blastReconstruct.Interrupted andalso
                 not (Option.isSome (#result base)) andalso
                 #current_phase base =
                   SOME
                     {boundary = blastReconstruct.Enter,
                      phase = blastReconstruct.AlternativeEnumeration}
                 andalso
                 #current_stored_rule base =
                   SOME
                     {script_position = 1,
                      step_kind = blastReconstruct.SafeRuleStep,
                      duplicate = false,
                      rule =
                        {boundary = clasetStep.RuleEnter,
                         phase = clasetStep.RuleInstantiation,
                         goal_position = 1,
                         rule_kind = clasetStep.ElimRule,
                         assumption_position = SOME 1}} andalso
                 Time.+
                   (#outer_reconstruction_time outer,
                    #classical_time (#classical_times base)) =
                 #attempt_wall_time base andalso exception_ok
               end
       end)

val _ =
  test
    ("timed-v3 Completed NONE pull and callback errors are exact",
     fn () =>
       let
         exception V3Callback of int ref
         val sentinel = ref 211
         val p = mk_var ("timed_v3_none_p", bool)
         val goal = ([], p)
         val proof : blastSearch.proof =
           {script = [blastSearch.CloseAssume {assumption = 1}],
            trace = [], depth = 0,
            branches_created = 0, branches_closed = 0,
            choices_pruned = 0}
         val report =
           blastReconstruct.reconstructMeasuredTimedDetailedV3
             {clock = reconstruction_ticking_clock (), observe = NONE,
              observe_stored_rule = NONE, stop = fn () => false}
             goal proof
         val base = #base (#base report)
         val outer = #outer_reconstruction_times (#base report)
         val pulls = #alternative_pull_times report

         fun raises callback =
           ((ignore
               (blastReconstruct.reconstructMeasuredTimedDetailedV3
                 callback goal proof);
             false)
            handle V3Callback actual => actual = sentinel
                 | _ => false)

         val observer_ok =
           raises
             {clock = reconstruction_ticking_clock (),
              observe =
                SOME
                  (fn {boundary, phase} =>
                    if boundary = blastReconstruct.Enter andalso
                       phase = blastReconstruct.AlternativeEnumeration
                    then raise V3Callback sentinel
                    else ()),
              observe_stored_rule = NONE, stop = fn () => false}
         val stop_ok =
           raises
             {clock = reconstruction_ticking_clock (), observe = NONE,
              observe_stored_rule = NONE,
              stop = fn () => raise V3Callback sentinel}
         val clock_ok =
           raises
             {clock = fn () => raise V3Callback sentinel,
              observe = NONE, observe_stored_rule = NONE,
              stop = fn () => false}
         val interrupt_ok =
           ((ignore
               (blastReconstruct.reconstructMeasuredTimedDetailedV3
                 {clock = reconstruction_ticking_clock (),
                  observe = SOME (fn _ => raise Interrupt),
                  observe_stored_rule = NONE, stop = fn () => false}
                 goal proof);
             false)
            handle Interrupt => true | _ => false)
         val readings =
           ref [Time.fromSeconds 2, Time.fromSeconds 1]
         fun backwards () =
           case !readings of
               [] => raise Fail "timed-v3 backwards clock exhausted"
             | value :: rest => (readings := rest; value)
         val backwards_ok =
           ((ignore
               (blastReconstruct.reconstructMeasuredTimedDetailedV3
                 {clock = backwards, observe = NONE,
                  observe_stored_rule = NONE, stop = fn () => false}
                 goal proof);
             false)
            handle HOL_ERR error =>
                     Feedback.top_structure_of error = "blastReconstruct"
                 | _ => false)
       in
         #completion base = blastReconstruct.Completed andalso
         not (Option.isSome (#result base)) andalso
         #completed_pulls pulls = 0 andalso
         #failed_pulls pulls = 1 andalso
         #interrupted_pulls pulls = 0 andalso
         #completed_pull_time pulls = Time.zeroTime andalso
         #failed_pull_time pulls = Time.fromSeconds 1 andalso
         #alternative_pull_time pulls = Time.fromSeconds 1 andalso
         #alternative_residual_time pulls = Time.zeroTime andalso
         #max_completed_pull_time pulls = Time.zeroTime andalso
         #max_failed_pull_time pulls = Time.fromSeconds 1 andalso
         #max_alternative_pull_time pulls = Time.fromSeconds 1 andalso
         #alternative_enumeration_time outer = Time.fromSeconds 1 andalso
         observer_ok andalso stop_ok andalso clock_ok andalso
         interrupt_ok andalso backwards_ok
       end)

val _ =
  test
    ("timed-v3 Alternative Enter and Exit stops classify exactly",
     fn () =>
       let
         val p = mk_var ("timed_v3_outer_stop_p", bool)
         val goal = ([p], p)
         val proof : blastSearch.proof =
           {script = [blastSearch.CloseAssume {assumption = 1}],
            trace = [], depth = 0,
            branches_created = 0, branches_closed = 0,
            choices_pruned = 0}

         fun run cutoff =
           let
             val stop_now = ref false
             fun observe {boundary, phase} =
               if phase = blastReconstruct.AlternativeEnumeration andalso
                  boundary = cutoff
               then stop_now := true
               else ()
           in
             blastReconstruct.reconstructMeasuredTimedDetailedV3
               {clock = reconstruction_ticking_clock (),
                observe = SOME observe, observe_stored_rule = NONE,
                stop = fn () => !stop_now}
               goal proof
           end

         val entered = run blastReconstruct.Enter
         val exited = run blastReconstruct.Exit
         val entered_pulls = #alternative_pull_times entered
         val exited_pulls = #alternative_pull_times exited
         val entered_base = #base (#base entered)
         val exited_base = #base (#base exited)

         exception ExitObserver of int ref
         val sentinel = ref 251
         val exit_callback_identity =
           ((ignore
               (blastReconstruct.reconstructMeasuredTimedDetailedV3
                 {clock = reconstruction_ticking_clock (),
                  observe =
                    SOME
                      (fn {boundary, phase} =>
                        if boundary = blastReconstruct.Exit andalso
                           phase =
                             blastReconstruct.AlternativeEnumeration
                        then raise ExitObserver sentinel
                        else ()),
                  observe_stored_rule = NONE, stop = fn () => false}
                 goal proof);
             false)
            handle ExitObserver actual => actual = sentinel
                 | _ => false)
       in
         #completion entered_base = blastReconstruct.Interrupted andalso
         #interrupted_pulls entered_pulls = 1 andalso
         #completed_pulls entered_pulls = 0 andalso
         #failed_pulls entered_pulls = 0 andalso
         #classical_elapsed_snapshots entered_pulls = 0 andalso
         #interrupted_pull_time entered_pulls = Time.zeroTime andalso
         #max_interrupted_pull_time entered_pulls = Time.zeroTime andalso
         #completion exited_base = blastReconstruct.Interrupted andalso
         #interrupted_pulls exited_pulls = 1 andalso
         #completed_pulls exited_pulls = 0 andalso
         #failed_pulls exited_pulls = 0 andalso
         #classical_elapsed_snapshots exited_pulls = 2 andalso
         #interrupted_pull_time exited_pulls = Time.fromSeconds 1 andalso
         #alternative_pull_time exited_pulls = Time.fromSeconds 1 andalso
         #max_interrupted_pull_time exited_pulls = Time.fromSeconds 1 andalso
         #max_alternative_pull_time exited_pulls = Time.fromSeconds 1 andalso
         exit_callback_identity
       end)

val _ =
  test
    ("timed-v3 transition failures retain replay policy and later success",
     fn () =>
       let
         exception OperationalTransition of int ref
         val sentinel = ref 263
         val p = mk_var ("timed_v3_transition_p", bool)
         val q = mk_var ("timed_v3_transition_q", bool)
         val goal = ([p, q], mk_conj (p, q))
         val cs =
           clasetLib.add_sintros
             [("timed-v3-transition-and", boolTheory.AND_INTRO_THM)]
             clasetLib.empty_cs
         val first = ref true
         fun transition sequence =
           if !first then
             (first := false; raise OperationalTransition sentinel)
           else clasetStep.timed_rule_cases_v3 sequence
         val reconstruct_transition =
           let
             open blastReconstruct
           in
             reconstructWithMeasuredTimedDetailedV3UsingTransition
           end
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 fun run () =
                   reconstruct_transition
                     {clock = reconstruction_ticking_clock (),
                      kernel_replay =
                        fn grounded =>
                          Tactical.VALID
                            (clasetReplay.REPLAY_TAC grounded),
                      transition = transition, observe = NONE,
                      observe_stored_rule = NONE,
                      stop = fn () => false}
                     cs goal proof
                 val failed = run ()
                 val succeeded = run ()
                 val failed_base = #base (#base failed)
                 val succeeded_base = #base (#base succeeded)
                 val failed_pulls = #alternative_pull_times failed
                 val succeeded_pulls = #alternative_pull_times succeeded
               in
                 not (!first) andalso
                 #completion failed_base = blastReconstruct.Completed andalso
                 not (Option.isSome (#result failed_base)) andalso
                 #failed_pulls failed_pulls = 1 andalso
                 #completed_pulls failed_pulls = 0 andalso
                 #classical_elapsed_snapshots failed_pulls = 2 andalso
                 #completion succeeded_base =
                   blastReconstruct.Completed andalso
                 Option.isSome (#result succeeded_base) andalso
                 #completed_pulls succeeded_pulls >= 1 andalso
                 #failed_pulls succeeded_pulls = 0
               end
       end)

val _ =
  test
    ("timed-v3 many sequences never scan statistics while pulling",
     fn () =>
       let
         val ps =
           List.tabulate
             (8, fn index =>
               mk_var ("timed_v3_many_" ^ Int.toString index, bool))
         fun conjunction [item] = item
           | conjunction (item :: rest) =
               mk_conj (item, conjunction rest)
           | conjunction [] = raise Fail "empty many-sequence fixture"
         val target = conjunction ps
         val goal = (ps, target)
         val cs =
           clasetLib.add_sintros
             [("timed-v3-many-and", boolTheory.AND_INTRO_THM)]
             clasetLib.empty_cs
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 val reads_were_zero = ref true
                 val observed_sequence_pulls = ref 0
                 fun transition sequence =
                   (observed_sequence_pulls := !observed_sequence_pulls + 1;
                    if clasetStep.timed_rule_statistics_reads_v3 sequence = 0
                    then ()
                    else reads_were_zero := false;
                    clasetStep.timed_rule_cases_v3 sequence)
                 val report =
                   let
                     open blastReconstruct
                   in
                     reconstructWithMeasuredTimedDetailedV3UsingTransition
                       {clock = reconstruction_ticking_clock (),
                        kernel_replay =
                          fn grounded =>
                            Tactical.VALID
                              (clasetReplay.REPLAY_TAC grounded),
                        transition = transition, observe = NONE,
                        observe_stored_rule = NONE,
                        stop = fn () => false}
                       cs goal proof
                   end
                 val base = #base (#base report)
                 val statistics = #statistics base
                 val pulls = #alternative_pull_times report
                 val sequences = #stored_rule_setups statistics
               in
                 sequences >= 7 andalso
                 !reads_were_zero andalso
                 !observed_sequence_pulls > 0 andalso
                 #alternative_pulls statistics >= sequences andalso
                 #classical_elapsed_snapshots pulls =
                   2 * #alternative_pulls statistics andalso
                 #sequence_statistics_reads pulls = 3 * sequences
               end
       end)

val _ =
  test
    ("bounded-v4 many sequences allocate and scan no retained trace",
     fn () =>
       let
         val ps =
           List.tabulate
             (16, fn index =>
               mk_var ("bounded_v4_many_" ^ Int.toString index, bool))
         fun conjunction [item] = item
           | conjunction (item :: rest) =
               mk_conj (item, conjunction rest)
           | conjunction [] = raise Fail "empty bounded-v4 fixture"
         val goal = (ps, conjunction ps)
         val cs =
           clasetLib.add_sintros
             [("bounded-v4-many-and", boolTheory.AND_INTRO_THM)]
             clasetLib.empty_cs
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 val bounded_during_pulls = ref true
                 val observed_pulls = ref 0
                 fun transition sequence =
                   let
                     val summary =
                       clasetStep.timed_rule_summary_of_v4 sequence
                     val _ = observed_pulls := !observed_pulls + 1
                     val _ =
                       if clasetStep.timed_rule_statistics_reads_v4
                            summary = 0 andalso
                          clasetStep.timed_rule_trace_allocations_v4
                            summary = 0
                       then ()
                       else bounded_during_pulls := false
                   in
                     clasetStep.timed_rule_cases_v4 sequence
                   end
                 val report =
                   reconstruct_v4_using_transition
                     {clock = reconstruction_ticking_clock (),
                      kernel_replay =
                        fn grounded =>
                          Tactical.VALID
                            (clasetReplay.REPLAY_TAC grounded),
                      transition = transition, observe = NONE,
                      observe_stored_rule = NONE,
                      stop = fn () => false}
                     cs goal proof
                 val base = #base (#base report)
                 val statistics = #statistics base
                 val pulls = #alternative_pull_times report
               in
                 #completion base = blastReconstruct.Completed andalso
                 Option.isSome (#result base) andalso
                 #stored_rule_setups statistics >= 15 andalso
                 !bounded_during_pulls andalso !observed_pulls > 0 andalso
                 #alternative_pulls statistics >=
                   #stored_rule_setups statistics andalso
                 #classical_elapsed_snapshots pulls =
                   2 * #alternative_pulls statistics andalso
                 #sequence_statistics_reads pulls = 0 andalso
                 #summary_statistics_reads pulls = 1 andalso
                 #retained_trace_allocations pulls = 0
               end
       end)

val _ =
  test
    ("timed-v2 failed finish restores its exact outer owner stack",
     fn () =>
       let
         exception OuterCleanupClock of int ref
         val sentinel = ref 157
         val p = mk_var ("timed_v2_none_p", bool)
         val goal = ([], p)
         val proof : blastSearch.proof =
           {script = [], trace = [], depth = 0,
            branches_created = 0, branches_closed = 0,
            choices_pruned = 0}
         val report =
           blastReconstruct.reconstructMeasuredTimedDetailedV2
             {clock = reconstruction_ticking_clock (), observe = NONE,
              observe_stored_rule = NONE, stop = fn () => false}
             goal proof
         val base = #base report
         val statistics = #statistics base
         val outer = #outer_reconstruction_times report

         fun cleanup_clock action =
           let
             val calls = ref 0
           in
             fn () =>
               let
                 val current = !calls
                 val _ = calls := current + 1
               in
                 if current = 3 then action ()
                 else Time.fromSeconds (Int.toLarge current)
               end
           end

         val clock_identity =
           ((ignore
               (blastReconstruct.reconstructMeasuredTimedDetailedV2
                 {clock =
                    cleanup_clock
                      (fn () => raise OuterCleanupClock sentinel),
                  observe = NONE, observe_stored_rule = NONE,
                  stop = fn () => false}
                 goal proof);
             false)
            handle OuterCleanupClock actual => actual = sentinel
                 | _ => false)
         val backwards_identity =
           ((ignore
               (blastReconstruct.reconstructMeasuredTimedDetailedV2
                 {clock =
                    cleanup_clock (fn () => Time.fromSeconds 1),
                  observe = NONE, observe_stored_rule = NONE,
                  stop = fn () => false}
                 goal proof);
             false)
            handle HOL_ERR error =>
                     Feedback.top_structure_of error = "blastReconstruct"
                 | _ => false)
       in
         #completion base = blastReconstruct.Completed andalso
         not (Option.isSome (#result base)) andalso
         #current_phase base =
           SOME
             {boundary = blastReconstruct.Exit,
              phase = blastReconstruct.ReplayRecursion} andalso
         #phase_entries statistics = 2 andalso
         #phase_exits statistics = 1 andalso
         #finish_open_goal_checks statistics = 1 andalso
         #alternative_enumeration_time outer = Time.zeroTime andalso
         #replay_continuation_time outer = Time.fromSeconds 2 andalso
         #other_outer_time outer = Time.fromSeconds 3 andalso
         #outer_reconstruction_time outer = Time.fromSeconds 5 andalso
         #classical_time (#classical_times base) = Time.zeroTime andalso
         #attempt_wall_time base = Time.fromSeconds 5 andalso
         clock_identity andalso backwards_identity
       end)

val _ =
  test
    ("timed-v2 nested alternative backtracking has exact owners",
     fn () =>
       let
         val p = mk_var ("timed_v2_nested_p", bool)
         val q = mk_var ("timed_v2_nested_q", bool)
         val r = mk_var ("timed_v2_nested_r", bool)
         val goal = ([r, mk_conj (p, q)], p)
         val cs =
           clasetLib.add_selims
             [("timed-v2-nested-andE", CONJ_ELIM_THM)]
             clasetLib.empty_cs
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 val report =
                   blastReconstruct.reconstructWithMeasuredTimedDetailedV2
                     {clock = reconstruction_ticking_clock (),
                      observe = NONE, observe_stored_rule = NONE,
                      stop = fn () => false}
                     cs goal proof
                 val base = #base report
                 val outer = #outer_reconstruction_times report
               in
                 #completion base = blastReconstruct.Completed andalso
                 Option.isSome (#result base) andalso
                 #alternative_pulls (#statistics base) = 2 andalso
                 #alternative_enumeration_time outer =
                   Time.fromSeconds 14 andalso
                 #replay_continuation_time outer =
                   Time.fromSeconds 13 andalso
                 #other_outer_time outer = Time.fromSeconds 11 andalso
                 #outer_reconstruction_time outer =
                   Time.fromSeconds 38 andalso
                 #classical_time (#classical_times base) =
                   Time.fromSeconds 17 andalso
                 #attempt_wall_time base = Time.fromSeconds 55
               end
       end)

val _ =
  test
    ("timed-v3 Alternative pulls have exact exclusive distribution",
     fn () =>
       let
         val p = mk_var ("timed_v3_nested_p", bool)
         val q = mk_var ("timed_v3_nested_q", bool)
         val r = mk_var ("timed_v3_nested_r", bool)
         val goal = ([r, mk_conj (p, q)], p)
         val cs =
           clasetLib.add_selims
             [("timed-v3-nested-andE", CONJ_ELIM_THM)]
             clasetLib.empty_cs
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 val report =
                   blastReconstruct.reconstructWithMeasuredTimedDetailedV3
                     {clock = reconstruction_ticking_clock (),
                      observe = NONE, observe_stored_rule = NONE,
                      stop = fn () => false}
                     cs goal proof
                 val v2 = #base report
                 val base = #base v2
                 val outer = #outer_reconstruction_times v2
                 val pulls = #alternative_pull_times report
                 val report_v2 =
                   blastReconstruct.reconstructWithMeasuredTimedDetailedV2
                     {clock = reconstruction_ticking_clock (),
                      observe = NONE, observe_stored_rule = NONE,
                      stop = fn () => false}
                     cs goal proof
                 val ordinary =
                   blastReconstruct.reconstructWith cs goal proof
                 val subtotal =
                   Time.+
                     (#completed_pull_time pulls,
                      Time.+
                        (#failed_pull_time pulls,
                         #interrupted_pull_time pulls))
               in
                 #completion base = blastReconstruct.Completed andalso
                 Option.isSome (#result base) andalso
                 Option.isSome ordinary andalso
                 #completion base = #completion (#base report_v2) andalso
                 #current_phase base = #current_phase (#base report_v2)
                 andalso
                 #statistics base = #statistics (#base report_v2) andalso
                 Option.isSome (#result base) =
                   Option.isSome (#result (#base report_v2)) andalso
                 #completed_pulls pulls = 2 andalso
                 #failed_pulls pulls = 0 andalso
                 #interrupted_pulls pulls = 0 andalso
                 #completed_pull_time pulls = Time.fromSeconds 14 andalso
                 #failed_pull_time pulls = Time.zeroTime andalso
                 #interrupted_pull_time pulls = Time.zeroTime andalso
                 #alternative_pull_time pulls = Time.fromSeconds 14 andalso
                 #alternative_residual_time pulls = Time.zeroTime andalso
                 #max_completed_pull_time pulls = Time.fromSeconds 13 andalso
                 #max_failed_pull_time pulls = Time.zeroTime andalso
                 #max_interrupted_pull_time pulls = Time.zeroTime andalso
                 #max_alternative_pull_time pulls = Time.fromSeconds 13
                 andalso
                 subtotal = #alternative_pull_time pulls andalso
                 Time.+
                   (#alternative_pull_time pulls,
                    #alternative_residual_time pulls) =
                   #alternative_enumeration_time outer
               end
       end)

val _ =
  test
    ("bounded-v4 matches timed-v3 categories, pulls and result",
     fn () =>
       let
         val p = mk_var ("bounded_v4_parity_p", bool)
         val q = mk_var ("bounded_v4_parity_q", bool)
         val r = mk_var ("bounded_v4_parity_r", bool)
         val goal = ([r, mk_conj (p, q)], p)
         val cs =
           clasetLib.add_selims
             [("bounded-v4-parity-andE", CONJ_ELIM_THM)]
             clasetLib.empty_cs
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 val controls =
                   {clock = reconstruction_ticking_clock (),
                    observe = NONE, observe_stored_rule = NONE,
                    stop = fn () => false}
                 val report_v3 = reconstruct_v3 controls cs goal proof
                 val report_v4 =
                   reconstruct_v4
                     {clock = reconstruction_ticking_clock (),
                      observe = NONE, observe_stored_rule = NONE,
                      stop = fn () => false}
                     cs goal proof
                 val v2_v3 = #base report_v3
                 val v2_v4 = #base report_v4
                 val base_v3 = #base v2_v3
                 val base_v4 = #base v2_v4
                 val pulls_v4 = #alternative_pull_times report_v4
               in
                 #completion base_v3 = #completion base_v4 andalso
                 #current_phase base_v3 = #current_phase base_v4 andalso
                 #current_stored_rule base_v3 =
                   #current_stored_rule base_v4 andalso
                 #statistics base_v3 = #statistics base_v4 andalso
                 #classical_times base_v3 = #classical_times base_v4
                 andalso #attempt_wall_time base_v3 =
                   #attempt_wall_time base_v4 andalso
                 Option.isSome (#result base_v3) =
                   Option.isSome (#result base_v4) andalso
                 #minor_unification_times v2_v3 =
                   #minor_unification_times v2_v4 andalso
                 #outer_reconstruction_times v2_v3 =
                   #outer_reconstruction_times v2_v4 andalso
                 same_fine_v3_v4
                   (#minor_unification_times report_v3)
                   (#minor_unification_times report_v4) andalso
                 same_pulls_v3_v4
                   (#alternative_pull_times report_v3) pulls_v4 andalso
                 #sequence_statistics_reads pulls_v4 = 0 andalso
                 #summary_statistics_reads pulls_v4 = 1 andalso
                 #retained_trace_allocations pulls_v4 = 0
               end
       end)

val _ =
  test
    ("timed-v2 kernel failure rejects exact provenance without scanning",
     fn () =>
       let
         val p = mk_var ("timed_v2_kernel_p", bool)
         val q = mk_var ("timed_v2_kernel_q", bool)
         val r = mk_var ("timed_v2_kernel_r", bool)
         val conjunction = mk_conj (p, q)
         val goal = ([r, conjunction, conjunction], p)
         val cs =
           clasetLib.add_selims
             [("timed-v2-kernel-andE", CONJ_ELIM_THM)]
             clasetLib.empty_cs
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 val kernel_calls = ref 0
                 val observations =
                   ref
                     ([] :
                       (blastReconstruct.boundary *
                        blastReconstruct.phase) list)

                 fun kernel_replay grounded kernel_goal =
                   (kernel_calls := !kernel_calls + 1;
                    if !kernel_calls = 1 then
                      raise mk_HOL_ERR "blast-selftest"
                        "kernel_replay" "injected first alternative"
                    else
                      Tactical.VALID
                        (clasetReplay.REPLAY_TAC grounded) kernel_goal)

                 val reconstruct_v2 =
                   blastReconstruct.reconstructWithMeasuredTimedDetailedV2

                 val report =
                   reconstruct_v2_using_kernel
                     {clock = reconstruction_ticking_clock (),
                      kernel_replay = kernel_replay,
                      observe =
                        SOME
                          (fn event =>
                            observations :=
                              (#boundary event, #phase event) ::
                              !observations),
                      observe_stored_rule = NONE,
                      stop = fn () => false}
                     cs goal proof
                 val base = #base report
                 val outer = #outer_reconstruction_times report

                 fun count boundary phase =
                   List.length
                     (List.filter
                       (fn (actual_boundary, actual_phase) =>
                         actual_boundary = boundary andalso
                         actual_phase = phase)
                       (!observations))

                 val ordinary_observations =
                   ref
                     ([] :
                       (blastReconstruct.boundary *
                        blastReconstruct.phase) list)
                 val injected_observations =
                   ref
                     ([] :
                       (blastReconstruct.boundary *
                        blastReconstruct.phase) list)
                 fun remember reference event =
                   reference :=
                     (#boundary event, #phase event) :: !reference
                 val ordinary =
                   reconstruct_v2
                     {clock = reconstruction_ticking_clock (),
                      observe = SOME (remember ordinary_observations),
                      observe_stored_rule = NONE,
                      stop = fn () => false}
                     cs goal proof
                 val delegated =
                   reconstruct_v2_using_kernel
                     {clock = reconstruction_ticking_clock (),
                      kernel_replay =
                        fn grounded =>
                          Tactical.VALID
                            (clasetReplay.REPLAY_TAC grounded),
                      observe = SOME (remember injected_observations),
                      observe_stored_rule = NONE,
                      stop = fn () => false}
                     cs goal proof
               in
                 !kernel_calls = 1 andalso
                 #completion base = blastReconstruct.Completed andalso
                 not (Option.isSome (#result base)) andalso
                 count blastReconstruct.Enter
                   blastReconstruct.KernelReplay = 1 andalso
                 count blastReconstruct.Exit
                   blastReconstruct.KernelReplay = 0 andalso
                 #kernel_replay_attempts (#statistics base) = 1 andalso
                 #alternative_enumeration_time outer =
                   Time.fromSeconds 16 andalso
                 #replay_continuation_time outer =
                   Time.fromSeconds 14 andalso
                 #other_outer_time outer = Time.fromSeconds 10 andalso
                 #outer_reconstruction_time outer =
                   Time.fromSeconds 40 andalso
                 #classical_time (#classical_times base) =
                   Time.fromSeconds 17 andalso
                 #attempt_wall_time base = Time.fromSeconds 57 andalso
                 #completion (#base ordinary) =
                   #completion (#base delegated) andalso
                 #current_phase (#base ordinary) =
                   #current_phase (#base delegated) andalso
                 #statistics (#base ordinary) =
                   #statistics (#base delegated) andalso
                 #classical_times (#base ordinary) =
                   #classical_times (#base delegated) andalso
                 #attempt_wall_time (#base ordinary) =
                   #attempt_wall_time (#base delegated) andalso
                 Option.isSome (#result (#base ordinary)) andalso
                 Option.isSome (#result (#base delegated)) andalso
                 #minor_unification_times ordinary =
                   #minor_unification_times delegated andalso
                 #outer_reconstruction_times ordinary =
                   #outer_reconstruction_times delegated andalso
                 rev (!ordinary_observations) =
                   rev (!injected_observations)
               end
       end)

val _ =
  test
    ("timed-v3 continuation failure rejects exact provenance",
     fn () =>
       let
         val p = mk_var ("timed_v3_kernel_p", bool)
         val q = mk_var ("timed_v3_kernel_q", bool)
         val r = mk_var ("timed_v3_kernel_r", bool)
         val conjunction = mk_conj (p, q)
         val goal = ([r, conjunction, conjunction], p)
         val cs =
           clasetLib.add_selims
             [("timed-v3-kernel-andE", CONJ_ELIM_THM)]
             clasetLib.empty_cs
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 val kernel_calls = ref 0
                 fun kernel_replay grounded kernel_goal =
                   (kernel_calls := !kernel_calls + 1;
                    if !kernel_calls = 1 then
                      raise mk_HOL_ERR "blast-selftest"
                        "v3-kernel" "injected first continuation"
                    else
                      Tactical.VALID
                        (clasetReplay.REPLAY_TAC grounded) kernel_goal)
                 val report =
                   reconstruct_v3_using_kernel
                     {clock = reconstruction_ticking_clock (),
                      kernel_replay = kernel_replay,
                      observe = NONE, observe_stored_rule = NONE,
                      stop = fn () => false}
                     cs goal proof
                 val base = #base (#base report)
                 val outer = #outer_reconstruction_times (#base report)
                 val pulls = #alternative_pull_times report
               in
                 !kernel_calls = 1 andalso
                 #completion base = blastReconstruct.Completed andalso
                 not (Option.isSome (#result base)) andalso
                 #stored_rule_attempt_selections (#statistics base) = 1
                 andalso
                 #completed_pulls pulls = 2 andalso
                 #failed_pulls pulls = 2 andalso
                 #interrupted_pulls pulls = 0 andalso
                 #completed_pull_time pulls = Time.fromSeconds 14 andalso
                 #failed_pull_time pulls = Time.fromSeconds 2 andalso
                 #interrupted_pull_time pulls = Time.zeroTime andalso
                 #alternative_pull_time pulls = Time.fromSeconds 16 andalso
                 #alternative_residual_time pulls = Time.zeroTime andalso
                 #max_completed_pull_time pulls =
                   Time.fromSeconds 13 andalso
                 #max_failed_pull_time pulls = Time.fromSeconds 1 andalso
                 #max_interrupted_pull_time pulls = Time.zeroTime andalso
                 #max_alternative_pull_time pulls =
                   Time.fromSeconds 13 andalso
                 #alternative_enumeration_time outer =
                   Time.fromSeconds 16 andalso
                 #replay_continuation_time outer =
                   Time.fromSeconds 14 andalso
                 #other_outer_time outer = Time.fromSeconds 10 andalso
                 #outer_reconstruction_time outer =
                   Time.fromSeconds 40 andalso
                 #classical_time (#classical_times base) =
                   Time.fromSeconds 201 andalso
                 #attempt_wall_time base = Time.fromSeconds 241
               end
       end)

val _ =
  test
    ("timed-v3 interrupted pull has one exact terminal outcome",
     fn () =>
       let
         val p = mk_var ("timed_v3_interrupt_p", bool)
         val q = mk_var ("timed_v3_interrupt_q", bool)
         val goal = ([mk_conj (p, q)], p)
         val cs =
           clasetLib.add_selims
             [("timed-v3-interrupt-andE", CONJ_ELIM_THM)]
             clasetLib.empty_cs
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 val stop_now = ref false
                 fun cutoff
                       ({rule = {boundary, phase, ...}, ...} :
                          blastReconstruct.stored_rule_observation) =
                   if boundary = clasetStep.RuleEnter andalso
                      phase = clasetStep.RuleInstantiation then
                     stop_now := true
                   else ()
                 val report =
                   blastReconstruct.reconstructWithMeasuredTimedDetailedV3
                     {clock = reconstruction_ticking_clock (),
                      observe = NONE, observe_stored_rule = SOME cutoff,
                      stop = fn () => !stop_now}
                     cs goal proof
                 val base = #base (#base report)
                 val outer = #outer_reconstruction_times (#base report)
                 val pulls = #alternative_pull_times report
               in
                 #completion base = blastReconstruct.Interrupted andalso
                 not (Option.isSome (#result base)) andalso
                 #completed_pulls pulls = 0 andalso
                 #failed_pulls pulls = 0 andalso
                 #interrupted_pulls pulls = 1 andalso
                 #classical_elapsed_snapshots pulls = 2 andalso
                 #completed_pull_time pulls = Time.zeroTime andalso
                 #failed_pull_time pulls = Time.zeroTime andalso
                 #interrupted_pull_time pulls = Time.fromSeconds 5 andalso
                 #alternative_pull_time pulls = Time.fromSeconds 5 andalso
                 #alternative_residual_time pulls = Time.zeroTime andalso
                 #max_completed_pull_time pulls = Time.zeroTime andalso
                 #max_failed_pull_time pulls = Time.zeroTime andalso
                 #max_interrupted_pull_time pulls = Time.fromSeconds 5 andalso
                 #max_alternative_pull_time pulls = Time.fromSeconds 5 andalso
                 Time.+
                   (#alternative_pull_time pulls,
                    #alternative_residual_time pulls) =
                   #alternative_enumeration_time outer
               end
       end)

val _ =
  test
    ("bounded-v4 backtracking and interruption preserve v3 semantics",
     fn () =>
       let
         val p = mk_var ("bounded_v4_control_p", bool)
         val q = mk_var ("bounded_v4_control_q", bool)
         val r = mk_var ("bounded_v4_control_r", bool)
         val conjunction = mk_conj (p, q)
         val backtrack_goal = ([r, conjunction, conjunction], p)
         val cs =
           clasetLib.add_selims
             [("bounded-v4-control-andE", CONJ_ELIM_THM)]
             clasetLib.empty_cs

         fun injected_counter () =
           let
             val calls = ref 0
             fun replay grounded kernel_goal =
               (calls := !calls + 1;
                if !calls = 1 then
                  raise mk_HOL_ERR "blast-selftest" "bounded-v4"
                    "injected first continuation"
                else
                  Tactical.VALID
                    (clasetReplay.REPLAY_TAC grounded) kernel_goal)
           in
             (calls, replay)
           end
       in
         case blastSearch.tryGoal cs 0 backtrack_goal of
             NONE => false
           | SOME proof =>
               let
                 val (v3_calls, v3_kernel) = injected_counter ()
                 val (v4_calls, v4_kernel) = injected_counter ()
                 val v3 =
                   reconstruct_v3_using_kernel
                     {clock = reconstruction_ticking_clock (),
                      kernel_replay = v3_kernel, observe = NONE,
                      observe_stored_rule = NONE,
                      stop = fn () => false}
                     cs backtrack_goal proof
                 val v4 =
                   reconstruct_v4_using_kernel
                     {clock = reconstruction_ticking_clock (),
                      kernel_replay = v4_kernel, observe = NONE,
                      observe_stored_rule = NONE,
                      stop = fn () => false}
                     cs backtrack_goal proof
                 val base_v3 = #base (#base v3)
                 val base_v4 = #base (#base v4)

                 val interrupt_goal = ([conjunction], p)
                 val interrupt_proof =
                   valOf (blastSearch.tryGoal cs 0 interrupt_goal)
                 val stop_now = ref false
                 fun cutoff
                       ({rule = {boundary, phase, ...}, ...} :
                          blastReconstruct.stored_rule_observation) =
                   if boundary = clasetStep.RuleEnter andalso
                      phase = clasetStep.RuleInstantiation then
                     stop_now := true
                   else ()
                 val interrupted =
                   reconstruct_v4
                     {clock = reconstruction_ticking_clock (),
                      observe = NONE, observe_stored_rule = SOME cutoff,
                      stop = fn () => !stop_now}
                     cs interrupt_goal interrupt_proof
                 val interrupted_base = #base (#base interrupted)
                 val interrupted_pulls =
                   #alternative_pull_times interrupted
               in
                 !v3_calls = 1 andalso !v4_calls = 1 andalso
                 #completion base_v3 = #completion base_v4 andalso
                 not (Option.isSome (#result base_v3)) andalso
                 not (Option.isSome (#result base_v4)) andalso
                 #statistics base_v3 = #statistics base_v4 andalso
                 #classical_times base_v3 = #classical_times base_v4
                 andalso #attempt_wall_time base_v3 =
                   #attempt_wall_time base_v4 andalso
                 same_fine_v3_v4
                   (#minor_unification_times v3)
                   (#minor_unification_times v4) andalso
                 same_pulls_v3_v4
                   (#alternative_pull_times v3)
                   (#alternative_pull_times v4) andalso
                 #retained_trace_allocations
                   (#alternative_pull_times v4) = 0 andalso
                 #completion interrupted_base =
                   blastReconstruct.Interrupted andalso
                 not (Option.isSome (#result interrupted_base)) andalso
                 #completed_pulls interrupted_pulls = 0 andalso
                 #failed_pulls interrupted_pulls = 0 andalso
                 #interrupted_pulls interrupted_pulls = 1 andalso
                 #sequence_statistics_reads interrupted_pulls = 0 andalso
                 #summary_statistics_reads interrupted_pulls = 1 andalso
                 #retained_trace_allocations interrupted_pulls = 0
               end
       end)

val _ =
  test
    ("bounded-v4 callback and Interrupt exceptions retain identity",
     fn () =>
       let
         exception BoundedCallback of int ref
         val sentinel = ref 317
         val p = mk_var ("bounded_v4_callback_p", bool)
         val goal = ([], p)
         val proof : blastSearch.proof =
           {script = [blastSearch.CloseAssume {assumption = 1}],
            trace = [], depth = 0,
            branches_created = 0, branches_closed = 0,
            choices_pruned = 0}
         fun raises controls =
           ((ignore
               (blastReconstruct.reconstructMeasuredTimedDetailedV4
                 controls goal proof);
             false)
            handle BoundedCallback actual => actual = sentinel
                 | _ => false)
         val clock_ok =
           raises
             {clock = fn () => raise BoundedCallback sentinel,
              observe = NONE, observe_stored_rule = NONE,
              stop = fn () => false}
         val observer_ok =
           raises
             {clock = reconstruction_ticking_clock (),
              observe = SOME (fn _ => raise BoundedCallback sentinel),
              observe_stored_rule = NONE, stop = fn () => false}
         val stop_ok =
           raises
             {clock = reconstruction_ticking_clock (), observe = NONE,
              observe_stored_rule = NONE,
              stop = fn () => raise BoundedCallback sentinel}
         val interrupt_ok =
           ((ignore
               (blastReconstruct.reconstructMeasuredTimedDetailedV4
                 {clock = reconstruction_ticking_clock (),
                  observe = SOME (fn _ => raise Interrupt),
                  observe_stored_rule = NONE,
                  stop = fn () => false}
                 goal proof);
             false)
            handle Interrupt => true | _ => false)
       in
         clock_ok andalso observer_ok andalso stop_ok andalso interrupt_ok
       end)

val _ =
  test
    ("timed-v2 exact replay failure re-enters search",
     fn () =>
       let
         val alpha = Type.mk_vartype "'timed_v2_backtrack"
         val x = mk_var ("timed_v2_backtrack_x", alpha)
         val y = mk_var ("timed_v2_backtrack_y", alpha)
         val pred = mk_var ("timed_v2_backtrack_P", alpha --> bool)
         val p = mk_comb (pred, x)
         val py = mk_comb (pred, y)
         val q = mk_var ("timed_v2_backtrack_q", bool)
         val r = mk_var ("timed_v2_backtrack_r", bool)
         val bad = Drule.ADD_ASSUM r boolTheory.OR_INTRO_THM1
         val goal = ([mk_eq (x, y), p, q], mk_disj (py, q))
         val cs =
           clasetLib.add_intros
             [("timed-v2-good-right", boolTheory.OR_INTRO_THM2),
              ("timed-v2-bad-left", bad)] clasetLib.empty_cs
         val attempts =
           ref
             ([] :
               (blastReconstruct.timed_detailed_measured_result_v2 *
                (blastReconstruct.boundary *
                 blastReconstruct.phase) list) list)

         fun accept proof =
           let
             val observations =
               ref
                 ([] :
                   (blastReconstruct.boundary *
                    blastReconstruct.phase) list)
             val report =
               blastReconstruct.reconstructWithMeasuredTimedDetailedV2
                 {clock = reconstruction_ticking_clock (),
                  observe =
                    SOME
                      (fn event =>
                        observations :=
                          (#boundary event, #phase event) ::
                          !observations),
                  observe_stored_rule = NONE, stop = fn () => false}
                 cs goal proof
             val _ =
               attempts := (report, rev (!observations)) :: !attempts
           in
             case #result (#base report) of
                 SOME result => (proof, result)
               | NONE => raise blastSearch.PROOF_FAILED
           end

         val result = blastSearch.searchGoal cs 1 goal accept
         val reports = rev (!attempts)

         fun has boundary phase observations =
           List.exists
             (fn (actual_boundary, actual_phase) =>
               actual_boundary = boundary andalso actual_phase = phase)
             observations
       in
         Option.isSome result andalso
         case reports of
             [(failed, failed_observations),
              (succeeded, succeeded_observations)] =>
               let
                 val failed_base = #base failed
                 val failed_outer = #outer_reconstruction_times failed
                 val succeeded_base = #base succeeded
                 val succeeded_outer =
                   #outer_reconstruction_times succeeded
               in
                 #completion failed_base = blastReconstruct.Completed
                 andalso not (Option.isSome (#result failed_base)) andalso
                 #kernel_replay_attempts (#statistics failed_base) = 0
                 andalso
                 #alternative_enumeration_time failed_outer =
                   Time.fromSeconds 10 andalso
                 #replay_continuation_time failed_outer =
                   Time.fromSeconds 13 andalso
                 #other_outer_time failed_outer = Time.fromSeconds 7
                 andalso
                 #outer_reconstruction_time failed_outer =
                   Time.fromSeconds 30 andalso
                 #classical_time (#classical_times failed_base) =
                   Time.fromSeconds 11 andalso
                 #attempt_wall_time failed_base = Time.fromSeconds 41
                 andalso
                 #completion succeeded_base = blastReconstruct.Completed
                 andalso Option.isSome (#result succeeded_base) andalso
                 has blastReconstruct.Enter blastReconstruct.KernelReplay
                   succeeded_observations andalso
                 has blastReconstruct.Exit blastReconstruct.KernelReplay
                   succeeded_observations andalso
                 #kernel_replay_attempts (#statistics succeeded_base) = 1
                 andalso
                 #alternative_enumeration_time succeeded_outer =
                   Time.fromSeconds 16 andalso
                 #replay_continuation_time succeeded_outer =
                   Time.fromSeconds 21 andalso
                 #other_outer_time succeeded_outer = Time.fromSeconds 15
                 andalso
                 #outer_reconstruction_time succeeded_outer =
                   Time.fromSeconds 52 andalso
                 #classical_time (#classical_times succeeded_base) =
                   Time.fromSeconds 17 andalso
                 #attempt_wall_time succeeded_base = Time.fromSeconds 69
               end
           | _ => false
       end)

val _ =
  test
    ("timed detailed NONE and clock exceptions preserve identity",
     fn () =>
       let
         exception TimedClock of int ref
         val sentinel = ref 97
         val p = mk_var ("timed_none_p", bool)
         val goal = ([], p)
         val proof : blastSearch.proof =
           {script = [], trace = [], depth = 0,
            branches_created = 0, branches_closed = 0,
            choices_pruned = 0}
         val untimed =
           blastReconstruct.reconstructMeasuredDetailed
             {observe = NONE, observe_stored_rule = NONE,
              stop = fn () => false}
             goal proof
         val timed =
           blastReconstruct.reconstructMeasuredTimedDetailed
             {clock = reconstruction_ticking_clock (),
              observe = NONE, observe_stored_rule = NONE,
              stop = fn () => false}
             goal proof
         val clock_calls = ref 0
         fun failing_clock () =
           if !clock_calls = 0 then
             (clock_calls := 1; Time.zeroTime)
           else raise TimedClock sentinel
         val exception_ok =
           ((ignore
               (blastReconstruct.reconstructMeasuredTimedDetailed
                 {clock = failing_clock, observe = NONE,
                  observe_stored_rule = NONE,
                  stop = fn () => false}
                 goal proof);
             false)
            handle TimedClock actual => actual = sentinel
                 | _ => false)
       in
         #completion untimed = blastReconstruct.Completed andalso
         #completion timed = blastReconstruct.Completed andalso
         not (Option.isSome (#result untimed)) andalso
         not (Option.isSome (#result timed)) andalso
         #statistics untimed = #statistics timed andalso
         #classical_time (#classical_times timed) = Time.zeroTime
         andalso
         #attempt_wall_time timed = Time.fromSeconds 1 andalso
         exception_ok
       end)

val _ =
  test
    ("timed detailed terminal clock precedes report aggregation",
     fn () =>
       let
         fun boundary_clock calls =
           fn () =>
             (calls := !calls + 1;
              case !calls of
                  1 => Time.fromSeconds 3
                | 2 => Time.fromSeconds 10
                | _ =>
                    raise mk_HOL_ERR "blast-selftest" "boundary_clock"
                      "clock read after terminal reconstruction outcome")

         fun run goal proof stop =
           let
             val calls = ref 0
             val report =
               blastReconstruct.reconstructMeasuredTimedDetailed
                 {clock = boundary_clock calls, observe = NONE,
                  observe_stored_rule = NONE, stop = stop}
                 goal proof
           in
             (report, !calls)
           end

         val p = mk_var ("timed_terminal_p", bool)
         val completed_proof : blastSearch.proof =
           {script = [blastSearch.CloseAssume {assumption = 1}],
            trace = [], depth = 0,
            branches_created = 0, branches_closed = 0,
            choices_pruned = 0}
         val none_proof : blastSearch.proof =
           {script = [], trace = [], depth = 0,
            branches_created = 0, branches_closed = 0,
            choices_pruned = 0}
         val (completed, completed_calls) =
           run ([p], p) completed_proof (fn () => false)
         val (none, none_calls) =
           run ([], p) none_proof (fn () => false)
         val (interrupted, interrupted_calls) =
           run ([p], p) completed_proof (fn () => true)

         fun terminal report calls completion has_result =
           calls = 2 andalso #completion report = completion andalso
           Option.isSome (#result report) = has_result andalso
           #attempt_wall_time report = Time.fromSeconds 7
       in
         terminal completed completed_calls blastReconstruct.Completed true
         andalso
         terminal none none_calls blastReconstruct.Completed false andalso
         terminal interrupted interrupted_calls
           blastReconstruct.Interrupted false
       end)

val _ =
  test
    ("timed stored clock observer and stop exceptions preserve identity",
     fn () =>
       let
         exception StoredTimed of string * int ref
         val sentinel = ref 109
         val p = mk_var ("timed_stored_exception_p", bool)
         val q = mk_var ("timed_stored_exception_q", bool)
         val goal = ([mk_conj (p, q)], p)
         val cs =
           clasetLib.add_selims
             [("andE", CONJ_ELIM_THM)] clasetLib.empty_cs

         fun at_instantiation action
               ({rule = {boundary, phase, ...}, ...} :
                  blastReconstruct.stored_rule_observation) =
           case (boundary, phase) of
               (clasetStep.RuleEnter,
                clasetStep.RuleInstantiation) => action ()
             | _ => ()

         fun reconstruct proof clock observer stop =
           ignore
             (blastReconstruct.reconstructWithMeasuredTimedDetailed
               {clock = clock, observe = NONE,
                observe_stored_rule = SOME observer, stop = stop}
               cs goal proof)

         fun from_clock proof action =
           let
             val armed = ref false
             fun observer observation =
               at_instantiation (fn () => armed := true) observation
             fun clock () =
               if !armed then action () else Time.zeroTime
           in
             reconstruct proof clock observer (fn () => false)
           end

         fun from_observer proof action =
           reconstruct proof (fn () => Time.zeroTime)
             (at_instantiation action) (fn () => false)

         fun from_stop proof action =
           let
             val armed = ref false
             fun observer observation =
               at_instantiation (fn () => armed := true) observation
             fun stop () =
               if !armed then action () else false
           in
             reconstruct proof (fn () => Time.zeroTime) observer stop
           end

         fun hol_ok run label =
           ((run
               (fn () =>
                 raise mk_HOL_ERR label "inner-phase" "original");
             false)
            handle HOL_ERR error =>
                     Feedback.top_structure_of error = label andalso
                     Feedback.top_function_of error = "inner-phase"
                     andalso Feedback.message_of error = "original"
                 | _ => false)

         fun custom_ok run label =
           ((run (fn () => raise StoredTimed (label, sentinel)); false)
            handle StoredTimed (actual, reference) =>
                     actual = label andalso reference = sentinel
                 | _ => false)

         fun interrupt_ok run =
           ((run (fn () => raise Interrupt); false)
            handle Interrupt => true | _ => false)
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 fun clock action = from_clock proof action
                 fun observer action = from_observer proof action
                 fun stop action = from_stop proof action
               in
                 hol_ok clock "timed-stored-clock-hol" andalso
                 custom_ok clock "clock" andalso interrupt_ok clock
                 andalso
                 hol_ok observer "timed-stored-observer-hol" andalso
                 custom_ok observer "observer" andalso
                 interrupt_ok observer andalso
                 hol_ok stop "timed-stored-stop-hol" andalso
                 custom_ok stop "stop" andalso interrupt_ok stop
               end
       end)

val _ =
  test
    ("detailed stored replay interrupts at an exact classical boundary",
     fn () =>
       let
         val p = mk_var ("measured_detailed_cutoff_p", bool)
         val q = mk_var ("measured_detailed_cutoff_q", bool)
         val goal = ([mk_conj (p, q)], p)
         val cs =
           clasetLib.add_selims
             [("andE", CONJ_ELIM_THM)] clasetLib.empty_cs
         val stop_now = ref false
         fun observe
               ({rule = {boundary, phase, ...}, ...} :
                  blastReconstruct.stored_rule_observation) =
           case (boundary, phase) of
               (clasetStep.RuleEnter,
                clasetStep.RuleInstantiation) => stop_now := true
             | _ => ()
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 val report =
                   blastReconstruct.reconstructWithMeasuredDetailed
                     {observe = NONE,
                      observe_stored_rule = SOME observe,
                      stop = fn () => !stop_now}
                     cs goal proof
                 val statistics = #statistics report
               in
                 #completion report = blastReconstruct.Interrupted andalso
                 not (Option.isSome (#result report)) andalso
                 #current_phase report =
                   SOME
                     {boundary = blastReconstruct.Enter,
                      phase = blastReconstruct.AlternativeEnumeration}
                 andalso
                 #current_stored_rule report =
                   SOME
                     {script_position = 1,
                      step_kind = blastReconstruct.SafeRuleStep,
                      duplicate = false,
                      rule =
                        {boundary = clasetStep.RuleEnter,
                         phase = clasetStep.RuleInstantiation,
                         goal_position = 1,
                         rule_kind = clasetStep.ElimRule,
                         assumption_position = SOME 1}} andalso
                 #stored_rule_checkpoints statistics = 9 andalso
                 #stored_rule_phase_entries statistics = 5 andalso
                 #stored_rule_phase_exits statistics = 4 andalso
                 #stored_rule_attempt_selections statistics = 1 andalso
                 #stored_rule_instantiations statistics = 1 andalso
                 #stored_rule_child_store_constructions statistics = 0
               end
       end)

val _ =
  test
    ("detailed stored observers cross reconstruction catch-all unchanged",
     fn () =>
       let
         exception StoredObserver of int ref
         val sentinel = ref 61
         val p = mk_var ("measured_detailed_exception_p", bool)
         val q = mk_var ("measured_detailed_exception_q", bool)
         val goal = ([mk_conj (p, q)], p)
         val cs =
           clasetLib.add_selims
             [("andE", CONJ_ELIM_THM)] clasetLib.empty_cs
         fun at_instantiation action
               ({rule = {boundary, phase, ...}, ...} :
                  blastReconstruct.stored_rule_observation) =
           case (boundary, phase) of
               (clasetStep.RuleEnter,
                clasetStep.RuleInstantiation) => action ()
             | _ => ()
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 fun run observer =
                   ignore
                     (blastReconstruct.reconstructWithMeasuredDetailed
                       {observe = NONE,
                        observe_stored_rule = SOME observer,
                        stop = fn () => false}
                       cs goal proof)
                 val hol_ok =
                   ((run
                       (at_instantiation
                         (fn () =>
                           raise mk_HOL_ERR
                             "measured-stored-hol"
                             "observe" "propagate"));
                     false)
                    handle HOL_ERR error =>
                             Feedback.top_structure_of error =
                               "measured-stored-hol"
                         | _ => false)
                 val custom_ok =
                   ((run
                       (at_instantiation
                         (fn () => raise StoredObserver sentinel));
                     false)
                    handle StoredObserver actual => actual = sentinel
                         | _ => false)
                 val interrupt_ok =
                   ((run (at_instantiation (fn () => raise Interrupt));
                     false)
                    handle Interrupt => true | _ => false)
                 val stop_throw_now = ref false
                 fun arm_stop observation =
                   at_instantiation
                     (fn () => stop_throw_now := true) observation
                 val stop_ok =
                   ((ignore
                       (blastReconstruct.reconstructWithMeasuredDetailed
                           {observe = NONE,
                            observe_stored_rule = SOME arm_stop,
                            stop =
                              fn () =>
                                if !stop_throw_now then
                                  raise mk_HOL_ERR
                                    "measured-stored-stop-hol"
                                    "stop" "propagate"
                                else false}
                           cs goal proof);
                     false)
                    handle HOL_ERR error =>
                             Feedback.top_structure_of error =
                               "measured-stored-stop-hol"
                         | _ => false)
               in
                 hol_ok andalso custom_ok andalso interrupt_ok andalso
                 stop_ok
               end
       end)

val _ =
  test
    ("detailed stored replay observations repeat deterministically",
     fn () =>
       let
         val p = mk_var ("measured_detailed_repeat_p", bool)
         val q = mk_var ("measured_detailed_repeat_q", bool)
         val goal = ([mk_conj (p, q)], p)
         val cs =
           clasetLib.add_selims
             [("andE", CONJ_ELIM_THM)] clasetLib.empty_cs
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 fun run () =
                   let
                     val observations =
                       ref
                         ([] :
                           blastReconstruct.stored_rule_observation list)
                     fun observe event =
                       observations := event :: !observations
                     val report =
                       blastReconstruct.reconstructWithMeasuredDetailed
                         {observe = NONE,
                          observe_stored_rule = SOME observe,
                          stop = fn () => false}
                         cs goal proof
                   in
                     (rev (!observations), #statistics report,
                      #completion report,
                      Option.isSome (#result report))
                   end
                 val (observations1, statistics1, completion1, result1) =
                   run ()
                 val (observations2, statistics2, completion2, result2) =
                   run ()
               in
                 observations1 = observations2 andalso
                 statistics1 = statistics2 andalso
                 completion1 = completion2 andalso result1 = result2
               end
       end)

val _ =
  test
    ("deep measured reconstruction stop exceptions propagate unchanged",
     fn () =>
       let
         val p = mk_var ("measured_deep_exception_p", bool)
         val q = mk_var ("measured_deep_exception_q", bool)
         val goal = ([mk_conj (p, q)], p)
         val cs =
           clasetLib.add_selims
             [("andE", CONJ_ELIM_THM)] clasetLib.empty_cs
         val throw_now = ref false
         fun observe
               ({boundary, phase} : blastReconstruct.observation) =
           case (boundary, phase) of
               (blastReconstruct.Enter,
                blastReconstruct.StoredRuleTransition) =>
                  throw_now := true
             | _ => ()
         fun stop () =
           if !throw_now then
             raise mk_HOL_ERR "measured-deep-stop-sentinel"
               "stop" "propagate"
           else false
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               ((ignore
                   (blastReconstruct.reconstructWithMeasured
                     {observe = SOME observe, stop = stop}
                     cs goal proof);
                 false)
                handle HOL_ERR error =>
                         Feedback.top_structure_of error =
                           "measured-deep-stop-sentinel"
                     | _ => false)
       end)

val _ =
  test
    ("deep observer exceptions preserve HOL_ERR custom and Interrupt identity",
     fn () =>
       let
         exception ObserverStop of int ref
         val sentinel = ref 47
         val p = mk_var ("measured_observer_exception_p", bool)
         val q = mk_var ("measured_observer_exception_q", bool)
         val goal = ([mk_conj (p, q)], p)
         val cs =
           clasetLib.add_selims
             [("andE", CONJ_ELIM_THM)] clasetLib.empty_cs

         fun at_transition action
               ({boundary, phase} : blastReconstruct.observation) =
           case (boundary, phase) of
               (blastReconstruct.Enter,
                blastReconstruct.StoredRuleTransition) => action ()
             | _ => ()

         fun hol_observer observation =
           at_transition
             (fn () =>
               raise mk_HOL_ERR "measured-observer-hol-sentinel"
                 "observe" "propagate") observation
         fun custom_observer observation =
           at_transition (fn () => raise ObserverStop sentinel) observation
         fun interrupt_observer observation =
           at_transition (fn () => raise Interrupt) observation
       in
         case blastSearch.tryGoal cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 fun run observer =
                   ignore
                     (blastReconstruct.reconstructWithMeasured
                       {observe = SOME observer, stop = fn () => false}
                       cs goal proof)
                 val hol_ok =
                   ((run hol_observer; false)
                    handle HOL_ERR error =>
                             Feedback.top_structure_of error =
                               "measured-observer-hol-sentinel"
                         | _ => false)
                 val custom_ok =
                   ((run custom_observer; false)
                    handle ObserverStop actual => actual = sentinel
                         | _ => false)
                 val interrupt_ok =
                   ((run interrupt_observer; false)
                    handle Interrupt => true
                         | _ => false)
               in
                 hol_ok andalso custom_ok andalso interrupt_ok
               end
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
               let
                 val report =
                   blastReconstruct.reconstructWithMeasured
                     {observe = NONE, stop = fn () => false}
                     cs goal proof
                 val statistics = #statistics report
               in
                 has_step
                   (fn blastSearch.DeferGoal => true | _ => false)
                   proof andalso
                 has_step
                   (fn blastSearch.UnsafeRule _ => true | _ => false)
                   proof andalso
                 #completion report = blastReconstruct.Completed andalso
                 Option.isSome (#result report) andalso
                 #defer_goal_steps statistics > 0 andalso
                 #unsafe_rule_steps statistics > 0 andalso
                 (ignore (validation []); true)
               end
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
         val stop_now = ref false
         fun observe
               ({boundary, phase} : blastReconstruct.observation) =
           case (boundary, phase) of
               (blastReconstruct.Enter,
                blastReconstruct.DuplicateChildMove) =>
                  stop_now := true
             | _ => ()
       in
         case blastReconstruct.searchGoal cs 2 goal of
             SOME (proof, ([], validation)) =>
               let
                 val report =
                   blastReconstruct.reconstructWithMeasured
                     {observe = SOME observe, stop = fn () => !stop_now}
                     cs goal proof
                 val statistics = #statistics report
               in
                 has_step
                   (fn blastSearch.UnsafeRule {duplicate = true, ...} =>
                         true
                     | _ => false) proof andalso
                 #completion report = blastReconstruct.Interrupted andalso
                 #current_phase report =
                   SOME
                     {boundary = blastReconstruct.Enter,
                      phase = blastReconstruct.DuplicateChildMove} andalso
                 #unsafe_rule_steps statistics > 0 andalso
                 #stored_rule_transitions statistics > 0 andalso
                 #duplicate_child_moves statistics = 1 andalso
                 (ignore (validation []); true)
               end
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
               let
                 val report =
                   blastReconstruct.reconstructWithMeasured
                     {observe = NONE, stop = fn () => false}
                     cs goal proof
                 val statistics = #statistics report
               in
                 has_step
                   (fn blastSearch.HypSubst {equality = 1} => true
                     | _ => false)
                   proof andalso
                 (case #script proof of
                      blastSearch.HypSubst {equality = 1} :: _ => true
                    | _ => false) andalso
                 #completion report = blastReconstruct.Completed andalso
                 Option.isSome (#result report) andalso
                 #hyp_subst_steps statistics > 0 andalso
                 (ignore (validation []); true)
               end
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
    ("hyp-subst reconstructs an equality with a beta-redex side",
     fn () =>
       let
         val alpha = Type.mk_vartype "'beta_subst"
         val x = mk_var ("beta_subst_x", alpha)
         val y = mk_var ("beta_subst_y", alpha)
         val a = mk_var ("beta_subst_a", alpha)
         val z = mk_var ("beta_subst_z", alpha)
         val p = mk_var ("beta_subst_P", alpha --> bool)
         val redex = mk_comb (mk_abs (z, x), a)
         val goal =
           ([mk_eq (redex, y), mk_comb (p, y)], mk_comb (p, redex))
         fun exact theorem =
           Term.term_eq (concl theorem) (#2 goal) andalso
           HOLset.equal
             (Thm.hypset theorem,
              HOLset.fromList Term.compare (#1 goal))
       in
         case blastSearch.tryGoal clasetLib.empty_cs 0 goal of
             NONE => false
           | SOME proof =>
               let
                 val ordinary = blastReconstruct.reconstruct goal proof
                 val measured =
                   blastReconstruct.reconstructMeasured
                     {observe = NONE, stop = fn () => false} goal proof
               in
                 case (ordinary, #completion measured, #result measured) of
                     (SOME ([], ordinary_validation),
                      blastReconstruct.Completed,
                      SOME ([], measured_validation)) =>
                       has_step
                         (fn blastSearch.HypSubst _ => true | _ => false)
                         proof andalso
                       has_step
                         (fn blastSearch.CloseAssume _ => true | _ => false)
                         proof andalso
                       #hyp_subst_steps (#statistics measured) > 0 andalso
                       #close_assume_steps (#statistics measured) > 0 andalso
                       exact (ordinary_validation []) andalso
                       exact (measured_validation [])
                   | _ => false
               end
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
         val failed_parity = ref false
         val successful_parity = ref false
         val messages = ref ([] : string list)
         val old_trace = Feedback.current_trace "blast"
         fun accept proof =
           let
             val _ = attempts := !attempts + 1
             val ordinary = blastReconstruct.reconstruct goal proof
             val measured =
               blastReconstruct.reconstructMeasured
                 {observe = NONE, stop = fn () => false} goal proof
             val _ =
               case (ordinary, #completion measured, #result measured) of
                   (NONE, blastReconstruct.Completed, NONE) =>
                     failed_parity := true
                 | (SOME (ordinary_goals, _),
                    blastReconstruct.Completed,
                    SOME (measured_goals, measured_validation)) =>
                     successful_parity :=
                       (null ordinary_goals andalso
                        null measured_goals andalso
                        (ignore (measured_validation []); true))
                 | _ => ()
           in
             case ordinary of
                 SOME result => (proof, result)
               | NONE => raise blastSearch.PROOF_FAILED
           end
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
         !attempts = 2 andalso !failed_parity andalso
         !successful_parity andalso traced andalso
         case result of
             SOME (proof, ([], validation)) =>
               has_step
                 (fn blastSearch.HypSubst _ => true | _ => false)
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
         case blastSearch.tryGoal cs 1 goal of
             NONE => false
           | SOME proof =>
               let
                 val ordinary =
                   blastReconstruct.reconstructWith cs goal proof
                 val measured =
                   blastReconstruct.reconstructWithMeasured
                     {observe = NONE, stop = fn () => false}
                     cs goal proof
               in
                 not (Option.isSome ordinary) andalso
                 #completion measured = blastReconstruct.Completed andalso
                 not (Option.isSome (#result measured)) andalso
                 not (Option.isSome
                   (blastReconstruct.searchGoal cs 1 goal))
               end
       end)

fun blast_solves tactic goal =
  case total (Tactical.VALID tactic) goal of
      SOME ([], validation) => (ignore (validation []); true)
    | _ => false

fun blast_fails tactic goal =
  not (Option.isSome (total (Tactical.VALID tactic) goal))

(* True when the tactic does not close the goal within the budget --
   whether it fails outright or simply runs over.  Expected-failure
   entries assert this, so a search that becomes fast enough turns the
   suite red rather than passing silently. *)
fun blast_exceeds budget tactic goal =
  let
    val started = Time.now ()
    val solved =
      Timeout.apply budget (fn () => not (blast_fails tactic goal)) ()
      handle Timeout.TIMEOUT _ => false
  in
    not (solved andalso Time.< (Time.- (Time.now (), started), budget))
  end

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
    ("kernel replay preserves transition-established rule instances",
     fn () =>
       blast_solves (tableauLib.BLAST_DEPTH_TAC 4 [])
         ([],
          “(!x:'a y.
               relation x y <=> (label x <=> label y)) ==>
            !x y. relation x y <=> relation y x”))

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
    ("fixed-depth trace separates final and cumulative counters",
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
         contains "fixed-depth runs 1" andalso
         contains "final fixed-depth configured depth 0" andalso
         contains "final fixed-depth maximum resource cost 0" andalso
         contains "final fixed-depth inferences performed 0" andalso
         contains "final fixed-depth branches created 1" andalso
         contains "final fixed-depth branches closed 0" andalso
         contains "cumulative inferences performed 0" andalso
         contains "cumulative branches created 1" andalso
         contains "cumulative branches closed 0" andalso
         contains "search " andalso contains "reconstruction "
       end)

val _ =
  test
    ("iterative trace labels final depth and cumulative aggregation",
     fn () =>
       let
         val p = mk_var ("iterative_stats_p", bool)
         val (solved, messages) =
           Lib.with_flag (tableauLib.depth_limit, 1)
             (fn () =>
                blast_trace_messages 2 (tableauLib.BLAST_TAC [])
                  ([], p)) ()
         fun contains text =
           List.exists (String.isSubstring text) messages
       in
         not solved andalso contains "Blast stats: no proof" andalso
         contains "fixed-depth runs 2" andalso
         contains "final fixed-depth configured depth 1" andalso
         contains "final fixed-depth maximum resource cost 0" andalso
         contains "final fixed-depth inferences performed 0" andalso
         contains "final fixed-depth branches created 1" andalso
         contains "final fixed-depth branches closed 0" andalso
         contains "cumulative inferences performed 0" andalso
         contains "cumulative branches created 2" andalso
         contains "cumulative branches closed 0" andalso
         contains "cumulative choices pruned 0"
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

(* Problems the tableau search does not yet solve within the budget.
   These are search deficiencies to fix, not properties of the goals:
   Entries are asserted to FAIL, so fixing one turns this suite red and
   forces the list to shrink -- the accounting has teeth in both
   directions.  A problem is NEVER to be closed by naming it, or its
   statement, in a preprocessor, rewrite table or claset seed. *)
val pelletier_expected_failures = []

fun expected_failure number =
  List.exists (fn known => known = number) pelletier_expected_failures

fun run_pelletier (number, proposition) =
  let
    val expected = expected_failure number
    val name =
      "BLAST_TAC Pelletier " ^ Int.toString number ^
      (if expected then " (expected failure)" else "")
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
    val within = Time.< (elapsed, pelletier_budget)
  in
    if solved andalso within then
      if expected then
        die (name ^ " now solves: remove it from " ^
             "pelletier_expected_failures and raise the count")
      else (pelletier_solved := !pelletier_solved + 1; OK ())
    else if expected then OK ()
    else if !timed_out orelse not within then
      die (name ^ " exceeded its 30 second budget")
    else
      die (name ^ " did not solve the goal")
  end

val _ = List.app run_pelletier pelletier_corpus

val _ =
  test
    ("BLAST_TAC Pelletier solved-goal count",
     fn () =>
       !pelletier_solved =
         length pelletier_corpus - length pelletier_expected_failures
       andalso !pelletier_solved = 48)

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

(* Entries here are search deficiencies at the published depths, not
   properties of the goals.  Each is asserted to fail, so improved
   search must shrink the list and raise the solved-goal count. *)
val table1_expected_failures = []

fun run_table1_depth (number, depth) =
  let
    val expected =
      List.exists (fn known => known = number) table1_expected_failures
    val name =
      "BLAST_DEPTH_TAC Pelletier " ^ Int.toString number ^ " at " ^
      Int.toString depth ^
      (if expected then " (expected failure)" else "")
    val proposition = pelletier_problem number
  in
    if expected then
      (tprint name;
       if blast_exceeds blast_regression_budget
            (tableauLib.BLAST_DEPTH_TAC depth []) ([], proposition)
       then OK ()
       else
         die (name ^ " now solves: remove it from " ^
              "table1_expected_failures and raise the count"))
    else
      (timed_blast name blast_regression_budget
         (tableauLib.BLAST_DEPTH_TAC depth []) ([], proposition);
       table1_solved := !table1_solved + 1)
  end

val _ = List.app run_table1_depth table1_depths

val _ =
  test
    ("Table-1 published-depth solved-goal count",
     fn () =>
       !table1_solved =
         length table1_depths - length table1_expected_failures
       andalso !table1_solved = 9)

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

val _ =
  if selftest_level () >= 2 then
    timed_blast "BLAST_DEPTH_TAC Halting II" (Time.fromSeconds 120)
      (tableauLib.BLAST_DEPTH_TAC 7 []) ([], halting_ii)
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
