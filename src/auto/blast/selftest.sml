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
                  (fn blastSearch.HypSubst => true | _ => false)
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
    fun step blastSearch.HypSubst = "subst"
      | step blastSearch.CloseAssume = "assume"
      | step blastSearch.CloseContradiction = "contradiction"
      | step (blastSearch.SafeRule {rule, updated}) =
          "safe:" ^ Bool.toString updated ^ ":" ^ origin (#origin rule)
      | step blastSearch.DeferGoal = "defer"
      | step
          (blastSearch.UnsafeRule {rule, updated, duplicate}) =
          "unsafe:" ^ Bool.toString updated ^ ":" ^
          Bool.toString duplicate ^ ":" ^ origin (#origin rule)
  in
    map step (#script proof)
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
                 same_proof_options (#result measured, #result repeated) andalso
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
            pattern = pattern, premises = premises}
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
       in
         same_rule_lists_alpha (dependencies, renamed_dependencies) andalso
         not (same_rule_lists_alpha (sharing_left, sharing_right)) andalso
         not (same_rule_lists_alpha (typed_left, typed_swapped)) andalso
         not (same_rule_lists_alpha (dependencies, wrong_identity)) andalso
         not (same_rule_lists_alpha (dependencies, wrong_count))
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
         val p = mk_var ("measured_contradiction_p", bool)
         val q = mk_var ("measured_contradiction_q", bool)
         val goal = ([p, mk_neg p], q)
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
                       (ignore (ordinary_validation []);
                        ignore (measured_validation []);
                        true)
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
                   (fn blastSearch.HypSubst => true | _ => false)
                   proof andalso
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
   the remedies are scoped in .agent-files/PLAN_phase_1_2_green.md.
   Entries are asserted to FAIL, so fixing one turns this suite red and
   forces the list to shrink -- the accounting has teeth in both
   directions.  A problem is NEVER to be closed by naming it, or its
   statement, in a preprocessor, rewrite table or claset seed. *)
val pelletier_expected_failures = [34, 38, 41, 42, 43, 45]

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
       andalso !pelletier_solved = 42)

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

(* The same search deficiencies as pelletier_expected_failures, seen at
   the published depths.  See .agent-files/PLAN_phase_1_2_green.md. *)
val table1_expected_failures = [34, 38, 43]

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
       andalso !table1_solved = 6)

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

(* Halting II is not yet within reach of the search at depth 7; it was
   previously "solved" by a preprocessor that recognised the goal and
   handed back a metis-proved theorem.  That preprocessor is gone.  The
   remedy is scoped in .agent-files/PLAN_phase_1_2_green.md; until then
   this is an asserted expected failure, never an answer lookup. *)
val _ =
  if selftest_level () >= 2 then
    let
      val name = "BLAST_DEPTH_TAC Halting II (expected failure)"
      val _ = tprint name
    in
      if blast_exceeds (Time.fromSeconds 120)
           (tableauLib.BLAST_DEPTH_TAC 7 []) ([], halting_ii)
      then OK ()
      else die (name ^ " now solves: promote it to an asserted success")
    end
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
