open HolKernel testutils

structure SelfTestTactical = Tactical
structure Tactical =
struct
  open SelfTestTactical
  fun VALID tactic goal =
    SelfTestTactical.VALID tactic goal (Context.snapshot())
end
open listTheory optionTheory pred_setTheory

(* check, residual, valid_closes and tactic_fails come from
   linarithCorpus, which states the assertion helpers once for the
   suites that reach linear arithmetic; with_arith_fact below is from
   there too. *)
open linarithCorpus

(* A selftest binary starts with no theory segment open, so a datatype
   has nowhere to be declared until one is. *)
val _ = Theory.new_theory "clasimpHookSelftest"

(* clasimpLib is loaded before this selftest unit, so this datatype exercises
   the live TypeBase hook rather than the registration catch-up sweep. *)
val _ = Datatype.Datatype
  `clasimp_hook_after_load = ClasimpHookAfter bool bool`

fun same_goals left right =
  ListPair.allEq
    (fn (goal1, goal2) => boolSyntax.goal_eq goal1 goal2)
    (left, right)

val solver_ss = simpLib.clear_rules (clasimpLib.clasimp_ss ())
val safe_simp = clasimpLib.safe_asm_full_simp solver_ss []

val _ =
  check
    ("safe solver accepts an alpha-matching assumption",
     fn () =>
       valid_closes safe_simp
         ([``(\x:'a. P x) a : bool``], ``(\y:'a. P y) a : bool``))

val _ =
  check
    ("safe solver proves an alpha-reflexive equality",
     fn () =>
       valid_closes safe_simp
         ([], ``(\x:'a. f x) = (\y:'a. f y)``))

val _ =
  check
    ("safe solver proves truth",
     fn () => valid_closes safe_simp ([], boolSyntax.T))

val _ =
  check
    ("safe solver closes from a false assumption",
     fn () =>
       valid_closes safe_simp
         ([boolSyntax.F], ``clasimp_false_goal:bool``))

val _ =
  check
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
  check
    ("conditional witnesses retain every context theorem's support",
     fn () =>
       let
         val left = ``clasimp_witness_p (3:num) : bool``
         val right = ``clasimp_witness_q (3:num) : bool``
         val condition =
           ``?n:num. clasimp_witness_p n /\ clasimp_witness_q n``
         fun prove context_thms =
           clasimpLib.witness_subgoaler
             {stack = [], context_thms = context_thms,
              recurse = Thm.REFL} condition
         val proved = prove [Thm.ASSUME left, Thm.ASSUME right]
         val missing = prove [Thm.ASSUME left]
         val hypotheses = Thm.hyp proved
       in
         Term.aconv (Thm.concl proved)
           (boolSyntax.mk_eq (condition, boolSyntax.T)) andalso
         length hypotheses = 2 andalso
         List.exists (Term.aconv left) hypotheses andalso
         List.exists (Term.aconv right) hypotheses andalso
         Term.aconv (Thm.concl missing)
           (boolSyntax.mk_eq (condition, condition))
       end)

(* A plain conditional citation must remain available to the safe
   simplifier even if unsafe search also compiles a rule view of it. *)
val invocation_q_def =
  new_definition
    ("invocation_q_def", ``invocation_q (x:'a) <=> T``)
val invocation_implication =
  Tactical.prove
    (``!x:'a. invocation_p x ==> invocation_q x``,
     Rewrite.REWRITE_TAC [invocation_q_def])
val invocation_goal =
  ([``invocation_p (a:'a):bool``], ``invocation_q (a:'a)``)
fun invocation_closes tactic =
  null (residual tactic invocation_goal) handle HOL_ERR _ => false

val _ =
  check
    ("CLARSIMP_TAC uses a directly supplied conditional fact",
     fn () =>
       invocation_closes
         (Tactical.THEN
           (Tactic.ASSUME_TAC invocation_implication,
            clasimpLib.CLARSIMP_TAC [])) andalso
       invocation_closes
         (clasimpLib.CLARSIMP_TAC [invocation_implication]))

val _ =
  check
    ("the conditional citation does not add unsafe CLARSIMP search",
     fn () =>
       let
         val target = ``invocation_q (a:'a)``
         val result =
           SOME
             (residual
               (clasimpLib.CLARSIMP_TAC [invocation_implication])
               ([], target))
           handle HOL_ERR _ => NONE
       in
         case result of
             SOME [(assumptions, remaining)] =>
               null assumptions andalso aconv remaining target
           | _ => false
       end)

val _ =
  check
    ("AUTO_DEPTH_TAC simplifies with a supplied conditional fact",
     fn () =>
       invocation_closes
         (clasimpLib.AUTO_DEPTH_TAC {blast = 0, depth = 0}
            [invocation_implication]))

(* The first cited rewrite exposes the bool-typed application of the
   second.  The initial target has no application of invocation_id, so
   an initial-goal-only literal specialization cannot supply that view. *)
val invocation_id_def =
  new_definition ("invocation_id_def", ``invocation_id (x:'a) = x``)
val invocation_bridge_def =
  new_definition
    ("invocation_bridge_def",
     ``invocation_bridge (n:num) = invocation_id T``)
val invocation_id_fact =
  Tactical.prove
    (``!x:'a. invocation_id x = x``,
     Rewrite.REWRITE_TAC [invocation_id_def])
val invocation_bridge_fact =
  Tactical.prove
    (``!n:num. invocation_bridge n = invocation_id T``,
     Rewrite.REWRITE_TAC [invocation_bridge_def])

val _ =
  check
    ("CLARSIMP_TAC uses a fact after another fact exposes its type",
     fn () =>
       let
         val goal = ([], ``invocation_bridge 0 = T``)
         fun closes facts =
           valid_closes (clasimpLib.CLARSIMP_TAC facts) goal
             handle HOL_ERR _ => false
       in
         not (closes [invocation_bridge_fact]) andalso
         not (closes [invocation_id_fact]) andalso
         closes [invocation_bridge_fact, invocation_id_fact]
       end)

val _ =
  check
    ("AUTO simplification uses a fact at a type exposed by another",
     fn () =>
       let
         val goal = ([], ``invocation_bridge 0 = T``)
         fun closes facts =
           valid_closes
             (clasimpLib.AUTO_DEPTH_TAC {blast = 0, depth = 0} facts)
             goal
             handle HOL_ERR _ => false
       in
         not (closes [invocation_bridge_fact]) andalso
         not (closes [invocation_id_fact]) andalso
         closes [invocation_bridge_fact, invocation_id_fact]
       end)

val _ =
  check
    ("clasimpset fixes conditional-rewrite depth at forty",
     fn () =>
       #cond_depth
         (simpLib.traverseconfig_for_ss (clasimpLib.clasimp_ss ())) =
       SOME 40)

val _ =
  check
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

(* The extra rewrite is scoped to this one probe: the tests below run
   against the ambient simpsets, and a rewrite with a live hypothesis left
   in srw_ss would make an unrelated one fail for an unrelated reason. *)
val derived_after =
  BasicProvers.with_simpset_updates
    (fn ss =>
      simpLib.++
        (ss, simpLib.named_rewrites "clasimp-selftest-derived"
               [derived_rule]))
    (fn () =>
      Conv.QCONV
        (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) []) derived_lhs)
    ()

val derived_restored =
  Conv.QCONV
    (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) []) derived_lhs

val _ =
  check
    ("clasimpset cache recomputes around a simpset update",
     fn () =>
       aconv (snd (boolSyntax.dest_eq (concl derived_before)))
         derived_lhs andalso
       aconv (snd (boolSyntax.dest_eq (concl derived_after)))
         derived_rhs andalso
       aconv (snd (boolSyntax.dest_eq (concl derived_restored)))
         derived_lhs)

(* A recursive equation whose right-hand side is a conditional is the
   ordinary way to state an interval or an iteration.  Under HOL4's
   COND_CONG the simplifier enters the then-branch with the test
   assumed, and the test is exactly what licenses the next unfolding, so
   the rewriting never stops.  The weak congruence this layer installs
   simplifies the test alone, so one unfolding is the normal form: the
   expected right-hand side below still carries the recursive call.  The
   budget is what keeps a regression a failure rather than a hang. *)
val recursion =
  ASSUME
    ``!item.
        clasimp_iterate item =
          if clasimp_test item then clasimp_iterate (clasimp_step item)
          else clasimp_base``

val recursion_step = Drule.SPEC_ALL recursion

val recursion_unfolded =
  Lib.total
    (Timeout.apply (Time.fromSeconds 30)
       (Conv.QCONV
          (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [recursion])))
    (boolSyntax.lhs (concl recursion_step))

val _ =
  check
    ("a conditional recursion unfolds once, not forever",
     fn () =>
       case recursion_unfolded of
           NONE => false
         | SOME theorem =>
             aconv (boolSyntax.rhs (concl theorem))
               (boolSyntax.rhs (concl recursion_step)))

(* And it reports an absent CONG fragment rather than replacing nothing:
   a simpset that kept the strong congruence under the weakened name
   would unfold forever again, silently. *)
val _ =
  check
    ("weakening reports a simpset with no conditional congruence",
     fn () =>
       (ignore (clasimpLib.weaken_cond_congruence simpLib.empty_ss);
        false)
       handle HOL_ERR error =>
                Feedback.top_function_of error = "weaken_cond_congruence"
            | Conv.UNCHANGED => false)

val mutual_goal =
  ([``P (a:'a) : bool``, ``a:'a = b``], ``mutual_q:bool``)
val mutual_expected =
  [([``P (b:'a) : bool``, ``a:'a = b``], ``mutual_q:bool``)]

val _ =
  check
    ("asm_full_simp uses later assumptions mutually",
     fn () =>
       same_goals
         (residual
            (clasimpLib.asm_full_simp BasicProvers.bool_ss [])
            mutual_goal)
         mutual_expected)

val chain_goal =
  ([``(f:'a -> 'b) x = g x``, ``(g:'a -> 'b) x = z``,
    ``R ((f:'a -> 'b) x) : bool``], ``chain_s:bool``)
val chain_expected =
  [([``(f:'a -> 'b) x = z``, ``(g:'a -> 'b) x = z``,
     ``R (z:'b) : bool``], ``chain_s:bool``)]

val _ =
  check
    ("asm_full_simp closes a three-assumption mutual chain",
     fn () =>
       same_goals
         (residual
            (clasimpLib.asm_full_simp BasicProvers.bool_ss [])
            chain_goal)
         chain_expected)

(* A source result states its premises as the antecedents of its
   conclusion, and mut_impc is mutual over exactly those.  Here the
   first antecedent is the one [LENGTH_TAKE] applies to and the second
   is its side condition, so the implication congruence -- which offers
   an antecedent only the ones before it -- leaves the goal standing. *)
val antecedent_goal =
  ([] : term list,
   ``LENGTH (TAKE n (l:'a list)) = k ==> n <= LENGTH l ==> n = k``)

val _ =
  check
    ("asm_full_simp simplifies an antecedent with the ones after it",
     fn () =>
       valid_closes
         (clasimpLib.asm_full_simp (clasimpLib.clasimp_ss ()) [])
         antecedent_goal)

val _ =
  check
    ("the ambient simplifier alone leaves that goal standing",
     fn () =>
       same_goals
         (residual
            (Tactical.TRY
               (simpLib.FULL_SIMP_TAC (clasimpLib.clasimp_ss ()) []))
            antecedent_goal)
         [antecedent_goal])

(* Isabelle simplifies the body of a bounded existential with its bound
   in context, [bex_cong_simp] being a default congruence there.  HOL4
   spells a bounded existential unfolded, so the fragment that carries
   the bound in is the congruence over the conjunction it unfolds to;
   with the fragment gone nothing offers the body its bound and the
   equivalence stands. *)
val bounded_goal =
  ([``!b:'a. MEM b zs ==> (p b <=> q b)``],
   ``(?e:'a. MEM e zs /\ p e) <=> (?e:'a. MEM e zs /\ q e)``)

val _ =
  check
    ("asm_full_simp simplifies a bounded body with its bound in context",
     fn () =>
       valid_closes
         (clasimpLib.asm_full_simp (clasimpLib.clasimp_ss ()) [])
         bounded_goal)

val _ =
  check
    ("without the congruence fragment that equivalence stands",
     fn () =>
       same_goals
         (residual
            (Tactical.TRY
               (clasimpLib.asm_full_simp
                  (simpLib.remove_ssfrags ["CONGWEAK"]
                     (clasimpLib.clasimp_ss ())) []))
            bounded_goal)
         [bounded_goal])

(* The rule hands the rebuilt conjunction back to the traversal, so the
   conjunction a bounded existential binds is still a term the rewrites
   reach -- the bound included.  A congruence that kept the node would
   leave the membership as it found it, this goal unchanged. *)
val _ =
  check
    ("the bound of a bounded existential is still rewritten",
     fn () =>
       aconv
         (boolSyntax.rhs
            (Thm.concl
               (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) []
                  ``?w:'a. MEM w (v::vs) /\ bounded_c w``)))
         ``?w:'a. ((w = v) \/ MEM w vs) /\ bounded_c (w:'a)``)

fun local_clasimp body base_cs base_ss controls =
  clasimpLib.process_clasimp_args body base_cs base_ss controls

fun probe_goal tactic =
  not
    (tactic_fails tactic
       ([], ``clasimp_argument_processor_probe:bool``))

fun same_thm left right =
  Term.aconv (concl left) (concl right)

fun same_spec
      ({kind = kind1, safe = safe1, prio = prio1} :
        clasetRules.rulespec)
      ({kind = kind2, safe = safe2, prio = prio2} :
        clasetRules.rulespec) =
  kind1 = kind2 andalso safe1 = safe2 andalso prio1 = prio2

datatype iff_test_shape = IffShape | NegShape | PlainShape

val iff_test_x = mk_var ("clasimp_iff_x", Type.ind)
val iff_test_pred =
  mk_var ("clasimp_iff_pred", Type.ind --> Type.bool)
val iff_test_left = mk_comb (iff_test_pred, iff_test_x)
val iff_test_right = mk_var ("clasimp_iff_right", Type.bool)
val iff_test_condition =
  boolSyntax.mk_eq (iff_test_x, iff_test_x)

fun iff_test_theorem conditional proposition =
  if conditional then
    DISCH iff_test_condition
      (Drule.ADD_ASSUM iff_test_condition (ASSUME proposition))
  else ASSUME proposition

fun install_iff name theorem =
  let
    val {rules, rewrite} =
      clasimpLib.iff_declaration name theorem
    val cs = clasimpLib.add_iff_rules rules clasetLib.empty_cs
    val ss =
      simpLib.++
        (BasicProvers.bool_ss, simpLib.rewrites [rewrite])
  in
    (rules, cs, ss)
  end

fun simp_rewrites_to ss source target =
  let
    val theorem =
      Conv.QCONV (simpLib.SIMP_CONV ss []) source
  in
    Term.aconv
      (snd (boolSyntax.dest_eq (concl theorem))) target
  end

fun rule_body theorem =
  snd (boolSyntax.strip_forall (concl theorem))

fun rule_has_shape expected_prems expected_conclusion (_, (_, theorem)) =
  let
    val (prems, conclusion) =
      boolSyntax.strip_imp_only (rule_body theorem)
  in
    ListPair.allEq
      (fn (left, right) => Term.aconv left right)
      (prems, expected_prems) andalso
    Term.aconv conclusion expected_conclusion
  end

fun iff_derivation_case
      (name, shape, conditional, proposition, rewrite_target) =
  let
    val theorem = iff_test_theorem conditional proposition
    val (rules, cs, ss) = install_iff name theorem
    val safe = not conditional
    val condition_tail =
      if conditional then [iff_test_condition] else []
    val installed = clasetLib.rules_of cs

    fun has_spec kind (spec, _) =
      same_spec spec {kind = kind, safe = safe, prio = NONE}

    val rules_ok =
      case (shape, rules) of
          (IffShape, [intro, dest]) =>
            has_spec clasetRules.Intro intro andalso
            has_spec clasetRules.Dest dest andalso
            rule_has_shape
              (iff_test_right :: condition_tail)
              iff_test_left intro andalso
            rule_has_shape
              (iff_test_left :: condition_tail)
              iff_test_right dest
        | (NegShape, [elim as (_, (_, theorem))]) =>
            let
              val (prems, conclusion) =
                boolSyntax.strip_imp_only (rule_body theorem)
            in
              has_spec clasetRules.Elim elim andalso
              ListPair.allEq
                (fn (left, right) => Term.aconv left right)
                (prems, iff_test_left :: condition_tail) andalso
              is_var conclusion andalso type_of conclusion = Type.bool
            end
        | (PlainShape, [intro]) =>
            has_spec clasetRules.Intro intro andalso
            rule_has_shape condition_tail iff_test_left intro
        | _ => false
  in
    rules_ok andalso length installed = length rules andalso
    simp_rewrites_to ss iff_test_left rewrite_target
  end

val iff_derivation_cases =
  [("iff-unconditional", IffShape, false,
    boolSyntax.mk_eq (iff_test_left, iff_test_right),
    iff_test_right),
   ("iff-conditional", IffShape, true,
    boolSyntax.mk_eq (iff_test_left, iff_test_right),
    iff_test_right),
   ("neg-unconditional", NegShape, false,
    boolSyntax.mk_neg iff_test_left, boolSyntax.F),
   ("neg-conditional", NegShape, true,
    boolSyntax.mk_neg iff_test_left, boolSyntax.F),
   ("plain-unconditional", PlainShape, false,
    iff_test_left, boolSyntax.T),
   ("plain-conditional", PlainShape, true,
    iff_test_left, boolSyntax.T)]

val _ =
  List.app
    (fn case_info as (name, _, _, _, _) =>
      check
        ("iff decision tree: " ^ name,
         fn () => iff_derivation_case case_info))
    iff_derivation_cases

val has_named_claset_rule = iffTestSupport.has_rule

(* The theory tests probe the persistent views the same way. *)
val has_iff_rewrite = iffTestSupport.rewrite_changes

fun persistent_iff_rule_name name suffix =
  name ^ ".__clasimp_iff_" ^ suffix

val clasimp_iff_attribute_probe_def =
  new_definition
    ("clasimp_iff_attribute_probe_def",
     ``clasimp_iff_attribute_probe (p : bool) = p``)

val _ =
  check
    ("iff settype and attribute are registered without collision",
     fn () =>
       List.exists (equal "iff") (ThmSetData.all_set_types ()) andalso
       ThmAttribute.is_attribute "iff")

val _ =
  check
    ("Theorem [iff] immediately updates and remove_iff retracts both stores",
     fn () =>
       let
         val local_name = "clasimp_iff_attribute_test"
         val persistent_name =
           KernelSig.name_toString (ThmSetData.toKName local_name)
         val theorem = clasimp_iff_attribute_probe_def
         val _ = boolLib.save_thm (local_name ^ "[iff]", theorem)
         val added =
           has_named_claset_rule
             (persistent_iff_rule_name persistent_name "intro") andalso
           has_named_claset_rule
             (persistent_iff_rule_name persistent_name "dest") andalso
           has_iff_rewrite persistent_name (BasicProvers.srw_ss ()) andalso
           has_iff_rewrite persistent_name (clasimpLib.clasimp_ss ())
         val _ = clasimpLib.remove_iff local_name
       in
         added andalso
         not
           (has_named_claset_rule
             (persistent_iff_rule_name persistent_name "intro")) andalso
         not
           (has_named_claset_rule
             (persistent_iff_rule_name persistent_name "dest")) andalso
         not
           (has_iff_rewrite persistent_name (BasicProvers.srw_ss ())) andalso
         not
           (has_iff_rewrite persistent_name (clasimpLib.clasimp_ss ()))
       end)

val _ =
  check
    ("a rejected remove_iff leaves a colliding claset rule installed",
     fn () =>
       let
         val local_name = "clasimp_absent_iff_test"
         val persistent_name =
           KernelSig.name_toString (ThmSetData.toKName local_name)
         val rule_name = persistent_name ^ "_intro"
         val spec =
           {kind = clasetRules.Intro, safe = false, prio = NONE}
         val theorem =
           ASSUME (mk_var ("clasimp_absent_iff_rule", Type.bool))
         val _ = clasetLib.temp_add_rule spec (rule_name, theorem)
         val rejected =
           (clasimpLib.remove_iff local_name; false)
             handle HOL_ERR _ => true
         val preserved =
           List.exists
             (fn (_, (name, rule)) =>
               name = rule_name andalso same_thm theorem rule)
             (clasetLib.rules_of (clasetLib.the_claset ()))
         val _ = clasetLib.temp_delrule rule_name
       in
         rejected andalso preserved
       end)

(* A name that denotes no installed declaration would be recorded as a
   delta that this theory, and every descendant of it, replays as a silent
   no-op -- and a malformed one would make them fail to load outright. *)
val _ =
  check
    ("remove_iff rejects an unresolvable name before recording a delta",
     fn () =>
       let
         fun deltas () =
           length (ThmSetData.current_data {settype = "iff"})
         val before_delta = deltas ()
         fun rejects name =
           (clasimpLib.remove_iff name; false) handle HOL_ERR _ => true
       in
         rejects "clasimp.absent.iff" andalso
         rejects "clasimp_absent_iff_name" andalso
         deltas () = before_delta
       end)

(* Two declarations may derive the same rule; each still owns its copy, so
   retracting one cannot disarm the other.  Neither is a declaration the
   user could correct, so neither warns. *)
val _ =
  check
    ("a derived iff rule duplicating an installed one is kept, unannounced",
     fn () =>
       let
         val theorem = clasimp_iff_attribute_probe_def
         val {rules = first, ...} =
           clasimpLib.iff_declaration "clasimp_iff_duplicate_first" theorem
         val {rules = second, ...} =
           clasimpLib.iff_declaration "clasimp_iff_duplicate_second" theorem
         val cs = clasimpLib.add_iff_rules first clasetLib.empty_cs
         val warnings = ref ([] : string list)
         val saved = !Feedback.WARNING_outstream
         val _ =
           Feedback.WARNING_outstream :=
             (fn message => warnings := message :: !warnings)
         val cs' =
           clasimpLib.add_iff_rules second cs
             handle e => (Feedback.WARNING_outstream := saved; raise e)
         val _ = Feedback.WARNING_outstream := saved
         val retracted =
           List.foldl
             (fn ((_, (name, _)), current) =>
               clasetLib.remove_rule name current)
             cs' first
         fun installed cs (_, (name, _)) =
           List.exists (fn (_, (name', _)) => name = name')
             (clasetLib.rules_of cs)
       in
         null (!warnings) andalso
         length (clasetLib.rules_of cs') =
           length (clasetLib.rules_of cs) + length second andalso
         List.all (installed cs') second andalso
         List.all (installed retracted) second andalso
         not (List.exists (installed retracted) first)
       end)

(* [iff_bottom_up] is [iff] with its simpset half installed as a
   low-priority reducer, which the traversal reaches only once the rewrites
   and the descent have both left a node alone.  The probe below is the
   shape that distinguishes the two: a declared rule reading its subject
   through [clasimp_bu_wrap], and an ordinary rewrite about a subject whose
   head is [clasimp_bu_step]. *)
val clasimp_bu_wrap_def =
  new_definition
    ("clasimp_bu_wrap_def", ``clasimp_bu_wrap (n:num) = (n = 0)``)

val clasimp_bu_view_def =
  new_definition
    ("clasimp_bu_view_def", ``clasimp_bu_view (n:num) = ~(n = 0)``)

val clasimp_bu_step_def =
  new_definition
    ("clasimp_bu_step_def", ``clasimp_bu_step (n:num) = SUC n``)

val clasimp_bu_rule =
  Tactical.prove
    (``!n. ~clasimp_bu_wrap n <=> clasimp_bu_view n``,
     Rewrite.REWRITE_TAC [clasimp_bu_wrap_def, clasimp_bu_view_def])

val clasimp_bu_head =
  Tactical.prove
    (``!n. clasimp_bu_wrap (clasimp_bu_step n) <=> F``,
     Rewrite.REWRITE_TAC
       [clasimp_bu_wrap_def, clasimp_bu_step_def, numTheory.NOT_SUC])

fun clasimp_bu_normalise term =
  let
    val ss =
      simpLib.++ (BasicProvers.srw_ss (), simpLib.rewrites [clasimp_bu_head])
  in
    boolSyntax.rhs (concl (Conv.QCONV (simpLib.SIMP_CONV ss []) term))
  end

(* Declared and retracted around the probe, so neither store keeps the
   rule once the check that needs it has run. *)
fun with_declaration (attribute, retract) local_name body =
  let
    val _ = boolLib.save_thm (local_name ^ "[" ^ attribute ^ "]",
                              clasimp_bu_rule)
    val result = body () handle e => (retract local_name; raise e)
    val _ = retract local_name
  in
    result
  end

(* A theory holds each name once, so every declaration takes its own. *)
fun with_bottom_up name body =
  with_declaration ("iff_bottom_up", clasimpLib.remove_iff_bottom_up) name body

fun with_plain_iff name body =
  with_declaration ("iff", clasimpLib.remove_iff) name body

val _ =
  check
    ("Theorem [iff_bottom_up] immediately updates and " ^
     "remove_iff_bottom_up retracts both stores",
     fn () =>
       let
         val local_name = "clasimp_bottom_up_attribute_test"
         val persistent_name =
           KernelSig.name_toString (ThmSetData.toKName local_name)
         val _ =
           boolLib.save_thm (local_name ^ "[iff_bottom_up]", clasimp_bu_rule)
         val added =
           has_named_claset_rule
             (persistent_iff_rule_name persistent_name "intro") andalso
           has_named_claset_rule
             (persistent_iff_rule_name persistent_name "dest") andalso
           has_iff_rewrite persistent_name (BasicProvers.srw_ss ()) andalso
           has_iff_rewrite persistent_name (clasimpLib.clasimp_ss ())
         val _ = clasimpLib.remove_iff_bottom_up local_name
       in
         added andalso
         not
           (has_named_claset_rule
             (persistent_iff_rule_name persistent_name "intro")) andalso
         not
           (has_named_claset_rule
             (persistent_iff_rule_name persistent_name "dest")) andalso
         not
           (has_iff_rewrite persistent_name (BasicProvers.srw_ss ())) andalso
         not
           (has_iff_rewrite persistent_name (clasimpLib.clasimp_ss ()))
       end)

(* The same theorem declared [iff] reaches the term first and leaves the
   subject in a form its own rule no longer addresses. *)
val _ =
  check
    ("an [iff_bottom_up] rewrite waits for a rule about the subject",
     fn () =>
       let
         val term = ``~clasimp_bu_wrap (clasimp_bu_step m)``
       in
         aconv
           (with_bottom_up "clasimp_bottom_up_masked"
              (fn () => clasimp_bu_normalise term))
           boolSyntax.T andalso
         aconv
           (with_plain_iff "clasimp_bottom_up_as_iff"
              (fn () => clasimp_bu_normalise term))
           ``clasimp_bu_view (clasimp_bu_step m)``
       end)

val _ =
  check
    ("an [iff_bottom_up] rewrite reduces a subject no rule addresses",
     fn () =>
       aconv
         (with_bottom_up "clasimp_bottom_up_bare"
            (fn () => clasimp_bu_normalise ``~clasimp_bu_wrap v``))
         ``clasimp_bu_view v``)

(* The same order for a rewrite a single invocation installs rather than
   a declaration: added plainly it reaches the term first and leaves the
   subject in a form the rule about that subject's head no longer
   addresses. *)
val clasimp_bu_head_ss =
  simpLib.++ (BasicProvers.srw_ss (), simpLib.rewrites [clasimp_bu_head])

fun clasimp_bu_reduce ss term =
  boolSyntax.rhs (concl (Conv.QCONV (simpLib.SIMP_CONV ss []) term))

val _ =
  check
    ("a rewrite installed for one invocation waits the same way",
     fn () =>
       let
         val term = ``~clasimp_bu_wrap (clasimp_bu_step m)``
       in
         aconv
           (clasimp_bu_reduce
              (simpLib.++
                 (clasimp_bu_head_ss,
                  clasimpLib.normalised_subject_fragment [clasimp_bu_rule]))
              term)
           boolSyntax.T andalso
         aconv
           (clasimp_bu_reduce
              (simpLib.++ (clasimp_bu_head_ss,
                           simpLib.rewrites [clasimp_bu_rule]))
              term)
           ``clasimp_bu_view (clasimp_bu_step m)``
       end)

val _ =
  check
    ("a rewrite installed for one invocation reduces a bare subject",
     fn () =>
       aconv
         (clasimp_bu_reduce
            (simpLib.++
               (clasimp_bu_head_ss,
                clasimpLib.normalised_subject_fragment [clasimp_bu_rule]))
            ``~clasimp_bu_wrap v``)
         ``clasimp_bu_view v``)

(* [simp_bottom_up] is the same order without the claset halves: a law the
   source declares [simp] and not [iff] may not seed the reasoner. *)
fun with_simp_bottom_up name body =
  with_declaration ("simp_bottom_up", clasimpLib.remove_simp_bottom_up)
    name body

val _ =
  check
    ("a [simp_bottom_up] rewrite waits for a rule about the subject",
     fn () =>
       aconv
         (with_simp_bottom_up "clasimp_simp_bottom_up_masked"
            (fn () => clasimp_bu_normalise
                        ``~clasimp_bu_wrap (clasimp_bu_step m)``))
         boolSyntax.T andalso
       aconv
         (with_simp_bottom_up "clasimp_simp_bottom_up_bare"
            (fn () => clasimp_bu_normalise ``~clasimp_bu_wrap v``))
         ``clasimp_bu_view v``)

val _ =
  check
    ("Theorem [simp_bottom_up] declares no claset rule and " ^
     "remove_simp_bottom_up retracts the rewrite",
     fn () =>
       let
         val local_name = "clasimp_simp_bottom_up_attribute_test"
         val persistent_name =
           KernelSig.name_toString (ThmSetData.toKName local_name)
         val _ =
           boolLib.save_thm
             (local_name ^ "[simp_bottom_up]", clasimp_bu_rule)
         val declared =
           has_iff_rewrite persistent_name (BasicProvers.srw_ss ()) andalso
           has_iff_rewrite persistent_name (clasimpLib.clasimp_ss ())
         val claset_rules =
           List.exists
             (fn suffix =>
                has_named_claset_rule
                  (persistent_iff_rule_name persistent_name suffix))
             ["intro", "dest", "elim"]
         val _ = clasimpLib.remove_simp_bottom_up local_name
       in
         declared andalso not claset_rules andalso
         not (has_iff_rewrite persistent_name (BasicProvers.srw_ss ())) andalso
         not (has_iff_rewrite persistent_name (clasimpLib.clasimp_ss ()))
       end)

(* The matcher the reducer uses.  A law stated as a higher-order pattern --
   Isabelle's miniscoping laws read a quantifier's body as [P x] -- fires
   on a body that is not literally a variable applied to the bound one only
   if the reducer matches the way the simplifier's own rewrites do. *)
val clasimp_bu_higher_order =
  Tactical.prove
    (``!P Q. (!x:num. P x ==> Q) <=> ((?x:num. P x) ==> Q)``,
     Rewrite.REWRITE_TAC [boolTheory.LEFT_FORALL_IMP_THM])

val _ =
  check
    ("a bottom-up rewrite is matched as a higher-order pattern",
     fn () =>
       aconv
         (clasimp_bu_reduce
            (simpLib.++
               (BasicProvers.srw_ss (),
                clasimpLib.normalised_subject_fragment
                  [clasimp_bu_higher_order]))
            ``!n:num.
                clasimp_bu_wrap (clasimp_bu_step n) ==> clasimp_bu_probe``)
         ``(?n:num. clasimp_bu_wrap (clasimp_bu_step n)) ==>
           clasimp_bu_probe``)

fun tyinfo_named tyop =
  case List.filter
    (fn tyi => #2 (TypeBasePure.ty_name_of tyi) = tyop)
    (TypeBase.elts ()) of
      [tyi] => tyi
    | _ => raise Fail ("missing or ambiguous TypeBase entry for " ^ tyop)

fun rules_named name =
  List.filter
    (fn (_, (name', _)) => name = name')
    (clasetLib.rules_of (clasetLib.the_claset ()))

val constructor_sintro_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE}

fun constructor_rule_names tyi index =
  let
    val (thy, tyop) = TypeBasePure.ty_name_of tyi
    val base =
      "__claset_tyinfo_" ^ thy ^ "_" ^ tyop ^
      "_inject_" ^ Int.toString index
  in
    {dest = base ^ "_dest", intro = base ^ "_intro"}
  end

fun has_constructor_intro tyi index =
  let
    val {intro, ...} = constructor_rule_names tyi index
  in
    case rules_named intro of
        [(spec, _)] => same_spec spec constructor_sintro_spec
      | _ => false
  end

val hook_tyinfo = tyinfo_named "clasimp_hook_after_load"
val list_tyinfo = tyinfo_named "list"

val _ =
  check
    ("constructor intro arrives through the post-load TypeBase hook",
     fn () => has_constructor_intro hook_tyinfo 0)

val _ =
  check
    ("constructor intro arrives through the TypeBase catch-up sweep",
     fn () => has_constructor_intro list_tyinfo 0)

val _ =
  check
    ("constructor intros do not duplicate Phase 0 injectivity seeds",
     fn () =>
       let
         val {dest, intro} = constructor_rule_names hook_tyinfo 0
       in
         length (rules_named dest) = 1 andalso
         length (rules_named intro) = 1
       end)

val {intro = hook_intro_name, ...} =
  constructor_rule_names hook_tyinfo 0

val (hook_intro_spec, (_, hook_intro_theorem)) =
  case rules_named hook_intro_name of
      [rule] => rule
    | _ => raise Fail "missing constructor intro"

val component_equality =
  CONJUNCT2 (CONJUNCT2 boolTheory.NOT_CLAUSES)

val component_equality_cs =
  clasetLib.add_sintros
    [("clasimp-component-equality", component_equality),
     ("clasimp-component-reflexivity", boolTheory.EQ_REFL)]
    clasetLib.empty_cs

val constructor_intro_cs =
  clasetLib.add_rule hook_intro_spec
    (hook_intro_name, hook_intro_theorem) component_equality_cs

val constructor_intro_goal : Abbrev.goal =
  ([],
   ``ClasimpHookAfter (~F) clasimp_hook_b =
     ClasimpHookAfter T clasimp_hook_b``)

fun constructor_safe cs =
  NTactical.DETERM (classicalLib.CS_SAFE_TAC cs)

val _ =
  check
    ("classical search cannot prove constructor equality without the intro",
     fn () =>
       tactic_fails
         (constructor_safe component_equality_cs)
         constructor_intro_goal)

val _ =
  check
    ("classical search proves constructor equality with the new intro",
     fn () =>
       valid_closes
         (constructor_safe constructor_intro_cs)
         constructor_intro_goal)

val _ =
  check
    ("the base claset proves constructor equality with its safe intro",
     fn () =>
       valid_closes
         (constructor_safe (clasetLib.the_claset ()))
         constructor_intro_goal)

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
      local_clasimp inspect clasetLib.empty_cs simpLib.empty_ss [marker]
  in
    probe_goal tactic
  end

val _ =
  check
    ("argument processor routes every claset theorem marker",
     fn () => List.all claset_marker_routed marker_rule_cases)

val _ =
  check
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
           local_clasimp inspect base simpLib.empty_ss
             [clasetLib.Del "clasimp-delete"]
       in
         probe_goal tactic
       end)

val _ =
  check
    ("Simp marker adds its theorem to the invocation simpset",
     fn () =>
       let
         fun simplify _ ss simp_args =
           simpLib.SIMP_TAC ss simp_args
         val tactic =
           local_clasimp simplify clasetLib.empty_cs simpLib.empty_ss
             [clasetLib.Simp
                (CONJUNCT2 (CONJUNCT2 boolTheory.NOT_CLAUSES))]
       in
         valid_closes tactic ([], ``~F``)
       end)

(* [inj_onD]'s shape.  HOL4's rewrite preparation refuses a bare-variable
   left-hand side and rewrites the conclusion to T instead, existentially
   closing the condition variables the conclusion does not carry
   (src/simp/src/Cond_rewr.sml), so the prepared rewrite matches every
   equation in the goal and nothing determines its condition: the simpset
   is not where this fact can reach a goal.  The invocation declares it as
   an unsafe destruction rule instead. *)
local
  (* [inj_onD]'s own form: the premises are separate, which is what lets a
     destruction rule fire on the first of them. *)
  val undetermined_fact =
    Tactical.prove
      (``!f s t x y.
           INJ f s t ==> x IN s ==> y IN s ==> (f x = f y) ==> (x = y)``,
       Tactical.THEN
         (Rewrite.REWRITE_TAC [pred_setTheory.INJ_DEF],
          Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC, Tactic.RES_TAC)))
  val undetermined_goal : Abbrev.goal =
    ([``INJ (undetermined_f : 'a -> 'b) undetermined_s undetermined_t``,
      ``(undetermined_x : 'a) IN undetermined_s``,
      ``(undetermined_y : 'a) IN undetermined_s``,
      ``(undetermined_f : 'a -> 'b) undetermined_x =
          undetermined_f undetermined_y``],
     ``(undetermined_x : 'a) = undetermined_y``)
in

(* The rewrite that cannot fire is not merely inert: it matches every
   equation and calls the solver on an existential at each, and the search
   that carries it does not come back, so a regression here stops the
   suite rather than failing a row.  There is no budget to bound it with
   -- [Timeout.apply] around this tactic never fired inside the selftest
   binary, where the same call preempts in an interactive session. *)

val _ =
  check
    ("a simp argument no rewrite of which can fire reaches the search",
     fn () =>
       valid_closes
         (clasimpLib.FORCE_TAC [clasetLib.Simp undetermined_fact])
         undetermined_goal)

(* The argument is what closes it: the ambient context does not. *)
val _ =
  check
    ("the goal that argument closes is not closed without it",
     fn () => tactic_fails (clasimpLib.FORCE_TAC []) undetermined_goal)

end

(* The other half of an undetermined condition variable.  [EVERY2_LENGTH]
   does carry a left-hand side to match -- [LENGTH l1 = LENGTH l2] -- and
   only its relation is undetermined, so the prepared rewrite is one the
   simpset can hold; what it needs is the witness the assumption names.
   [LIST_REL_APPEND_EQ] asks for that length equation as its own
   condition, which is where Isabelle's proof of [list_all2_appendI]
   sends it. *)
local
  val lifted_goal : Abbrev.goal =
    ([], ``!relation a b c d.
             LIST_REL relation a b ==> LIST_REL relation c d ==>
             LIST_REL relation (a ++ c) (b ++ d)``)
  val lifting_arguments =
    [clasetLib.Simp listTheory.LIST_REL_APPEND_EQ,
     clasetLib.Simp listTheory.EVERY2_LENGTH]
in

val _ =
  check
    ("a condition variable the left-hand side leaves open is read off " ^
     "an assumption",
     fn () => valid_closes (clasimpLib.AUTO_TAC lifting_arguments)
                lifted_goal)

(* The arguments are what close it; neither is ambient. *)
val _ =
  check
    ("the goal those arguments close is not closed without them",
     fn () => not (valid_closes (clasimpLib.AUTO_TAC []) lifted_goal))

end

(* The same witness, once the simpset has miniscoped the closure it sits
   in.  The closed condition is a conjunction over the rewrite's premises,
   and Isabelle's [ex_simps] -- ambient there, declared here -- leaves the
   quantifier over the one conjunct its variable occurs in, which is not
   where the assumption naming the witness can be read off.  The law is
   declared below in the form the seeds declare it; neither the goal nor
   the rule is a benchmark entry. *)
local
  val clasimp_pull_p_def =
    new_definition
      ("clasimp_pull_p_def", ``clasimp_pull_p (n:num) <=> (n MOD 2 = 0)``)
  val clasimp_pull_q_def =
    new_definition
      ("clasimp_pull_q_def", ``clasimp_pull_q (n:num) <=> clasimp_pull_p n``)
  val clasimp_pull_link_def =
    new_definition
      ("clasimp_pull_link_def",
       ``clasimp_pull_link (r:num -> num -> bool) x y <=> r x y``)
  (* Two premises, so that the closure is a conjunction, and a relation the
     conclusion does not carry, so that there is a witness to name at all:
     the conclusion determines the subject and nothing else. *)
  val clasimp_pull_fact =
    Tactical.prove
      (``!relation x y.
           (!a b. relation (a:num) (b:num) ==> clasimp_pull_p a) ==>
           clasimp_pull_link relation x y ==> clasimp_pull_q x``,
       Tactical.THEN
         (Rewrite.REWRITE_TAC [clasimp_pull_q_def, clasimp_pull_link_def],
          Tactical.THEN
            (Tactical.REPEAT Tactic.STRIP_TAC,
             Tactical.THEN (Tactic.RES_TAC, Rewrite.ASM_REWRITE_TAC []))))
  (* The assumption that names the witness is the goal's own antecedent, as
     it is in the corpus: the traversal has it in context only once it has
     descended through the quantifiers and the implication, and by then the
     condition has been left to the reducer. *)
  val clasimp_pull_goal : Abbrev.goal =
    ([``!a b. (clasimp_pull_r : num -> num -> bool) a b ==>
              clasimp_pull_p a``],
     ``!x y. clasimp_pull_link clasimp_pull_r x y ==> clasimp_pull_q x``)
  (* A theory holds each name once, so each declaration takes its own. *)
  fun with_miniscoping local_name body =
    let
      val _ =
        boolLib.save_thm
          (local_name ^ "[simp_bottom_up]", boolTheory.RIGHT_EXISTS_AND_THM)
      val result =
        body ()
        handle e => (clasimpLib.remove_simp_bottom_up local_name; raise e)
      val _ = clasimpLib.remove_simp_bottom_up local_name
    in
      result
    end
  fun closes local_name arguments =
    with_miniscoping local_name
      (fn () =>
         valid_closes
           (clasimpLib.asm_full_simp (clasimpLib.clasimp_ss ()) arguments)
           clasimp_pull_goal)
in

val _ =
  check
    ("a witness the simpset has miniscoped out of reach is still read " ^
     "off an assumption",
     fn () => closes "clasimp_pull_supplied" [clasimp_pull_fact])

(* The argument is what closes it: the assumptions alone do not. *)
val _ =
  check
    ("the goal that argument closes is not closed without it",
     fn () => not (closes "clasimp_pull_bare" []))

end

(* How a citation reaches the search.  An implication becomes a rule of
   the invocation claset and is kept out of the assumptions; both routes
   close the goal below, so what the routing changes is how much search
   that takes.  Reached as an assumption, the fact is taken apart a
   quantifier and an implication at a time; reached as a rule it is one
   application.  The work meter is the measurement, not the clock.

   The predicates are defined here and declared nowhere, and neither the
   rule nor the goal is a benchmark entry.  Their heads have to be
   constants: a rule concluding an applied variable is indexed under no
   constant and reaches nothing, which is a fact about the rule net and
   not about the routing. *)
local
  val routing_ord_def =
    new_definition
      ("routing_ord_def", ``routing_ord (r : 'a -> 'a -> bool) <=> T``)
  val routing_srt_def =
    new_definition
      ("routing_srt_def",
       ``routing_srt (r : 'a -> 'a -> bool) (x : 'a) <=> T``)
  val routing_dst_def =
    new_definition ("routing_dst_def", ``routing_dst (x : 'a) <=> T``)
  val routing_same_def =
    new_definition
      ("routing_same_def", ``routing_same (x : 'a) (y : 'a) <=> T``)
  (* Five premises, so that the assumption route has something to peel:
     the rule's own subjects are determined by the premises and not by
     its conclusion. *)
  val routing_fact =
    Tactical.prove
      (``!r x y.
           routing_ord r ==>
           routing_srt r x ==> routing_srt r y ==>
           routing_dst x ==> routing_dst y ==>
           routing_same x y``,
       Rewrite.REWRITE_TAC [routing_same_def])
  val routing_goal : Abbrev.goal =
    ([``routing_ord (routing_le : 'a -> 'a -> bool)``,
      ``routing_srt (routing_le : 'a -> 'a -> bool) (routing_a : 'a)``,
      ``routing_srt (routing_le : 'a -> 'a -> bool) (routing_b : 'a)``,
      ``routing_dst (routing_a : 'a)``,
      ``routing_dst (routing_b : 'a)``],
     ``routing_same (routing_a : 'a) (routing_b : 'a)``)
  fun search tactic =
    searchWork.measure (fn () => valid_closes tactic routing_goal)
in

val _ =
  check
    ("a supplied implication shortens the search it is given to",
     fn () =>
       let
         val (assumed_closed, assumed_work) =
           search
             (Tactical.THEN
                (Tactic.ASSUME_TAC routing_fact, classicalLib.FAST_TAC []))
         val (supplied_closed, supplied_work) =
           search (classicalLib.FAST_TAC [routing_fact])
       in
         assumed_closed andalso supplied_closed andalso
         #expansions supplied_work < #expansions assumed_work
       end)

end

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
  check
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
           local_clasimp inspect clasetLib.empty_cs simpLib.empty_ss
             generic_simp_markers
       in
         probe_goal tactic
       end)

val _ =
  check
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
           local_clasimp inspect clasetLib.empty_cs simpLib.empty_ss [once]
       in
         probe_goal tactic
       end)

val _ =
  check
    ("plain theorems are inserted before the clasimp script",
     fn () =>
       let
         val fact = Thm.REFL ``clasimp_insert_x:'a``
         fun leave_residue _ _ _ = Tactical.ALL_TAC
         val tactic =
           local_clasimp leave_residue clasetLib.empty_cs
             simpLib.empty_ss [fact]
       in
         case residual tactic ([], ``clasimp_insert_goal:bool``) of
             [([assumption], _)] => Term.aconv assumption (concl fact)
           | _ => false
       end)

(* A citation that is an implication takes the other route: it is a rule
   of the claset the script is handed, and the goal it runs on does not
   carry it as well. *)
val _ =
  check
    ("a supplied implication reaches the script as a rule instead",
     fn () =>
       let
         val p = ``clasimp_insert_p:bool``
         val fact = DISCH p (ASSUME p)
         val seen = ref ~1
         fun leave_residue cs _ _ =
           (seen := length (clasetLib.rules_of cs); Tactical.ALL_TAC)
         val tactic =
           local_clasimp leave_residue clasetLib.empty_cs
             simpLib.empty_ss [fact]
       in
         case residual tactic ([], ``clasimp_insert_goal:bool``) of
             [([], _)] => !seen = 1
           | _ => false
       end)

val _ =
  check
    ("Iff marker is temporary and solves through a clasimp tactic",
     fn () =>
       let
         val equivalence =
           CONJUNCT2 (CONJUNCT2 boolTheory.NOT_CLAUSES)
         val (left, right) =
           boolSyntax.dest_eq (concl equivalence)
         val goal = ([right], left)
         fun search cs ss _ =
           clasimpLib.CS_FASTFORCE_TAC cs ss
         fun tactic controls =
           local_clasimp search clasetLib.empty_cs simpLib.empty_ss controls
         val rules_before =
           length (clasetLib.rules_of (clasetLib.the_claset ()))
         val rewrite_before =
           Conv.QCONV
             (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [])
             iff_test_left
         val unavailable_before =
           tactic_fails (tactic []) goal
         val available =
           valid_closes
             (tactic
               [clasetLib.Iff equivalence]) goal
         val rules_after =
           length (clasetLib.rules_of (clasetLib.the_claset ()))
         val rewrite_after =
           Conv.QCONV
             (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [])
             iff_test_left
       in
         unavailable_before andalso available andalso
         tactic_fails (tactic []) goal andalso
         rules_before = rules_after andalso
         Term.aconv (concl rewrite_before) (concl rewrite_after)
       end)

val _ =
  check
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
           local_clasimp accept clasetLib.empty_cs simpLib.empty_ss controls
       in
         tactic_fails (tactic []) goal andalso
         valid_closes
           (tactic [markerLib.Abbr [QUOTE name]]) goal
       end)

val wrapper_ss =
  simpLib.++
    (simpLib.clear_rules (clasimpLib.clasimp_ss ()),
     simpLib.rewrites
       [CONJUNCT2 (CONJUNCT2 boolTheory.NOT_CLAUSES)])

val wrapper_goal : Abbrev.goal = ([], ``~F``)

val wrapper_rungs =
  [("add_simp_wrapper reaches the FAST unsafe rung",
    fn cs => NTactical.DETERM (classicalLib.CS_FAST_TAC cs),
    clasimpLib.add_simp_wrapper),
   ("add_simp_wrapper reaches the bounded depth rung",
    fn cs =>
      NTactical.DETERM
        (classicalLib.CS_DEPTH_SOLVE_TAC {dup = false} 1 cs),
    clasimpLib.add_simp_wrapper),
   ("add_safe_simp_wrapper reaches the SAFE rung",
    fn cs => NTactical.DETERM (classicalLib.CS_SAFE_TAC cs),
    clasimpLib.add_safe_simp_wrapper),
   ("add_safe_simp_wrapper reaches the CLARIFY rung",
    fn cs => NTactical.DETERM (classicalLib.CS_CLARIFY_TAC cs),
    clasimpLib.add_safe_simp_wrapper)]

fun wrapper_rung (name, rung, add_wrapper) =
  check
    (name,
     fn () =>
       tactic_fails (rung clasetLib.empty_cs) wrapper_goal andalso
       valid_closes
         (rung (add_wrapper wrapper_ss [] clasetLib.empty_cs))
         wrapper_goal)

val _ = List.app wrapper_rung wrapper_rungs

val wrapper_control_name =
  {Thy = "clasimpSelftest", Name = "wrapper_control"}

val wrapper_spare_name =
  {Thy = "clasimpSelftest", Name = "wrapper_spare"}

(* An atom the empty claset has no rule for, so that only its own rewrite
   can turn it into T. *)
val wrapper_spare_goal : Abbrev.goal =
  ([], ``EMPTY SUBSET (clasimp_wrapper_set : 'a set)``)

val wrapper_control_ss =
  simpLib.++
    (simpLib.clear_rules (clasimpLib.clasimp_ss ()),
     simpLib.named_rewrites_with_names "clasimp-wrapper-control"
       [(wrapper_control_name,
         CONJUNCT2 (CONJUNCT2 boolTheory.NOT_CLAUSES)),
        (wrapper_spare_name, pred_setTheory.EMPTY_SUBSET)])

(* [clasimpSelftest] names no loaded theory, and that is the point: a
   rewrite is excludable by the qualified name it was installed under
   whether or not that theory part is an ancestor of the one being built.

   Failing to close the goal is how the search reports both a control that
   took effect and a control the simp step refused -- [NTactical.LIFT]
   turns the refusal into the same "no result" -- so neither direction is
   asserted on its own.  Each name is excluded in turn, and each run must
   still close the other name's goal: a control that raised, or that never
   reached the embedded simp step, could not close one goal while losing
   the other. *)
val _ =
  check
    ("add_simp_wrapper passes controls to its embedded simp step",
     fn () =>
       let
         fun fast controls =
           NTactical.DETERM
             (classicalLib.CS_FAST_TAC
                (clasimpLib.add_simp_wrapper wrapper_control_ss controls
                   clasetLib.empty_cs))
         val without_control =
           [markerLib.Excl "clasimpSelftest.wrapper_control"]
         val without_spare =
           [markerLib.Excl "clasimpSelftest.wrapper_spare"]
       in
         valid_closes (fast []) wrapper_goal andalso
         valid_closes (fast []) wrapper_spare_goal andalso
         valid_closes (fast without_control) wrapper_spare_goal andalso
         tactic_fails (fast without_control) wrapper_goal andalso
         valid_closes (fast without_spare) wrapper_goal andalso
         tactic_fails (fast without_spare) wrapper_spare_goal
       end)

val _ =
  check
    ("re-adding a simp wrapper overwrites its named slot",
     fn () =>
       let
         val inert_ss =
           simpLib.clear_rules (clasimpLib.clasimp_ss ())
         val unsafe_cs =
           clasimpLib.add_simp_wrapper inert_ss []
             (clasimpLib.add_simp_wrapper wrapper_ss []
               clasetLib.empty_cs)
         val safe_cs =
           clasimpLib.add_safe_simp_wrapper inert_ss []
             (clasimpLib.add_safe_simp_wrapper wrapper_ss []
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
  check
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
           clasimpLib.add_safe_simp_wrapper ss [] clasetLib.empty_cs
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

val force_logic_goals : Abbrev.goal list =
  [([], ``((P ==> Q) /\ P) ==> Q``),
   ([], ``(!x:'a. P x ==> Q x) ==> P a ==> Q a``),
   ([], ``(P \/ Q) ==> (P ==> R) ==> (Q ==> R) ==> R``)]

val force_native_goals : Abbrev.goal list =
  [([], ``MEM (x:'a) (x :: xs)``),
   ([], ``THE (SOME (x:'a)) = x``),
   ([],
    ``((x:'a) IN (s UNION t)) =
      (x IN s \/ x IN t)``)]

val force_goals = force_logic_goals @ force_native_goals

val beta_force_goal : Abbrev.goal =
  ([], ``(\proposition. proposition)
          (((P ==> Q) /\ P) ==> Q)``)

val nested_beta_force_goal : Abbrev.goal =
  ([],
   ``((\left : 'a -> 'b option.
         \right : 'a -> 'b option.
         !key value.
           left key = SOME value ==> right key = SOME value)
       (\query. if query = x then NONE else f query)
       f)``)

val force_tactics =
  [("FASTFORCE_TAC", clasimpLib.FASTFORCE_TAC []),
   ("SLOWSIMP_TAC", clasimpLib.SLOWSIMP_TAC []),
   ("BESTSIMP_TAC", clasimpLib.BESTSIMP_TAC [])]

fun force_battery (name, tactic) =
  check
    (name ^ " solves logical and set/list/option batteries",
     fn () => List.all (valid_closes tactic) force_goals)

val _ = List.app force_battery force_tactics

val _ =
  check
    ("FORCE_TAC restores a beta-normalized target",
     fn () =>
       List.all
         (valid_closes (clasimpLib.FORCE_TAC []))
         [beta_force_goal, nested_beta_force_goal])

val _ =
  check
    ("AUTO_TAC restores an eta-normalized target",
     fn () =>
       case Tactical.VALID (clasimpLib.AUTO_TAC [])
              ([], ``(\value : bool. predicate value) = predicate``) of
           ([], validation) => (ignore (validation []); true)
         | _ => false)

(* Isabelle's higher-order patterns are matched modulo eta, so a rewrite
   rule about a partial application fires on a goal spelled as its
   eta-expansion.  HOL4 matches up to alpha and beta only, so the
   clasimpset carries ETA_ss to contract the goal first.  The rule is
   assumed here rather than taken from a seed, and it is handed to the
   simpset rather than to a tactic, because a search that sees the rule
   as an assumption closes such a goal without any eta step -- it is the
   rewriting that stops at the mismatch. *)
val eta_matching_rule =
  Thm.ASSUME
    ``!start count. EVERY eta_matching_p (GENLIST ($+ start) count)``

val eta_matching_goal =
  ``EVERY eta_matching_p (GENLIST (\offset. eta_matching_base + offset) len)``

val _ =
  check
    ("the clasimpset matches a rule across an eta step",
     fn () =>
       let
         val rewritten =
           simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [eta_matching_rule]
             eta_matching_goal
       in
         Term.aconv (boolSyntax.rhs (Thm.concl rewritten)) boolSyntax.T
       end
       handle Conv.UNCHANGED => false)

(* The same mismatch one spelling further on.  Isabelle normalises the
   numeral 1 to [Suc 0] -- One_nat_def is simp there -- so a rule stated
   on SUC fires against a goal that spells the number as a numeral.
   HOL4 normalises the other way, and the clasimpset carries
   SUC_FILTER_ss to derive the numeral-matching variant of a SUC rule as
   it enters.  The rule is assumed and handed to the simpset for the
   same reason as the eta case above. *)
val suc_matching_rule =
  Thm.ASSUME ``!count. suc_matching_f (SUC count) = suc_matching_g count``

val suc_matching_goal = ``suc_matching_f 3 = suc_matching_g 2``

val _ =
  check
    ("the clasimpset matches a rule across a numeral and SUC",
     fn () =>
       let
         val rewritten =
           simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [suc_matching_rule]
             suc_matching_goal
       in
         Term.aconv (boolSyntax.rhs (Thm.concl rewritten)) boolSyntax.T
       end
       handle Conv.UNCHANGED => false)

val extensional_search_goals : Abbrev.goal list =
  [([],
    ``(\value : 'a. left value /\ right value) =
      (\value. right value /\ left value)``),
   ([],
    ``(\first : 'a. \second : 'b.
          relation first second /\ guard first second) =
      (\first. \second.
          guard first second /\ relation first second)``)]

val _ =
  check
    ("AUTO and FORCE normalize nested function equality once",
     fn () =>
       List.all
         (valid_closes (clasimpLib.AUTO_TAC []))
         extensional_search_goals andalso
       List.all
         (valid_closes (clasimpLib.FORCE_TAC []))
         extensional_search_goals)

val context_force_tactics =
  [("CS_FASTFORCE_TAC", clasimpLib.CS_FASTFORCE_TAC),
   ("CS_SLOWSIMP_TAC", clasimpLib.CS_SLOWSIMP_TAC),
   ("CS_BESTSIMP_TAC", clasimpLib.CS_BESTSIMP_TAC)]

fun context_force_battery (name, tactic) =
  check
    (name ^ " uses the supplied claset and simpset",
     fn () =>
       List.all
         (valid_closes
            (tactic (clasetLib.the_claset ())
              (clasimpLib.clasimp_ss ())))
         force_logic_goals)

val _ = List.app context_force_battery context_force_tactics

val force_negative_goal : Abbrev.goal =
  ([], ``clasimp_force_unprovable:bool``)

fun force_must_close (name, tactic) =
  check
    (name ^ " fails instead of returning an open residue",
     fn () => tactic_fails tactic force_negative_goal)

val _ = List.app force_must_close force_tactics

val _ =
  List.app
    (fn (name, tactic) =>
      force_must_close
        (name,
         tactic (clasetLib.the_claset ())
           (clasimpLib.clasimp_ss ())))
    context_force_tactics

val _ =
  check
    ("CLARSIMP_TAC returns an exact non-closing residue",
     fn () =>
       let
         val goal = ([], ``clasimp_p ==> clasimp_q``)
         val expected =
           [([], ``clasimp_q:bool``)]
         val actual =
           residual (clasimpLib.CLARSIMP_TAC []) goal
       in
         same_goals actual expected
       end)

val _ =
  check
    ("CS_CLARSIMP_TAC uses the supplied claset and simpset",
     fn () =>
       valid_closes
         (clasimpLib.CS_CLARSIMP_TAC
            (clasetLib.the_claset ())
            (clasimpLib.clasimp_ss ()))
         ([], ``THE (SOME (clasimp_cs_x:'a)) =
                clasimp_cs_x``))

val _ =
  check
    ("CLARSIMP_TAC accepts simplification-only progress",
     fn () =>
       let
         val goal =
           ([], ``T /\ clasimp_simp_residue``)
         val expected =
           [([], ``clasimp_simp_residue:bool``)]
       in
         same_goals
           (residual (clasimpLib.CLARSIMP_TAC []) goal)
           expected
       end)

val _ =
  check
    ("CLARSIMP_TAC solves set/list/option simplification goals",
     fn () =>
       List.all
         (valid_closes (clasimpLib.CLARSIMP_TAC []))
         force_native_goals)

val _ =
  check
    ("CLARSIMP_TAC fails exactly when its script changes nothing",
     fn () =>
       tactic_fails
         (clasimpLib.CLARSIMP_TAC [])
         ([], ``clasimp_clarsimp_unchanged:bool``))

val _ =
  check
    ("CS_CLARSIMP_TAC fails exactly when its script changes nothing",
     fn () =>
       tactic_fails
         (clasimpLib.CS_CLARSIMP_TAC
            (clasetLib.the_claset ())
            (clasimpLib.clasimp_ss ()))
         ([], ``clasimp_cs_clarsimp_unchanged:bool``))

val _ =
  check
    ("CLARSIMP_TAC still splits a conditional assumption",
     fn () =>
       let
         val goal =
           ([``P (if b then x:'a else y) : bool``],
            ``clasimp_split_residue:bool``)
         val residues =
           residual (clasimpLib.CLARSIMP_TAC []) goal
         fun clean (assumptions, conclusion) =
           not
             (List.exists
                (can (find_term boolSyntax.is_cond))
                (conclusion :: assumptions))
       in
         length residues = 2 andalso List.all clean residues
       end)

val auto_logic_goals : Abbrev.goal list =
  [([], ``((P ==> Q) /\ P) ==> Q``),
   ([], ``(!x:'a. P x ==> Q x) ==> P a ==> Q a``),
   ([], ``(P \/ Q) ==> (P ==> R) ==> (Q ==> R) ==> R``),
   ([], ``(~P ==> P) ==> P``)]

val auto_native_goals : Abbrev.goal list =
  [([], ``MEM (x:'a) (x :: xs)``),
   ([], ``THE (SOME (x:'a)) = x``),
   ([],
    ``((x:'a) IN (s UNION t)) =
      (x IN s \/ x IN t)``)]

val auto_goals = auto_logic_goals @ auto_native_goals

val _ =
  check
    ("AUTO_TAC solves translated auto regressions and HOL4 goals",
     fn () =>
       List.all
         (valid_closes (clasimpLib.AUTO_TAC []))
         auto_goals)

(* A commuting assumption applied in the direction the term order does
   not take downwards.  Read schematically the rule is permutative and is
   refused; with its condition discharged from the goal's own assumption
   the terms it speaks of are local constants to matching, and what is
   left is an ordinary rewrite at one redex.  Only after it has fired
   does the conditional assumption close the goal -- the condition holds
   of [clasimp_perm_a], which the commutation moves into the argument
   that assumption reads.  Dropping the condition's assumption takes the
   instance away and nothing else closes the goal, which is what says the
   rewrite is doing the work.  Nothing here is a benchmark entry. *)
val permutation_rule =
  ``!x y : num. clasimp_perm_R x y ==> (x - y = y - x)``

val permutation_condition =
  ``clasimp_perm_R (clasimp_perm_a : num) (clasimp_perm_b : num) : bool``

val permutation_context =
  [``EVEN (clasimp_perm_a : num)``,
   ``!x y : num. EVEN y ==> EVEN (x - y)``]

val permutation_target =
  ``EVEN ((clasimp_perm_a : num) - (clasimp_perm_b : num))``

val _ =
  check
    ("AUTO_TAC commutes an assumption at the redex its condition pins",
     fn () =>
       valid_closes (clasimpLib.AUTO_TAC [])
         (permutation_rule :: permutation_condition :: permutation_context,
          permutation_target))

val _ =
  check
    ("AUTO_TAC leaves a commuting assumption alone with nothing to pin it",
     fn () =>
       let
         val goal = (permutation_rule :: permutation_context,
                     permutation_target)
       in
         tactic_fails (clasimpLib.AUTO_TAC []) goal orelse
         not (valid_closes (clasimpLib.AUTO_TAC []) goal)
       end)

val auto_linarith_rewrite =
  hd (Drule.CONJUNCTS arithmeticTheory.MIN_EQ_LE)

val auto_linarith_tactic =
  clasimpLib.AUTO_TAC
    [clasetLib.Simp auto_linarith_rewrite]

val auto_linarith_goal : Abbrev.goal =
  ([``(x:num) <= y``, ``y <= z``], ``MIN x z = x``)

val _ =
  check
    ("AUTO_TAC discharges a linear-arithmetic rewrite condition",
     fn () => valid_closes auto_linarith_tactic auto_linarith_goal)

val auto_arith_fact_goal : Abbrev.goal =
  ([``(x:num) ** 2 <= y``], ``MIN x y = x``)

val _ =
  check
    ("AUTO_TAC reads [arith] facts dynamically and leaves the set clean",
     fn () =>
       tactic_fails auto_linarith_tactic auto_arith_fact_goal andalso
       with_arith_fact
         (fn () =>
           valid_closes auto_linarith_tactic auto_arith_fact_goal) andalso
       tactic_fails auto_linarith_tactic auto_arith_fact_goal)

(* Isabelle's arithmetic simprocs answer an atom wherever the traversal
   meets one, so the layer's simpset carries a decision procedure beside
   its rewrites.  An implication between two bounds is a rewrite for
   nothing: only that procedure closes it. *)
val auto_arith_atom = ``~((m:num) < n) ==> ~(SUC m < n)``

val _ =
  check
    ("the simpset decides an arithmetic atom rewriting leaves standing",
     fn () =>
       aconv
         (boolSyntax.rhs (concl
            (Conv.QCONV
              (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [])
              auto_arith_atom)))
         boolSyntax.T)

(* The other half of that layer: deciding an atom is not normalising a
   term, and two spellings of one sum must not be left side by side for
   the search to rediscover. *)
val auto_arith_spellings =
  (``(x:num) + (y + z)``, ``(z:num) + (y + x)``)

val _ =
  check
    ("the simpset gives two spellings of a sum one normal form",
     fn () =>
       let
         fun normal_form tm =
           boolSyntax.rhs (concl
             (Conv.QCONV
               (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) []) tm))
       in
         aconv (normal_form (fst auto_arith_spellings))
               (normal_form (snd auto_arith_spellings))
       end)

val _ =
  check
    ("CS_AUTO_TAC uses the supplied claset and simpset",
     fn () =>
       List.all
         (valid_closes
            (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
              (clasetLib.the_claset ())
              (clasimpLib.clasimp_ss ())))
         auto_logic_goals)

val _ =
  check
    ("AUTO_DEPTH_TAC accepts explicit blast and depth bounds",
     fn () =>
       let
         val x = mk_var ("clasimp_auto_depth_x", Type.ind)
         val y = mk_var ("clasimp_auto_depth_y", Type.ind)
         val body =
           boolSyntax.mk_conj
             (boolSyntax.mk_eq (x, x), boolSyntax.mk_eq (y, y))
         val goal =
           ([], boolSyntax.mk_exists
             (x, boolSyntax.mk_exists (y, body)))
         fun auto blast =
           clasimpLib.CS_AUTO_TAC {blast = blast, depth = 0}
             (clasetLib.the_claset ()) simpLib.empty_ss
         val witness = mk_var ("clasimp_auto_witness", Type.ind)
         val constant = mk_var ("clasimp_auto_constant", Type.ind)
         val predicate =
           mk_var
             ("clasimp_auto_predicate", Type.ind --> Type.bool)
         val fact = mk_comb (predicate, constant)
         val depth_goal =
           ([fact], boolSyntax.mk_exists
             (witness, mk_comb (predicate, witness)))
         fun depth_auto depth =
           clasimpLib.CS_AUTO_TAC {blast = 0, depth = depth}
             (clasetLib.the_claset ()) simpLib.empty_ss
       in
         tactic_fails (auto 1) goal andalso
         valid_closes (auto 2) goal andalso
         tactic_fails (depth_auto 0) depth_goal andalso
         valid_closes (depth_auto 1) depth_goal andalso
         valid_closes
           (clasimpLib.AUTO_DEPTH_TAC {blast = 4, depth = 2} [])
           ([], ``(~clasimp_auto_bound_p ==>
                    clasimp_auto_bound_p) ==>
                   clasimp_auto_bound_p``)
       end)

val _ =
  check
    ("AUTO_TAC returns an exact non-closing residue",
     fn () =>
       let
         val goal =
           ([], ``clasimp_auto_p ==> clasimp_auto_q``)
         val expected =
           [([], ``clasimp_auto_q:bool``)]
       in
         same_goals
           (residual (clasimpLib.AUTO_TAC []) goal)
           expected
       end)

val _ =
  check
    ("AUTO_TAC fails exactly when its script changes nothing",
     fn () =>
       tactic_fails
         (clasimpLib.AUTO_TAC [])
         ([], ``clasimp_auto_unchanged:bool``))

val _ =
  check
    ("CS_AUTO_TAC fails exactly when its script changes nothing",
     fn () =>
       tactic_fails
         (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
            (clasetLib.the_claset ())
            (clasimpLib.clasimp_ss ()))
         ([], ``clasimp_cs_auto_unchanged:bool``))

val auto_idempotence_goals : Abbrev.goal list =
  [([], ``T /\ clasimp_auto_stable_a``),
   ([], ``clasimp_auto_stable_b ==> clasimp_auto_stable_c``),
   ([``P (if clasimp_auto_stable_b then x:'a else y) : bool``],
    ``clasimp_auto_stable_d:bool``)]

val _ =
  check
    ("AUTO_TAC residues are idempotent without blast instantiations",
     fn () =>
       List.all
         (fn goal =>
           let
             val residues =
               residual (clasimpLib.AUTO_TAC []) goal
           in
             not (null residues) andalso
             List.all
               (tactic_fails (clasimpLib.AUTO_TAC []))
               residues
           end)
         auto_idempotence_goals)

fun goal_has_cond (assumptions, conclusion) =
  List.exists
    (can (find_term boolSyntax.is_cond))
    (conclusion :: assumptions)

val _ =
  check
    ("AUTO_TAC splits if where srw_ss simplification does not",
     fn () =>
       let
         val goal =
           ([``P (if clasimp_auto_split_b then
                    clasimp_auto_split_x:'a
                  else clasimp_auto_split_y) : bool``],
            ``clasimp_auto_split_result:bool``)
         val plain =
           residual
             (simpLib.SIMP_TAC (BasicProvers.srw_ss ()) [])
             goal
         val automatic =
           residual (clasimpLib.AUTO_TAC []) goal
       in
         case plain of
             [residue] =>
               goal_has_cond residue andalso
               length automatic = 2 andalso
               not (List.exists goal_has_cond automatic)
           | _ => false
       end)

val _ =
  check
    ("AUTO_TAC splits datatype cases where srw_ss does not",
     fn () =>
       let
         val goal =
           ([``P (case xs:'a list of
                    [] => clasimp_auto_case_x
                  | h::t => clasimp_auto_case_y) : bool``],
            ``clasimp_auto_case_result:bool``)
         val plain =
           residual
             (simpLib.SIMP_TAC (BasicProvers.srw_ss ()) [])
             goal
         val automatic =
           residual (clasimpLib.AUTO_TAC []) goal
         fun has_case (assumptions, conclusion) =
           List.exists
             (can (find_term TypeBase.is_case))
             (conclusion :: assumptions)
       in
         case plain of
             [residue] =>
               has_case residue andalso
               length automatic = 2 andalso
               not (List.exists has_case automatic)
           | _ => false
       end)

val _ =
  check
    ("FORCE_TAC solves translated force regressions and HOL4 goals",
     fn () =>
       List.all
         (valid_closes (clasimpLib.FORCE_TAC []))
         force_goals)

val _ =
  check
    ("CS_FORCE_TAC uses the supplied claset and simpset",
     fn () =>
       List.all
         (valid_closes
            (clasimpLib.CS_FORCE_TAC
              (clasetLib.the_claset ())
              (clasimpLib.clasimp_ss ())))
         force_goals)

val _ =
  check
    ("FORCE_TAC and CS_FORCE_TAC fail unless they close the goal",
     fn () =>
       tactic_fails
         (clasimpLib.FORCE_TAC [])
         force_negative_goal andalso
       tactic_fails
         (clasimpLib.CS_FORCE_TAC
            (clasetLib.the_claset ())
            (clasimpLib.clasimp_ss ()))
         force_negative_goal)

val force_witness_goals : (string * tactic * Abbrev.goal) list =
  [("complement",
    clasimpLib.FORCE_TAC [],
    ([``value = COMPL (candidate : 'a set)``],
     ``?witness : 'a set. value = COMPL witness``)),
   ("option case",
    clasimpLib.FORCE_TAC [],
    ([],
     ``(if flag then NONE else SOME (value : 'a)) = NONE \/
       ?witness.
         (if flag then NONE else SOME value) = SOME witness``))]

val _ =
  List.app
    (fn (name, tactic, goal) =>
      check
        ("FORCE synthesizes a " ^ name ^ " witness",
         fn () => valid_closes tactic goal))
    force_witness_goals

(* Isabelle's force_tac ends in first_best_tac alone: the method carries
   no tableau leg at all (src/Provers/clasimp.ML:167 @ Isabelle2025-2).
   Ours keeps one, but behind the parity leg rather than in front of it.
   The goal below is a partial map read at two points -- the shape
   Isabelle closes with force and with nothing weaker, neither simp nor
   fastforce nor blast.  Best-first closes it in milliseconds; the
   tableau does not return on it, so with the legs the other way round
   the budget is spent before the leg that carries the parity is
   reached.  The bound is what makes that a failure rather than a hang. *)
val force_partial_map_goal : Abbrev.goal =
  ([``(force_m : 'a -> 'b option) force_x = SOME force_e``,
    ``(force_m : 'a -> 'b option) force_a = NONE``],
   ``?k. (k = force_a ==> force_b = force_e) /\
         (k <> force_a ==> (force_m : 'a -> 'b option) k = SOME force_e)``)

val _ =
  check
    ("FORCE closes a partial-map goal its tableau leg does not return on",
     fn () =>
       Lib.total
         (Timeout.apply (Time.fromSeconds 30)
            (valid_closes (clasimpLib.FORCE_TAC [])))
         force_partial_map_goal = SOME true)

val staged_branch_goal : Abbrev.goal =
  ([``branch_a1 \/ branch_b1``,
    ``branch_a2 \/ branch_b2``,
    ``branch_a3 \/ branch_b3``,
    ``branch_a4 \/ branch_b4``,
    ``decision ==> result``, ``~decision ==> result``],
   ``result:bool``)

val _ =
  check
    ("staged AUTO and FORCE bypass irrelevant satisfiable branches",
     fn () =>
       valid_closes (clasimpLib.AUTO_TAC []) staged_branch_goal andalso
       valid_closes (clasimpLib.FORCE_TAC []) staged_branch_goal)

val _ =
  check
    ("AUTO_TAC arguments are temporary and leave no state behind",
     fn () =>
       let
         val lhs = ``clasimp_temporary_lhs:'a``
         val goal =
           ([], ``clasimp_temporary_goal:bool``)
         val rules_before =
           length (clasetLib.rules_of (clasetLib.the_claset ()))
         val before_conv =
           Conv.QCONV
             (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [])
             lhs
         val failed =
           tactic_fails
             (clasimpLib.AUTO_TAC
               [clasetLib.Simp boolTheory.IMP_CLAUSES])
             goal
         val after_conv =
           Conv.QCONV
             (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [])
             lhs
         val rules_after =
           length (clasetLib.rules_of (clasetLib.the_claset ()))
       in
         failed andalso rules_before = rules_after andalso
         aconv (concl before_conv) (concl after_conv)
       end)

(* An assumption the safe cascade has just stripped must not be rebuilt
   into the conclusion.  The cascade's negation introduction turns a
   goal [~p] into [p |- F], and a simplification that re-forms [p ==> F]
   as [~p] hands the two steps a cycle; safe saturation repeats while
   any step applies, so it never leaves that cycle.  The goal below is
   unprovable -- what is asserted is that the tactic returns at all. *)
val cascade_cycle_goal : goal =
  ([] : term list, ``!x. cycle_q (x:'a) ==> ~cycle_p x``)

val _ =
  check
    ("safe simplification does not undo the cascade's negation step",
     fn () =>
       let
         fun run () =
           (ignore (clasimpLib.AUTO_TAC [] cascade_cycle_goal); true)
           handle HOL_ERR _ => true
       in
         Timeout.apply (Time.fromSeconds 30) run ()
         handle Timeout.TIMEOUT _ => false
       end)

(* The order procedure is in the stack.  This goal is closed by
   chaining two steps the assumptions state through an order the goal
   itself supplies, and nothing else in the stack chains: HOL4 carries
   no order reasoning ambiently, and the premise gives the axioms
   rather than the step.  It is not a benchmark entry. *)
val order_chaining_goal : goal =
  ([] : term list,
   ``!le a b c.
       relation$WeakLinearOrder le ==> le a b ==> le b c ==> le a c``)

val _ =
  check
    ("AUTO_TAC chains a step in an order the goal supplies",
     fn () => valid_closes (clasimpLib.AUTO_TAC []) order_chaining_goal)

(* The second position the same procedure is asked about: the rewrite
   in the assumptions fires on the conclusion only once its order
   premise is discharged, and the chain that discharges it is the one
   above.  A side condition is simplified with this simpset, so the
   decision procedure reaches it and no separate solver is wired. *)
val order_condition_goal : goal =
  ([] : term list,
   ``!le a b c.
       relation$WeakLinearOrder le ==>
       (!x y. le x y ==> (clasimp_order_f x y <=> T)) ==>
       le a b ==> le b c ==> clasimp_order_f a c``)

val _ =
  check
    ("a conditional rewrite's order premise is discharged",
     fn () => valid_closes (clasimpLib.AUTO_TAC []) order_condition_goal)

(* A first-order step meets a goal the simplification before it left in
   the ambient normal form, and a fact stated some other way misses it.
   The two constants below are the same function, and the rewrite
   between them is the normal form; the fact is stated in the spelling
   the normal form leaves behind, and the goal in the one it produces. *)
val ambient_form_left =
  Definition.new_definition
    ("clasimp_ambient_left_def", ``clasimp_ambient_left (x:'a) = x``)

val ambient_form_right =
  Definition.new_definition
    ("clasimp_ambient_right_def", ``clasimp_ambient_right (x:'a) = x``)

val ambient_variable = mk_var ("x", alpha)

val ambient_normal_form =
  GEN ambient_variable
    (TRANS (SPEC ambient_variable ambient_form_left)
       (SYM (SPEC ambient_variable ambient_form_right)))

val ambient_normalized_goal : goal =
  ([] : term list, ``clasimp_ambient_right (a:'a) = a``)

val _ =
  BasicProvers.augment_srw_ss
    [simpLib.named_rewrites "clasimpAmbientProbe" [ambient_normal_form]]

val _ =
  check
    ("a fact reaches the goal its own spelling misses",
     fn () =>
       tactic_fails (metisLib.METIS_TAC [ambient_form_left])
         ambient_normalized_goal andalso
       valid_closes (clasimpLib.AMBIENT_METIS_TAC [ambient_form_left])
         ambient_normalized_goal)

val _ = BasicProvers.diminish_srw_ss ["clasimpAmbientProbe"]

(* A first-order search instantiates a function variable with an
   abstraction and then has no rule to reduce the redex that leaves, so
   the fact below is unusable in its own goal until the abstraction is
   named.  The constant is local and the goal is not a benchmark entry:
   what is asserted is that naming the abstraction is what closes it. *)
val lifted_application_def =
  Definition.new_definition
    ("clasimp_lifted_application_def",
     ``clasimp_lifted_application (predicate:'a -> bool) (element:'a) =
         predicate element``)

val lifted_application_goal : goal =
  ([], ``clasimp_lifted_application (\y. p y /\ q y) (a:'a) ==> p a``)

val _ =
  check
    ("naming an abstraction lets a fact instantiate a function variable",
     fn () =>
       tactic_fails (metisLib.METIS_TAC [lifted_application_def])
         lifted_application_goal andalso
       valid_closes
         (Tactical.THEN
            (clasimpLib.LAMBDA_LIFT_TAC,
             metisLib.METIS_TAC [lifted_application_def]))
         lifted_application_goal andalso
       valid_closes
         (clasimpLib.AMBIENT_METIS_TAC [lifted_application_def])
         lifted_application_goal)

(* Nothing stands in an argument position, so there is nothing to name
   and the step refuses rather than reproducing the goal. *)
val _ =
  check
    ("the lifting step refuses a goal with no argument abstraction",
     fn () =>
       tactic_fails clasimpLib.LAMBDA_LIFT_TAC
         ([], ``!x:'a. p x ==> q x ==> p x``))

(* What the exclusion drops is a cancellation step the source's simpset
   also takes, so the layer runs HOL4's procedure and respells what it
   returns.  None of the terms below is a benchmark entry. *)
fun simplifies term =
  SOME (boolSyntax.rhs
          (Thm.concl (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) [] term)))
  handle Conv.UNCHANGED => NONE

val _ =
  check
    ("the layer does not renest an append the way HOL4 does",
     fn () =>
       let
         val term = ``(as:'a list) ++ (bs ++ cs)``
         fun renests ss =
           (ignore (simpLib.SIMP_CONV ss [] term); true)
           handle Conv.UNCHANGED => false
       in
         renests (BasicProvers.srw_ss ()) andalso
         not (renests (clasimpLib.clasimp_ss ()))
       end)

val _ =
  check
    ("an equation with nothing to cancel is left as it stands",
     fn () =>
       not (isSome (simplifies ``(as:'a list) ++ (bs ++ cs) = ds``)))

(* A common prefix cancels by APPEND_11, which is ambient; matching two
   equations up by their last element is the procedure's own step and
   no rewrite reaches it. *)
val _ =
  check
    ("two equations are still matched up by their last element",
     fn () =>
       case simplifies ``(xs:'a list) ++ [x] = ys ++ [y]`` of
           SOME result =>
             aconv result ``(xs:'a list) = ys /\ (x:'a) = y``
         | NONE => false)

(* The cancellation is HOL4's and leaves what it returns left-nested;
   what this asserts is the respelling that follows it. *)
val _ =
  check
    ("what cancelling leaves is spelled the way the source states it",
     fn () =>
       case simplifies
              ``((as:'a list) ++ (bs ++ cs)) ++ [x] = ds ++ [y]`` of
           SOME result =>
             aconv result
               ``((as:'a list) ++ (bs ++ cs) = ds) /\ (x:'a) = y``
         | NONE => false)

(* One statement written twice.  The HOL4 result answering an Isabelle
   one states the same fact in its own conjunct order and on its own
   side of an equation, and the residual is then an equivalence between
   a term and a permutation of itself.  The decision closes it; it does
   not reorder anything, which is what the two assertions above depend
   on.  None of the terms below is a benchmark entry. *)
val _ =
  check
    ("an equivalence between two permutations of one statement closes",
     fn () =>
       List.all
         (fn term =>
           case simplifies term of
               SOME result => aconv result boolSyntax.T
             | NONE => false)
         [``(clasimp_perm_y = clasimp_perm_x) /\ 0 < clasimp_perm_n <=>
            (clasimp_perm_x = clasimp_perm_y) /\ 0 < clasimp_perm_n``,
          ``0 < clasimp_perm_n /\ clasimp_perm_p clasimp_perm_a <=>
            clasimp_perm_p clasimp_perm_a /\ 0 < clasimp_perm_n``,
          ``(?value.
               clasimp_perm_opt = SOME value /\
               clasimp_perm_y = clasimp_perm_f value) <=>
            ?value.
              clasimp_perm_opt = SOME value /\
              clasimp_perm_f value = clasimp_perm_y``])

val _ =
  check
    ("an equivalence that is not a permutation is left alone",
     fn () =>
       not (isSome (simplifies
         ``(clasimp_perm_p /\ clasimp_perm_q) <=>
           (clasimp_perm_p \/ clasimp_perm_q)``)))

(* src/HOL/HOL.thy declares [disj_not1] simp and HOL4 declares nothing
   in either direction, so a negated existential arrives at a source
   rule as a disjunction where the source states it as an implication.
   The rule below is hypothetical rather than proved: what is under
   test is the shape the simplifier hands its condition solver, and the
   goal is not a benchmark entry. *)
val membership_condition_rule =
  Thm.ASSUME
    ``!xs. (!i. MEM i xs ==> q i) ==> walk (xs:'a list) = xs``

val _ =
  check
    ("a negated existential premise reads as an implication",
     fn () =>
       case simplifies ``~(?i. MEM i (xs:'a list) /\ P i)`` of
           SOME result =>
             aconv result ``!i. MEM i (xs:'a list) ==> ~P i``
         | NONE => false)

val _ =
  check
    ("a side condition is discharged from a negated existential",
     fn () =>
       let
         val (subgoals, _) =
           clasimpLib.asm_full_simp (clasimpLib.clasimp_ss ())
             [membership_condition_rule]
             ([``~(?i. MEM i (as:'a list) /\ ~q i)``],
              ``walk (as:'a list) = as``)
             (Context.snapshot())
       in
         null subgoals
       end)

(* HOL4's simplifier rewrites outermost-first and Isabelle's the other way
   round, and the two differ wherever an ambient rule matches a whole term
   whose subterm the context has already settled.  Below the context
   settles [TAKE n l] to the empty list while the ambient identity matches
   the whole [TAKE n l ++ DROP n l]: taken outermost-first the inserted
   instance collapses to T and the goal loses the equation that would
   close it.  The simpset carries the identity and the empty append and
   nothing else, so no case analysis on the assumption stands in for the
   equation, and the goal is not a benchmark entry. *)
val traversal_ss =
  simpLib.++
    (simpLib.empty_ss,
     simpLib.rewrites [listTheory.TAKE_DROP, CONJUNCT1 listTheory.APPEND])

val traversal_goal : Abbrev.goal =
  ([``TAKE n (l:'a list) ++ DROP n l = l``, ``TAKE n (l:'a list) = []``],
   ``DROP n (l:'a list) = l``)

val _ =
  check
    ("a context equation refines a term the ambient rule would collapse",
     fn () =>
       valid_closes
         (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
            clasetLib.empty_cs traversal_ss)
         traversal_goal)

(* The same divergence the other way round: here the redex the ambient
   rule swallows is one a rule the invocation named would have refined.
   [MEM x (REPLICATE n a)] is a membership the ambient decomposition
   matches whole, and [set (REPLICATE n a)] -- what the rule below is
   stated on -- is a subterm of it, so outermost-first the rule never
   fires and the [if] it would have built is never there to split.  With
   it built the case split carries [n = 0] across the whole goal, which
   is what settles the disjunct on the other side of it.  The goal is
   not a benchmark entry. *)
val replicate_set_rule =
  Tactical.prove
    (``!n (value : 'a).
         LIST_TO_SET (REPLICATE n value) =
         if n = 0 then {} else {value}``,
     Tactical.THEN
       (bossLib.Induct,
        Tactical.THEN
          (BasicProvers.SRW_TAC []
             [rich_listTheory.REPLICATE, pred_setTheory.EXTENSION],
           bossLib.metis_tac [])))

val supplied_subterm_goal : Abbrev.goal =
  ([], ``(!clasimp_replicate_x.
            MEM clasimp_replicate_x
                (REPLICATE clasimp_replicate_n (clasimp_replicate_a : 'a)) ==>
            clasimp_replicate_P clasimp_replicate_x) ==>
         clasimp_replicate_n = 0 \/
         clasimp_replicate_P clasimp_replicate_a``)

val _ =
  check
    ("a supplied rewrite refines a subterm the ambient rule would swallow",
     fn () =>
       let
         val (subgoals, _) =
           clasimpLib.asm_full_simp (clasimpLib.clasimp_ss ())
             [replicate_set_rule] supplied_subterm_goal
             (Context.snapshot())
       in
         null subgoals
       end)

(* A tactic that reports no proof has come back, which is what the bound
   below is about; only the timeout distinguishes the two outcomes. *)
fun terminates_within seconds tactic goal =
  (Timeout.apply (Time.fromSeconds seconds)
     (fn () => (ignore (Tactical.VALID tactic goal) handle HOL_ERR _ => ()))
     ();
   true)
  handle Timeout.TIMEOUT _ => false

(* A case analysis on a walk leaves an equation that reproduces its own
   left-hand side among the assumptions.  Read as the invocation's own
   simpset reads it the pass stands it down, the canonicalisation
   recognising a rewrite that would loop; read raw -- an empty simpset
   keeps an assumption as it finds it -- the same equation rewrites
   forever.  The goal is not a benchmark entry and what is asserted is
   that the tactic comes back at all. *)
val self_referential_goal : Abbrev.goal =
  ([``(clasimp_walk_P : 'a -> bool) clasimp_walk_x``,
    ``(clasimp_walk_xs : 'a list) =
        takeWhile ($~ o clasimp_walk_P) clasimp_walk_xs ++
        clasimp_walk_x::clasimp_walk_rest``],
   ``?clasimp_walk_value.
       MEM clasimp_walk_value (clasimp_walk_xs : 'a list) /\
       clasimp_walk_P clasimp_walk_value``)

val _ =
  check
    ("a context equation that reproduces itself does not rewrite forever",
     fn () =>
       terminates_within 30
         (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
            clasetLib.empty_cs (clasimpLib.clasimp_ss ()))
         self_referential_goal)

(* The library states [FUNPOW f 0 x = x] where the source states
   [f ^^ 0 = id], so the goal below and the rule that settles it are the
   same fact at different arities and no rewrite brings them together.
   Neither goal is a benchmark entry.  The first is put to simplification
   alone, which is the method the source's own [simp] names; the search
   tactics reach the same goal through their own root-only
   normalisation, so it says nothing about them. *)
val extensional_goal : Abbrev.goal =
  ([], ``FUNPOW SUC 0 = (I : num -> num)``)

val _ =
  check
    ("an equation between functions meets the applied law that settles it",
     fn () =>
       valid_closes
         (clasimpLib.with_extensionality (clasimpLib.clasimp_ss ())
            (clasimpLib.asm_full_simp (clasimpLib.clasimp_ss ()) []))
         extensional_goal)

(* Simplification leaves the equation under whatever quantifiers and
   implications the goal carried, so the step is looked for there and
   not only at the conclusion's root.  The goal below arrives as neither
   -- it is a quantified implication, which the root-only normalisation
   the search tactics run first declines -- and the equation appears
   only once simplification has stripped it. *)
val nested_extensional_goal : Abbrev.goal =
  ([], ``!clasimp_ext_k.
           (!n. (clasimp_ext_f : num -> num -> num) clasimp_ext_k n =
                clasimp_ext_g clasimp_ext_k n) ==>
           clasimp_ext_f clasimp_ext_k = clasimp_ext_g clasimp_ext_k``)

val _ =
  check
    ("the equation is found under the quantifiers the goal carries",
     fn () =>
       valid_closes
         (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
            clasetLib.empty_cs (clasimpLib.clasimp_ss ()))
         nested_extensional_goal)

(* HOL4 states its set and list facts on [x IN s] -- [x IN set l] is
   [MEM x l] itself -- while an equation taken pointwise as an application
   produces [set (FILTER P xs) x], which none of those facts meet.  Neither
   reading below is a benchmark entry.  The first is put to simplification
   alone, which is the method the source's own [simp] names; the second
   reaches the same reading through the root-only normalisation the search
   tactics run first.  MEM_FILTER is named because it is not ambient in the
   bare simpset the layer's own tests run against; what is under test is
   the reading the equation is given, not which membership facts are
   declared. *)
val membership_goal : Abbrev.goal =
  ([], ``(\clasimp_member. clasimp_ext_p clasimp_member /\
                           MEM clasimp_member clasimp_ext_xs) =
         set (FILTER clasimp_ext_p clasimp_ext_xs)``)

val membership_ss =
  simpLib.++ (BasicProvers.srw_ss (),
              simpLib.rewrites [listTheory.MEM_FILTER])

val _ =
  check
    ("an equation between sets meets the rules stated on membership",
     fn () =>
       valid_closes
         (clasimpLib.with_extensionality membership_ss
            (clasimpLib.asm_full_simp membership_ss []))
         membership_goal)

val _ =
  check
    ("the search tactics reach the membership reading as well",
     fn () =>
       valid_closes
         (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
            clasetLib.empty_cs membership_ss)
         membership_goal)

(* The other side of the same choice: where neither side of the equation
   is a set HOL4 states facts about, the applied reading is the one the
   goal's own context is in.  The goal is not a benchmark entry; the
   source's [Collect_cong] is the shape it stands for. *)
val applied_goal : Abbrev.goal =
  ([``!clasimp_ext_element.
        clasimp_ext_p clasimp_ext_element <=>
        clasimp_ext_q clasimp_ext_element /\
        clasimp_ext_r clasimp_ext_element``],
   ``(clasimp_ext_p : 'a -> bool) =
     \clasimp_member.
       clasimp_ext_q clasimp_member /\ clasimp_ext_r clasimp_member``)

val _ =
  check
    ("an equation between predicates keeps the reading its context has",
     fn () =>
       valid_closes
         (clasimpLib.with_extensionality (BasicProvers.srw_ss ())
            (clasimpLib.asm_full_simp (BasicProvers.srw_ss ()) []))
         applied_goal)

(* The reading is this layer's default and not the invocation's.
   [EVERY clasimp_ext_p] is constant-headed at [-> bool] and is no set:
   it is a predicate short of an argument, and every fact about it is
   stated applied, so the default membership reading leaves
   [clasimp_member IN EVERY clasimp_ext_p], which nothing meets.  The
   rewrites below are what a method naming [fun_eq_iff] and
   [list_all_iff] supplies, and they say which reading the equation is
   to be taken in; taken first, the default would put the equation out
   of their reach for good.  Neither the goal nor the rewrites are a
   benchmark entry. *)
val supplied_reading_goal : Abbrev.goal =
  ([], ``EVERY (clasimp_ext_p : 'a -> bool) =
         \clasimp_member.
           !clasimp_element.
             MEM clasimp_element clasimp_member ==>
             clasimp_ext_p clasimp_element``)

val supplied_reading_ss =
  simpLib.++ (BasicProvers.srw_ss (),
              simpLib.rewrites
                [boolTheory.FUN_EQ_THM, listTheory.EVERY_MEM])

val _ =
  check
    ("a supplied rewrite decides the reading of an equation",
     fn () =>
       valid_closes
         (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
            clasetLib.empty_cs supplied_reading_ss)
         supplied_reading_goal)

(* Which reading the default takes is decided by the head, not by the
   head being a constant.  [EVERY clasimp_ext_q] is constant-headed at
   [-> bool] and is no set: the simpset states no membership fact about
   it -- no rewrite of its own has [_ IN EVERY ...] for a left-hand side
   -- and every fact it does state is applied, so read as a membership
   the equation meets none of them.  The rewrite below is what a method
   naming [list_all_iff] supplies, and it says nothing about the
   reading; the applied one has to be the default's own choice.  Neither
   the goal nor the rewrite is a benchmark entry. *)
val predicate_reading_goal : Abbrev.goal =
  ([], ``EVERY (clasimp_ext_q : 'a -> bool) =
         \clasimp_subject.
           !clasimp_item.
             MEM clasimp_item clasimp_subject ==>
             clasimp_ext_q clasimp_item``)

val predicate_reading_ss =
  simpLib.++ (BasicProvers.srw_ss (),
              simpLib.rewrites [listTheory.EVERY_MEM])

val _ =
  check
    ("a predicate short of an argument is read applied, not as a set",
     fn () =>
       valid_closes
         (clasimpLib.CS_AUTO_TAC {blast = 4, depth = 2}
            clasetLib.empty_cs predicate_reading_ss)
         predicate_reading_goal)
