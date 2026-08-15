open HolKernel testutils
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
         val p = ``clasimp_insert_p:bool``
         val fact = DISCH p (ASSUME p)
         fun leave_residue _ _ _ = Tactical.ALL_TAC
         val tactic =
           local_clasimp leave_residue clasetLib.empty_cs
             simpLib.empty_ss [fact]
       in
         case residual tactic ([], ``clasimp_insert_goal:bool``) of
             [([assumption], _)] => Term.aconv assumption (concl fact)
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
