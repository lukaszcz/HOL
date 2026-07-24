open HolKernel Parse Tactic testutils boolSyntax
open NTactical clasetNet clasetRules clasetLib clasetSeedTheory

fun test (name, check) =
  (tprint name;
   if check () then OK () else die "failed")

(* This deliberately precedes the first [the_claset] demand below. *)
val _ = Datatype.Datatype
  `claset_hook_before_demand = ClasetHookA | ClasetHookB num`

fun same_seed_spec
  ({kind = kind1, safe = safe1, prio = prio1} : rulespec)
  ({kind = kind2, safe = safe2, prio = prio2} : rulespec) =
  kind1 = kind2 andalso safe1 = safe2 andalso prio1 = prio2

val seed_initialisation_start = Time.now ()
val seed_claset = the_claset ()
val seed_initialisation_time =
  Time.- (Time.now (), seed_initialisation_start)

val seed_sintro_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE}
val seed_intro_spec =
  {kind = clasetRules.Intro, safe = false, prio = NONE}
val seed_selim_spec =
  {kind = clasetRules.Elim, safe = true, prio = NONE}
val seed_elim_spec =
  {kind = clasetRules.Elim, safe = false, prio = NONE}

val seed_expected_rules =
  [(seed_sintro_spec, "bool$TRUTH"),
   (seed_sintro_spec, "bool$EQ_REFL"),
   (seed_sintro_spec, "clasetSeed$DISJ_CINTRO_THM"),
   (seed_sintro_spec, "bool$IMP_F"),
   (seed_sintro_spec, "clasetSeed$EX_EX1_INTRO_THM"),
   (seed_sintro_spec, "bool$AND_INTRO_THM"),
   (seed_sintro_spec, "bool$IMP_ANTISYM_AX"),
   (seed_selim_spec, "bool$FALSITY"),
   (seed_selim_spec, "clasetSeed$EX1_ELIM_THM"),
   (seed_selim_spec, "clasetSeed$EXISTS_ELIM_THM"),
   (seed_selim_spec, "clasetSeed$CONJ_ELIM_THM"),
   (seed_selim_spec, "clasetSeed$IFF_CELIM_THM"),
   (seed_selim_spec, "clasetSeed$IMP_CELIM_THM"),
   (seed_selim_spec, "bool$OR_ELIM_THM"),
   (seed_intro_spec, "clasetSeed$EXISTS_INTRO_THM"),
   (seed_intro_spec, "bool$EQ_EXT"),
   (seed_intro_spec, "clasetSeed$EX1_INTRO_THM"),
   (seed_elim_spec, "clasetSeed$FORALL_ELIM_THM")]

val seed_theory_name = "clasetSeed"

fun seed_export_identity name = seed_theory_name ^ "$" ^ name

val seed_programmatic_schemas =
  map seed_export_identity
    ["NOT_IMP_CELIM_THM", "NOT_FORALL_CELIM_THM", "NOT_ELIM_THM"]

fun untagged_theorems
  {theorem_names, persistent_rule_names, permitted} =
  let
    fun classified name =
      List.exists
        (fn rule_name => rule_name = name) persistent_rule_names orelse
      List.exists (fn permitted_name => permitted_name = name) permitted
  in
    List.filter (not o classified) theorem_names
  end

val _ =
  test
    ("seed classification requires fully qualified persistent rule names",
     fn () =>
       untagged_theorems
         {theorem_names =
            map seed_export_identity ["TAGGED", "NOT_ELIM_THM", "UNTAGGED"],
          persistent_rule_names =
            [seed_export_identity "TAGGED", "foreign$UNTAGGED"],
          permitted = seed_programmatic_schemas} =
       [seed_export_identity "UNTAGGED"])

val persisted_seed_claset =
  case persistent_claset_of_theory {thyname = seed_theory_name} of
      SOME cs => cs
    | NONE => raise Fail "clasetSeed has no persisted claset data"

val untagged_seed_theorems =
  untagged_theorems
    {theorem_names =
       map (seed_export_identity o #1) (DB.theorems seed_theory_name),
     persistent_rule_names = map (#1 o #2) (rules_of persisted_seed_claset),
     permitted = seed_programmatic_schemas}

val _ =
  (tprint "every seed theorem is a claset rule or permitted schema";
   case untagged_seed_theorems of
       [] => OK ()
     | names =>
         die ("untagged clasetSeed theorem(s): " ^
              String.concatWith ", " names))

fun is_seed_rule (_, (name, _)) =
  List.exists (fn (_, expected_name) => name = expected_name)
    seed_expected_rules

val _ =
  test
    ("seed claset contains the HOL.thy rules in canonical order",
     fn () =>
       ListPair.allEq
         (fn ((spec, (name, _)), (expected_spec, expected_name)) =>
            name = expected_name andalso same_seed_spec spec expected_spec)
         (List.filter is_seed_rule (rules_of seed_claset), seed_expected_rules)
       andalso
       not (List.exists
              (fn (_, (name, _)) => name = "clasetSeed$NOT_ELIM_THM")
              (rules_of seed_claset)))

val _ =
  test
    ("seed claset initialisation stays within its load-time budget",
     fn () => Time.< (seed_initialisation_time, Time.fromSeconds 30))

fun same_terms ts1 ts2 =
  ListPair.allEq (fn (tm1, tm2) => Term.aconv tm1 tm2) (ts1, ts2)

fun labelled tm _ =
  seq.result ([([], tm)], fn _ => ASSUME tm)

fun labels tac goal =
  map
    (fn (gs, _) =>
       case gs of
           [(_, tm)] => tm
         | _ => raise Fail "labelled tactic did not return one goal")
    (seq.take 10 (tac goal))

val p = ``p : bool``
val q = ``q : bool``
val r = ``r : bool``
val label_goal = ([], p)

val _ =
  test
    ("NORELSE is associative",
     fn () =>
       same_terms
         (labels (NORELSE (NORELSE (labelled p, labelled q), labelled r))
            label_goal)
         (labels (NORELSE (labelled p, NORELSE (labelled q, labelled r)))
            label_goal))

val _ =
  test
    ("NAPPEND is associative",
     fn () =>
       same_terms
         (labels (NAPPEND (NAPPEND (labelled p, labelled q), labelled r))
            label_goal)
         (labels (NAPPEND (labelled p, NAPPEND (labelled q, labelled r)))
            label_goal))

val choice_goal = ([p], p)
val close = LIFT (Tactical.FIRST_ASSUM ACCEPT_TAC)

val _ =
  test
    ("NORELSE does not backtrack after later failure",
     fn () =>
       seq.null
         (NTHEN (NORELSE (NALL_TAC, close), NNO_TAC) choice_goal))

val _ =
  test
    ("NAPPEND backtracks after later failure",
     fn () =>
       not
         (seq.null
            (NTHEN (NAPPEND (NALL_TAC, close), NNO_TAC) choice_goal)))

val _ =
  let
    fun diverging_branch _ =
      let fun loop () = loop () in loop () end
    val _ = seq.hd (NORELSE (NALL_TAC, diverging_branch) choice_goal)
  in
    test ("NORELSE leaves a diverging second branch unforced", fn () => true)
  end

val validation_goal = ([p, q], ``p /\ q``)
val validation_tac =
  DETERM
    (NTHEN (LIFT CONJ_TAC, LIFT (Tactical.FIRST_ASSUM ACCEPT_TAC)))

val _ =
  test
    ("NTHEN composed validations satisfy Tactical.VALID",
     fn () =>
       let
         val (gs, _) = Tactical.VALID validation_tac validation_goal
       in
         List.null gs
       end)

val repeat_goal : Abbrev.goal = ([], ``p ==> p``)

val _ =
  test
    ("NREPEAT keeps only the first result at every iteration",
     fn () =>
       let
         val (gs, _) =
           Tactical.VALID (DETERM (NREPEAT (LIFT DISCH_TAC))) repeat_goal
       in
         case gs of
             [([asm], tm)] => Term.aconv asm p andalso Term.aconv tm p
           | _ => false
       end)

fun tmset ts = HOLset.fromList Term.compare ts

fun mem x xs = List.exists (fn y => x = y) xs

fun rigid_frees pat patvars =
  tmset (List.filter (fn v => not (HOLset.member (patvars, v)))
                     (free_vars pat))

fun really_matches pat patvars query =
  can (Term.raw_match [] (rigid_frees pat patvars) pat query) ([], [])

(* Either directional match is a brute-force witness to unifiability. *)
fun really_unifies pat patvars query qvars =
  really_matches pat patvars query orelse really_matches query qvars pat

val x = ``x : bool``
val y = ``y : bool``
val f = ``f : bool -> bool``
val g = ``g : bool -> bool``
val small_terms =
  [p, q, r, ``~p``, ``p /\ q``, ``p ==> q``,
   ``(f : bool -> bool) p``,
   ``\z : bool. z``, ``\z : bool. p /\ z``]

val small_patterns =
  [(x, tmset [x]),
   (``x /\ y``, tmset [x, y]),
   (``x ==> y``, tmset [x, y]),
   (``~x``, tmset [x]),
   (``(f : bool -> bool) x``, tmset [x]),
   (``\z : bool. x /\ z``, tmset [x]),
   (``\z : bool. z``, tmset [])]

fun random_pairs n =
  let
    val plen = length small_patterns
    val qlen = length small_terms
    fun loop 0 _ acc = acc
      | loop k seed acc =
          let
            val seed' = (seed * 37 + 17) mod 997
            val pat = List.nth (small_patterns, seed' mod plen)
            val query = List.nth (small_terms, (seed' div plen) mod qlen)
          in
            loop (k - 1) seed' ((pat, query) :: acc)
          end
  in
    loop n 19 []
  end

val net_entries =
  ListPair.zip (List.tabulate (length small_patterns, fn i => i),
                small_patterns)

val small_net =
  List.foldl
    (fn ((i, (pat, patvars)), net) =>
        insert ({pat = pat, patvars = patvars}, i) net)
    empty net_entries

val _ =
  test
    ("clasetNet match retrieves every brute-force random match",
     fn () =>
       List.all
         (fn (((pat, patvars), query)) =>
            List.all
              (fn (i, (stored, storedvars)) =>
                 not (really_matches stored storedvars query) orelse
                 mem i (match query small_net))
              net_entries)
         (random_pairs 80))

val query_var_sets = [tmset [], tmset [p], tmset [q], tmset [p, q]]

val _ =
  test
    ("clasetNet unify retrieves every brute-force random unifier",
     fn () =>
       List.all
         (fn (((_, _), query)) =>
            List.all
              (fn qvars =>
                 List.all
                   (fn (i, (stored, storedvars)) =>
                      not (really_unifies stored storedvars query qvars) orelse
                      mem i (unify {q = query, qvars = qvars} small_net))
                   net_entries)
              query_var_sets)
         (random_pairs 80))

fun one pat patvars = insert ({pat = pat, patvars = patvars}, 1) empty

val _ =
  test
    ("clasetNet follows Lam bodies and Cmb rators",
     fn () =>
     mem 1
       (match ``\a : bool. p /\ a``
          (one ``\z : bool. x /\ z`` (tmset [x])))
     andalso mem 1
       (match ``(f : bool -> bool) p``
          (one ``(f : bool -> bool) x`` (tmset [x])))
     andalso not
       (mem 1
          (match ``(g : bool -> bool) p``
             (one ``(f : bool -> bool) x`` (tmset [x])))))

val _ =
  test
    ("clasetNet unification harvests Lam and Cmb subnets",
     fn () =>
       mem 1
         (unify {q = x, qvars = tmset [x]}
            (one ``\z : bool. z`` (tmset [])))
       andalso mem 1
         (unify {q = x, qvars = tmset [x]}
            (one ``(f : bool -> bool) p`` (tmset [])))
       andalso mem 1
         (unify {q = ``\z : bool. z``, qvars = tmset []}
            (one x (tmset [x]))))

val _ =
  test
    ("clasetNet keeps non-pattern free variables rigid",
     fn () =>
       mem 1 (match x (one x (tmset [])))
       andalso not (mem 1 (match p (one x (tmset [])))))

val _ =
  test
    ("clasetNet vfilter deletes values from every subnet",
     fn () =>
       let
         val net =
           insert ({pat = p, patvars = tmset []}, 1)
             (insert ({pat = q, patvars = tmset []}, 2) empty)
         val net' = vfilter (fn i => i <> 1) net
       in
         List.null (match p net') andalso listItems net' = [2]
       end)

(* clasetRules: normalize only the implication spine. *)
fun aconv_thm th1 th2 = Term.aconv (concl th1) (concl th2)

fun thm_prem_conj () =
  let val pq = ``p /\ q``
  in DISCH pq (DISCH r (CONJUNCT1 (ASSUME pq))) end

fun thm_nested_conj () =
  let val pqr = ``(p /\ q) /\ r``
  in DISCH pqr (CONJUNCT1 (CONJUNCT1 (ASSUME pqr))) end

val _ =
  test
    ("canonical_rule curries top-level conjunction premises",
     fn () =>
       Term.aconv (concl (canonical_rule (thm_prem_conj ())))
         ``p ==> q ==> r ==> p``)

val _ =
  test
    ("canonical_rule recursively curries nested conjunctions",
     fn () =>
       Term.aconv (concl (canonical_rule (thm_nested_conj ())))
         ``p ==> q ==> r ==> p``)

val _ =
  test
    ("canonical_rule leaves premise-internal binders intact",
     fn () =>
       let
         val P = ``P : bool -> bool``
         val z = ``z : bool``
         val internal = ``!z : bool. P z ==> q``
         val th = DISCH internal (ASSUME internal)
       in
         Term.aconv (concl (canonical_rule th))
           ``(!z : bool. P z ==> q) ==> (!z : bool. P z ==> q)``
       end)

fun shadowed_outer_rule () =
  let
    val x = ``x : bool``
    val pq = ``p /\ q``
    val quantified = GEN x (DISCH pq (CONJUNCT1 (ASSUME pq)))
  in
    Drule.ADD_ASSUM x quantified
  end

fun shadowed_canonical_rule () =
  let
    val x = ``x : bool``
    val quantified = GEN x (DISCH p (ASSUME p))
  in
    Drule.ADD_ASSUM x quantified
  end

fun shadowed_canonical_elim () =
  let
    val x = ``x : bool``
    val major = ``p /\ q``
    val quantified = GEN x (DISCH major (DISCH r (ASSUME r)))
  in
    Drule.ADD_ASSUM x quantified
  end

val _ =
  test
    ("rule preprocessing freshens outer binders away from hypotheses",
     fn () =>
       let
         val th = shadowed_outer_rule ()
         val th' = canonical_rule th
         val spec = {kind = clasetRules.Intro, safe = true, prio = NONE}
       in
         Term.aconv (concl th') ``!x : bool. p ==> q ==> p`` andalso
         List.exists (Term.aconv ``x : bool``) (hyp th') andalso
         can (ext_info spec) th andalso
         can (ext_info spec) (shadowed_canonical_rule ())
       end)

val _ =
  test
    ("repeated canonicalization avoids intro and elim kernel rebuilding",
     fn () =>
       let
         fun unchanged canonicalize th =
           let
             val once = canonicalize th
             val twice = canonicalize once
             fun binder_names theorem =
               map (fst o dest_var) (fst (strip_forall (concl theorem)))
           in
             binder_names once = binder_names th andalso
             binder_names twice = binder_names once andalso
             Term.aconv (concl twice) (concl th) andalso
             same_terms (hyp twice) (hyp th)
           end
       in
         unchanged canonical_rule (shadowed_canonical_rule ()) andalso
         unchanged (canonical_rule_of clasetRules.Elim)
           (shadowed_canonical_elim ())
       end)

val _ =
  test
    ("canonical_form records outer quantified variables as patvars",
     fn () =>
       let
         val z = ``z : bool``
         val P = ``P : bool -> bool``
         val Pz = mk_comb (P, z)
         val th = GEN z (DISCH Pz (ASSUME Pz))
         val form = canonical_form th
       in
         HOLset.member (#patvars form, z) andalso
         Term.aconv (#concl form) Pz
       end)

val _ =
  test
    ("elimination canonicalization preserves a conjunctive major premise",
     fn () =>
       let
         val spec =
           {kind = clasetRules.Elim, safe = true, prio = NONE}
         val theorem = clasetSeedTheory.CONJ_ELIM_THM
         val processed = #1 (#rl (ext_info spec theorem))
       in
         Term.aconv
           (rule_index clasetRules.Elim processed) ``p /\ q`` andalso
         subgoals_of (true, processed) = 1
       end)

val _ =
  test
    ("elimination canonicalization still curries conjunctive side premises",
     fn () =>
       let
         val major = ``p /\ q``
         val side = ``q /\ r``
         val theorem =
           DISCH major
             (DISCH side (CONJUNCT1 (ASSUME major)))
       in
         Term.aconv
           (concl (canonical_rule_of clasetRules.Elim theorem))
           ``p /\ q ==> q ==> r ==> p``
       end)

val _ =
  test
    ("rule_index rejects premise-free elimination rules",
     fn () =>
       not (can (rule_index clasetRules.Elim) boolTheory.TRUTH))

fun info_of th = {rl = (th, NONE), dup_rl = (th, NONE)}
val safe_intro = {kind = clasetRules.Intro, safe = true, prio = NONE}
val safe_elim = {kind = clasetRules.Elim, safe = true, prio = NONE}

fun decl name spec th =
  make_decl {name = name, spec = spec, weight = 1,
             info = info_of th, orig = th}

fun add d ds =
  case extend_decl d ds of
      (SOME _, ds') => ds'
    | (NONE, _) => raise Fail "test declaration unexpectedly rejected"

val decl_a = decl "a" safe_intro (DISCH p (ASSUME p))
val decl_b = decl "b" safe_intro (DISCH q (ASSUME q))
val decl_c = decl "c" safe_elim (DISCH r (ASSUME r))
val decl_d = decl "d" safe_intro (DISCH ``p /\ q`` (ASSUME ``p /\ q``))

val _ =
  test
    ("decls use decreasing indices and remove by declaration name",
     fn () =>
       let
         val ds = add decl_b (add decl_a empty_decls)
         val names = map #name (dest_decls ds)
         val (removed, ds') = remove_decl "a" ds
       in
         names = ["b", "a"] andalso map #name removed = ["a"] andalso
         map #name (dest_decls ds') = ["b"]
       end)

val _ =
  test
    ("merge_decls replays Bires merge order by kind-class and reverse index",
     fn () =>
       let
         val left = add decl_a empty_decls
         val right = add decl_d (add decl_c (add decl_b empty_decls))
         val (fresh, merged) = merge_decls (left, right)
         val fresh_names = map #name fresh
         val merged_names = map #name (dest_decls merged)
       in
         fresh_names = ["b", "d", "c"] andalso
         merged_names = ["d", "b", "a", "c"]
       end)

val _ =
  test
    ("candidate_order prefers fewer subgoals, then recent declarations",
     fn () =>
       let
         val th = thm_prem_conj ()
         val ordered = candidate_order
           [({weight = 2, index = ~1}, (false, th)),
            ({weight = 1, index = ~1}, (false, th)),
            ({weight = 1, index = ~3}, (false, th))]
       in
         map (fn ({index, ...}, _) => index) ordered = [~3, ~1, ~1]
       end)

fun same_spec ({kind = kind1, safe = safe1, prio = prio1} : rulespec)
              ({kind = kind2, safe = safe2, prio = prio2} : rulespec) =
  kind1 = kind2 andalso safe1 = safe2 andalso prio1 = prio2

val _ =
  test
    ("claset delta codec round-trips version-one ADD and RM deltas",
     fn () =>
       let
         val name = {Thy = "bool", Name = "AND_IMP_INTRO"}
         val spec = {kind = clasetRules.Dest, safe = false, prio = SOME 75}
       in
         (case decode_delta (encode_delta (ADD {name = name, spec = spec})) of
             SOME (ADD {name = name', spec = spec'}) =>
               name = name' andalso same_spec spec spec'
           | _ => false)
         andalso decode_delta (encode_delta (RM "gone")) = SOME (RM "gone")
       end)

val _ =
  test
    ("claset ADD deltas load their theorem by name and check liveness",
     fn () =>
       let
         val name = {Thy = "bool", Name = "AND_IMP_INTRO"}
         val spec = {kind = clasetRules.Intro, safe = true, prio = NONE}
       in
         (case load_delta (ADD {name = name, spec = spec}) of
             SOME (name', spec', th) =>
               name = name' andalso same_spec spec spec' andalso
               aconv_thm th boolTheory.AND_IMP_INTRO
           | NONE => false)
         andalso uptodate_delta (ADD {name = name, spec = spec})
       end)


(* clasetRules: primitive preprocessing derived rules. *)
fun same_thm th1 th2 = Term.aconv (concl th1) (concl th2)

fun specs [] th = th
  | specs (tm :: tms) th = specs tms (SPEC tm th)

fun contradiction not_tm tm_th = MP (NOT_ELIM not_tm) tm_th

fun injD_analogue () =
  let
    val inj = ``\f : bool -> bool. !x : bool y : bool.
                 f x = f y ==> x = y``
    val f = ``f : bool -> bool``
    val x = ``x : bool``
    val y = ``y : bool``
    val injf = mk_comb (inj, f)
    val injf_th = EQ_MP (BETA_CONV injf) (ASSUME injf)
    val inst = specs [x, y] injf_th
    val (fxy, xeqy) = dest_imp (concl inst)
    val xeqy_th = MP inst (ASSUME fxy)
  in
    GENL [f, x, y] (DISCH injf (DISCH fxy xeqy_th))
  end

fun repaired_inj_elim () =
  let
    val f = ``f : bool -> bool``
    val x = ``x : bool``
    val y = ``y : bool``
    val r = ``r : bool``
    val source = specs [f, x, y] (injD_analogue ())
    val (injf, tail) = dest_imp (concl source)
    val (fxy, xeqy) = dest_imp tail
    val notr = mk_neg r
    val hfxy = ASSUME (mk_imp (notr, fxy))
    val hkr = ASSUME (mk_imp (xeqy, r))
    val negative =
      MP hkr
        (MP (MP source (ASSUME injf)) (MP hfxy (ASSUME notr)))
    val body =
      DISJ_CASES (SPEC r boolTheory.EXCLUDED_MIDDLE) (ASSUME r) negative
  in
    GENL [f, x, y, r]
      (DISCH injf (DISCH (mk_imp (notr, fxy))
        (DISCH (mk_imp (xeqy, r)) body)))
  end

val _ = test ("injD analogue is locally proved", fn () =>
  (injD_analogue (); true))

val _ =
  test
    ("dest declarations make and classically repair the injD analogue",
     fn () =>
       let
         val spec = {kind = clasetRules.Dest, safe = true, prio = NONE}
         val expected = repaired_inj_elim ()
         val info = ext_info spec (injD_analogue ())
       in
         same_thm (#1 (#rl info)) expected
       end)

fun hand_swap_and () =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val r = ``r : bool``
    val pq = mk_conj (p, q)
    val notpq = mk_neg pq
    val notr = mk_neg r
    val hp = ASSUME (mk_imp (notr, p))
    val hq = ASSUME (mk_imp (notr, q))
    val body =
      CCONTR r (contradiction (ASSUME notpq)
        (CONJ (MP hp (ASSUME notr)) (MP hq (ASSUME notr))))
  in
    GENL [p, q, r]
      (DISCH notpq (DISCH (mk_imp (notr, p))
        (DISCH (mk_imp (notr, q)) body)))
  end

fun hand_dup_and () =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val pq = mk_conj (p, q)
    val notpq = mk_neg pq
    val hp = ASSUME (mk_imp (notpq, p))
    val hq = ASSUME (mk_imp (notpq, q))
    val negative =
      CONJ (MP hp (ASSUME notpq)) (MP hq (ASSUME notpq))
    val body =
      DISJ_CASES (SPEC pq boolTheory.EXCLUDED_MIDDLE) (ASSUME pq) negative
  in
    GENL [p, q]
      (DISCH (mk_imp (notpq, p)) (DISCH (mk_imp (notpq, q)) body))
  end

fun cdisj_intro () =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val notq = mk_neg q
    val h = ASSUME (mk_imp (notq, p))
    val body =
      DISJ_CASES (SPEC q boolTheory.EXCLUDED_MIDDLE)
        (DISJ2 p (ASSUME q)) (DISJ1 (MP h (ASSUME notq)) q)
  in
    GENL [p, q] (DISCH (mk_imp (notq, p)) body)
  end

fun cdisj_from h =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val notq = mk_neg q
  in
    DISJ_CASES (SPEC q boolTheory.EXCLUDED_MIDDLE)
      (DISJ2 p (ASSUME q)) (DISJ1 (MP h (ASSUME notq)) q)
  end

fun hand_swap_cdisj () =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val r = ``r : bool``
    val c = mk_disj (p, q)
    val notc = mk_neg c
    val notr = mk_neg r
    val h = ASSUME (mk_imp (notr, mk_imp (mk_neg q, p)))
    val body =
      CCONTR r (contradiction (ASSUME notc)
        (cdisj_from (MP h (ASSUME notr))))
  in
    GENL [p, q, r]
      (DISCH notc (DISCH (mk_imp (notr, mk_imp (mk_neg q, p))) body))
  end

fun hand_dup_cdisj () =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val c = mk_disj (p, q)
    val notc = mk_neg c
    val h = ASSUME (mk_imp (notc, mk_imp (mk_neg q, p)))
    val negative = cdisj_from (MP h (ASSUME notc))
    val body =
      DISJ_CASES (SPEC c boolTheory.EXCLUDED_MIDDLE) (ASSUME c) negative
  in
    GENL [p, q] (DISCH (mk_imp (notc, mk_imp (mk_neg q, p))) body)
  end

fun exists_intro () =
  let
    val P = ``P : bool -> bool``
    val x = ``x : bool``
    val px = mk_comb (P, x)
    val ex = mk_exists (x, px)
  in
    GENL [P, x] (DISCH px (EXISTS (ex, x) (ASSUME px)))
  end

fun hand_swap_exists () =
  let
    val P = ``P : bool -> bool``
    val x = ``x : bool``
    val r = ``r : bool``
    val px = mk_comb (P, x)
    val ex = mk_exists (x, px)
    val notex = mk_neg ex
    val notr = mk_neg r
    val hp = ASSUME (mk_imp (notr, px))
    val body =
      CCONTR r (contradiction (ASSUME notex)
        (EXISTS (ex, x) (MP hp (ASSUME notr))))
  in
    GENL [P, x, r]
      (DISCH notex (DISCH (mk_imp (notr, px)) body))
  end

fun hand_dup_exists () =
  let
    val P = ``P : bool -> bool``
    val x = ``x : bool``
    val px = mk_comb (P, x)
    val ex = mk_exists (x, px)
    val notex = mk_neg ex
    val hp = ASSUME (mk_imp (notex, px))
    val negative = EXISTS (ex, x) (MP hp (ASSUME notex))
    val body =
      DISJ_CASES (SPEC ex boolTheory.EXCLUDED_MIDDLE) (ASSUME ex) negative
  in
    GENL [P, x] (DISCH (mk_imp (notex, px)) body)
  end

val _ =
  test
    ("swap and duplication rules agree with hand proofs for seed intros",
     fn () =>
       let
         val and_intro = boolTheory.AND_INTRO_THM
         val disj_intro = cdisj_intro ()
         val ex_intro = exists_intro ()
       in
         Option.isSome (SWAP_INTRO_RULE and_intro) andalso
         same_thm (Option.valOf (SWAP_INTRO_RULE and_intro))
           (hand_swap_and ()) andalso
         same_thm (DUP_INTRO_RULE and_intro) (hand_dup_and ()) andalso
         Option.isSome (SWAP_INTRO_RULE disj_intro) andalso
         same_thm (Option.valOf (SWAP_INTRO_RULE disj_intro))
           (hand_swap_cdisj ()) andalso
         same_thm (DUP_INTRO_RULE disj_intro) (hand_dup_cdisj ()) andalso
         Option.isSome (SWAP_INTRO_RULE ex_intro) andalso
         same_thm (Option.valOf (SWAP_INTRO_RULE ex_intro))
           (hand_swap_exists ()) andalso
         same_thm (DUP_INTRO_RULE ex_intro) (hand_dup_exists ())
       end)

fun no_swap NONE = true
  | no_swap _ = false

val _ =
  test
    ("swap declines negation-headed conclusions",
     fn () =>
       let
         val negp = mk_neg p
         val neg_intro = GEN p (DISCH negp (ASSUME negp))
       in
         no_swap (SWAP_INTRO_RULE neg_intro)
       end)

val _ =
  test
    ("swap retains the classical form of negation introduction",
     fn () =>
       case SWAP_INTRO_RULE boolTheory.IMP_F of
           NONE => false
         | SOME theorem =>
             case strip_forall (concl theorem) of
                 ([t, r], body) =>
                   (case strip_imp_only body of
                        ([double_neg_t, lifted], result) =>
                          aconv double_neg_t (mk_neg (mk_neg t)) andalso
                          aconv lifted
                            (mk_imp
                              (mk_neg r, mk_imp (t, boolSyntax.F))) andalso
                          aconv result r
                      | _ => false)
               | _ => false)

val _ =
  test
    ("swap declines variable-headed conclusions",
     fn () =>
       let val var_intro = GEN p (DISCH p (ASSUME p))
       in no_swap (SWAP_INTRO_RULE var_intro) end)

fun simple_elim () =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val hp = ASSUME p
    val hpq = ASSUME (mk_imp (p, q))
  in
    GENL [p, q] (DISCH p (DISCH (mk_imp (p, q)) (MP hpq hp)))
  end

fun hand_dup_elim () =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val hp = ASSUME p
    val h = ASSUME (mk_imp (p, mk_imp (p, q)))
  in
    GENL [p, q]
      (DISCH p (DISCH (mk_imp (p, mk_imp (p, q))) (MP (MP h hp) hp)))
  end

val _ =
  test
    ("DUP_ELIM_RULE retains the major premise in every side premise",
     fn () => same_thm (DUP_ELIM_RULE (simple_elim ())) (hand_dup_elim ()))

fun hand_rev_conj_elim () =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val r = ``r : bool``
    val major = mk_conj (p, q)
    val hmajor = ASSUME major
    val minor =
      mk_imp (p, mk_imp (q, mk_imp (major, r)))
    val hminor = ASSUME minor
    val body =
      MP (MP (MP hminor (CONJUNCT1 hmajor)) (CONJUNCT2 hmajor))
        hmajor
  in
    GENL [p, q, r] (DISCH major (DISCH minor body))
  end

fun hand_rev_disj_elim () =
  let
    val p = ``p : bool``
    val q = ``q : bool``
    val r = ``r : bool``
    val major = mk_disj (p, q)
    val hmajor = ASSUME major
    val left = mk_imp (p, mk_imp (major, r))
    val right = mk_imp (q, mk_imp (major, r))
    val hleft = ASSUME left
    val hright = ASSUME right
    val body =
      DISJ_CASES hmajor
        (MP (MP hleft (ASSUME p)) hmajor)
        (MP (MP hright (ASSUME q)) hmajor)
  in
    GENL [r, p, q]
      (DISCH major (DISCH left (DISCH right body)))
  end

fun hand_rev_exists_elim () =
  let
    val P = ``P : bool -> bool``
    val x = ``x : bool``
    val q = ``q : bool``
    val px = mk_comb (P, x)
    val major = mk_exists (x, px)
    val hmajor = ASSUME major
    val minor =
      mk_forall (x, mk_imp (px, mk_imp (major, q)))
    val hminor = ASSUME minor
    val branch = MP (MP (SPEC x hminor) (ASSUME px)) hmajor
    val body = CHOOSE (x, hmajor) branch
  in
    GEN q (DISCH major (DISCH minor body))
  end

val _ =
  test
    ("REV_DUP_ELIM_RULE has the exact conjunction-elim output",
     fn () =>
       same_thm (REV_DUP_ELIM_RULE clasetSeedTheory.CONJ_ELIM_THM)
         (hand_rev_conj_elim ()))

val _ =
  test
    ("REV_DUP_ELIM_RULE has the exact disjunction-elim output",
     fn () =>
       same_thm (REV_DUP_ELIM_RULE boolTheory.OR_ELIM_THM)
         (hand_rev_disj_elim ()))

val _ =
  test
    ("REV_DUP_ELIM_RULE has the exact exists-elim output",
     fn () =>
       let
         val P = ``P : bool -> bool``
         val exists_elim =
           Drule.ISPEC P clasetSeedTheory.EXISTS_ELIM_THM
       in
         same_thm (REV_DUP_ELIM_RULE exists_elim)
           (hand_rev_exists_elim ())
       end)

fun shadowed_minor_elim () =
  let
    val P = ``P : bool -> bool``
    val x = ``x : bool``
    val r = ``r : bool``
    val major = mk_comb (P, x)
    val minor = mk_forall (x, mk_imp (mk_comb (P, x), r))
    val body = MP (SPEC x (ASSUME minor)) (ASSUME major)
  in
    GENL [P, x, r] (DISCH major (DISCH minor body))
  end

val _ =
  test
    ("reverse elim duplication avoids capturing the major premise",
     fn () =>
       let
         val theorem = REV_DUP_ELIM_RULE (shadowed_minor_elim ())
       in
         case rule_premises_of clasetRules.Elim theorem of
             [major, minor] =>
               let
                 val (bound, body) = dest_forall minor
                 val (added, _) = strip_imp_only body
               in
                 not (free_in bound major) andalso
                 length added = 2 andalso
                 Term.aconv (List.last added) major
               end
           | _ => false
       end)

val _ =
  test
    ("reverse and ordinary elim duplication order hypotheses differently",
     fn () =>
       let
         val p = ``p : bool``
         val q = ``q : bool``
         val r = ``r : bool``
         val major = mk_conj (p, q)
         val rev_minor =
           mk_imp (p, mk_imp (q, mk_imp (major, r)))
         val dup_minor =
           mk_imp (major, mk_imp (p, mk_imp (q, r)))
         val rev_prems =
           rule_premises_of clasetRules.Elim
             (REV_DUP_ELIM_RULE clasetSeedTheory.CONJ_ELIM_THM)
         val dup_prems =
           rule_premises_of clasetRules.Elim
             (DUP_ELIM_RULE clasetSeedTheory.CONJ_ELIM_THM)
       in
         same_terms rev_prems [major, rev_minor] andalso
         same_terms dup_prems [major, dup_minor] andalso
         not (same_terms rev_prems dup_prems)
       end)

fun hol_err_msg f =
  (f (); NONE) handle HOL_ERR e => SOME (Feedback.message_of e)

val _ =
  test
    ("reverse elim duplication handles no-op and failure edges",
     fn () =>
       let
         val false_elim = canonical_rule_of clasetRules.Elim
           boolTheory.FALSITY
         val once = REV_DUP_ELIM_RULE boolTheory.FALSITY
       in
         same_thm once false_elim andalso
         same_thm (REV_DUP_ELIM_RULE once) once andalso
         hol_err_msg
           (fn () => (REV_DUP_ELIM_RULE boolTheory.TRUTH; ())) =
           SOME "Ill-formed elimination rule"
       end)

val _ =
  test
    ("ext_info rejects premise-free eliminations and classifies safe rules",
     fn () =>
       let
         val safe_elim = {kind = clasetRules.Elim, safe = true, prio = NONE}
         val safe0 = ext_info safe_elim boolTheory.FALSITY
         val safep = ext_info safe_elim boolTheory.OR_ELIM_THM
       in
         same_thm (CLASSICAL_RULE boolTheory.FALSITY)
           (canonical_rule boolTheory.FALSITY) andalso
         hol_err_msg (fn () => (ext_info safe_elim boolTheory.TRUTH; ())) =
           SOME "Ill-formed elimination rule" andalso
         safe_class_of safe_elim safe0 = SOME Safe0 andalso
         safe_class_of safe_elim safep = SOME SafeP
       end)

val _ =
  test
    ("duplicate and cross-kind declarations warn as appropriate",
     fn () =>
       let
         val th = DISCH p (ASSUME p)
         val first = decl "duplicate-one" safe_intro th
         val second = decl "duplicate-two" safe_intro th
         val other = decl "cross-kind" safe_elim th
         val (one, ds) = extend_decl first empty_decls
         val (two, ds') = extend_decl second ds
         val (three, ds'') = extend_decl other ds'
       in
         Option.isSome one andalso not (Option.isSome two) andalso
         Option.isSome three andalso length (dest_decls ds'') = 2
       end)


(* clasetLib: value operations and netpair lookup. *)
fun has_thm th = List.exists (fn (_, (_, th')) => same_thm th th')

val _ =
  test
    ("rules_of preserves a conjunctive elimination major premise",
     fn () =>
       let
         val cs =
           add_selims
             [("conjunction-elim", clasetSeedTheory.CONJ_ELIM_THM)]
             empty_cs
       in
         case rules_of cs of
             [({kind = clasetRules.Elim, ...}, (_, theorem))] =>
               Term.aconv
                 (rule_index clasetRules.Elim theorem) ``p /\ q``
           | _ => false
       end)

val _ =
  test
    ("clasetLib routes safe zero- and positive-subgoal rules",
     fn () =>
       let
         val cs =
           add_selims [("falseE", boolTheory.FALSITY)]
             (add_sintros [("truthI", boolTheory.TRUTH)]
                (add_selims [("orE", boolTheory.OR_ELIM_THM)]
                   (add_sintros [("andI", boolTheory.AND_INTRO_THM)]
                      empty_cs)))
         val safe0_intro =
           match_intro_candidates (safe0_part cs) ``T``
         val safe0_elim =
           match_elim_candidates (safe0_part cs) ``F``
         val safep_intro =
           match_intro_candidates (safep_part cs) ``p /\ q``
         val safep_elim =
           match_elim_candidates (safep_part cs) ``p \/ q``
       in
         has_thm boolTheory.TRUTH safe0_intro andalso
         has_thm boolTheory.FALSITY safe0_elim andalso
         has_thm boolTheory.AND_INTRO_THM safep_intro andalso
         has_thm boolTheory.OR_ELIM_THM safep_elim
       end)

fun refl_intro vars tm = GENL vars (DISCH tm (ASSUME tm))

fun candidate_indices candidates =
  map (fn (({index, ...} : tag), _) => index) candidates

fun candidate_weights candidates =
  map (fn (({weight, ...} : tag), _) => weight) candidates

val _ =
  test
    ("clasetLib orders six matching rules by subgoals then recency",
     fn () =>
       let
         val a = ``p /\ p``
         val b = ``p /\ q``
         val c = ``q /\ p``
         val d = ``x /\ x``
         val e = ``x /\ y``
         val f = ``y /\ x``
         val rules =
           [("one", refl_intro [] a),
            ("two", refl_intro [q] b),
            ("three", refl_intro [q] c),
            ("four", refl_intro [x] d),
            ("five", refl_intro [x, y] e),
            ("six", refl_intro [x, y] f)]
         val cs = add_intros rules empty_cs
         val candidates =
           match_intro_candidates (unsafe_part cs) ``p /\ p``
       in
         candidate_weights candidates = [2, 2, 2, 2, 2, 2] andalso
         candidate_indices candidates = [~11, ~9, ~7, ~5, ~3, ~1]
       end)

val _ =
  test
    ("clasetLib routes swapped intros to elimination lookup",
     fn () =>
       let
         val cs = add_intros [("andI", boolTheory.AND_INTRO_THM)] empty_cs
         val swapped = Option.valOf (SWAP_INTRO_RULE boolTheory.AND_INTRO_THM)
         val query = ``~(p /\ q)``
         val intros = match_intro_candidates (unsafe_part cs) query
         val elims = match_elim_candidates (unsafe_part cs) query
       in
         List.null intros andalso
         has_thm swapped elims andalso
         List.exists (fn (tag, (is_elim, th)) =>
           is_elim andalso #index tag = ~2 andalso same_thm th swapped) elims
       end)

fun indexed_term (is_elim, th) =
  rule_index (if is_elim then clasetRules.Elim else clasetRules.Intro) th

fun exactly_matches (is_elim, th) query =
  let val {patvars, ...} = canonical_form th
  in really_matches (indexed_term (is_elim, th)) patvars query end

fun same_candidates (cs1 : (tag * brl) list) (cs2 : (tag * brl) list) =
  ListPair.allEq
    (fn ((tag1, brl1), (tag2, brl2)) =>
       #weight tag1 = #weight tag2 andalso #index tag1 = #index tag2 andalso
       #1 brl1 = #1 brl2 andalso same_thm (#2 brl1) (#2 brl2))
    (cs1, cs2)

val _ =
  test
    ("measured candidate FVL preserves a free variable beside its shadow",
     fn () =>
       let
         val rigid =
           ``(P : bool -> (bool -> bool) -> bool) T (\x : bool. x)``
         val rule = ASSUME rigid
         val cs = add_intros [("rigid", rule)] empty_cs
         val query =
           ``(P : bool -> (bool -> bool) -> bool) (x : bool)
               (\x : bool. x)``
         val ordinary = unify_intro_candidates (unsafe_part cs) query
         val polls = ref 0
         val measured =
           unify_intro_candidates_measured
             (fn () => polls := !polls + 1) (unsafe_part cs) query
       in
         !polls > 0 andalso has_thm rule ordinary andalso
         same_candidates ordinary measured
       end)

fun rule_entries index kind (th, swapped) =
  let
    fun entry is_elim index th =
      ({weight = subgoals_of (is_elim, th), index = index},
       (is_elim, th))
  in
    entry (kind <> clasetRules.Intro) (2 * index + 1) th ::
    (case swapped of
         NONE => []
       | SOME th' => [entry true (2 * index) th'])
  end

fun brute_unsafe_entries declarations =
  let
    fun add ((kind, th), (index, entries)) =
      let
        val spec = {kind = kind, safe = false, prio = NONE}
        val info = ext_info spec th
      in
        (index - 1, rule_entries index kind (#rl info) @ entries)
      end
  in
    candidate_order (#2 (List.foldl add (~1, []) declarations))
  end

fun exactly_unifies (is_elim, th) query =
  let
    val {patvars, ...} = canonical_form th
  in
    really_unifies (indexed_term (is_elim, th)) patvars query
      (tmset (free_vars query))
  end

val _ =
  test
    ("clasetLib match introduction candidates agree with brute filtering",
     fn () =>
       let
         val declarations =
           [(clasetRules.Elim, boolTheory.OR_ELIM_THM),
            (clasetRules.Intro, boolTheory.AND_INTRO_THM)]
         val cs =
           add_intros [("andI", boolTheory.AND_INTRO_THM)]
             (add_elims [("orE", boolTheory.OR_ELIM_THM)] empty_cs)
         val entries = brute_unsafe_entries declarations
         val iq = ``p /\ q``
         val eq = ``p \/ q``
         fun matching is_elim query = candidate_order
           (List.filter
             (fn (_, brl) => #1 brl = is_elim andalso
                             exactly_matches brl query) entries)
       in
         same_candidates
           (match_intro_candidates (unsafe_part cs) iq) (matching false iq)
       end)

val _ =
  test
    ("clasetLib match elimination candidates agree with brute filtering",
     fn () =>
       let
         val cs =
           add_intros [("andI", boolTheory.AND_INTRO_THM)]
             (add_elims [("orE", boolTheory.OR_ELIM_THM)] empty_cs)
         val entries = brute_unsafe_entries
           [(clasetRules.Elim, boolTheory.OR_ELIM_THM),
            (clasetRules.Intro, boolTheory.AND_INTRO_THM)]
         val query = ``p \/ q``
         val expected = candidate_order
           (List.filter
             (fn (_, brl) => #1 brl andalso exactly_matches brl query)
             entries)
       in
         same_candidates (match_elim_candidates (unsafe_part cs) query)
           expected
       end)

val _ =
  test
    ("clasetLib unify introduction candidates agree with brute filtering",
     fn () =>
       let
         val cs =
           add_intros [("andI", boolTheory.AND_INTRO_THM)]
             (add_elims [("orE", boolTheory.OR_ELIM_THM)] empty_cs)
         val entries = brute_unsafe_entries
           [(clasetRules.Elim, boolTheory.OR_ELIM_THM),
            (clasetRules.Intro, boolTheory.AND_INTRO_THM)]
         val query = ``p /\ q``
       in
         same_candidates (unify_intro_candidates (unsafe_part cs) query)
           (candidate_order
             (List.filter
               (fn (_, brl) => not (#1 brl) andalso
                               exactly_unifies brl query) entries))
       end)

val _ =
  test
    ("clasetLib unify elimination candidates agree with brute filtering",
     fn () =>
       let
         val cs =
           add_intros [("andI", boolTheory.AND_INTRO_THM)]
             (add_elims [("orE", boolTheory.OR_ELIM_THM)] empty_cs)
         val entries = brute_unsafe_entries
           [(clasetRules.Elim, boolTheory.OR_ELIM_THM),
            (clasetRules.Intro, boolTheory.AND_INTRO_THM)]
         val query = ``p \/ q``
       in
         same_candidates (unify_elim_candidates (unsafe_part cs) query)
           (candidate_order
             (List.filter
               (fn (_, brl) => #1 brl andalso exactly_unifies brl query)
               entries))
       end)

fun same_rules xs ys =
  ListPair.allEq
    (fn ((spec1, (name1, th1)), (spec2, (name2, th2))) =>
       same_spec spec1 spec2 andalso name1 = name2 andalso same_thm th1 th2)
    (xs, ys)

val _ =
  test
    ("clasetLib add, remove, and merge preserve canonical rule order",
     fn () =>
       let
         val a = ("a", DISCH p (ASSUME p))
         val b = ("b", DISCH q (ASSUME q))
         val left =
           add_intros [("andI", boolTheory.AND_INTRO_THM)]
             (add_selims [("falseE", boolTheory.FALSITY)] empty_cs)
         val right =
           add_sintros [a, b]
             (add_selims [("orE", boolTheory.OR_ELIM_THM)] empty_cs)
         val merged = merge_cs (left, right)
         val incremented =
           add_sintros [a, b]
             (add_selims [("orE", boolTheory.OR_ELIM_THM)] left)
         val removed = remove_rule "b" merged
       in
         same_rules (rules_of merged) (rules_of incremented) andalso
         map (fn (_, (name, _)) => name) (rules_of removed) =
           ["a", "falseE", "orE", "andI"]
       end)

val _ =
  test
    ("clasetLib removes tagged rules from every netpair",
     fn () =>
       let
         val cs =
           add_elims [("orE", boolTheory.OR_ELIM_THM)]
             (add_intros [("andI", boolTheory.AND_INTRO_THM)]
               (add_selims [("orES", boolTheory.OR_ELIM_THM)]
                 (add_sintros [("andIS", boolTheory.AND_INTRO_THM)]
                   (add_selims [("falseE", boolTheory.FALSITY)]
                     (add_sintros [("truthI", boolTheory.TRUTH)] empty_cs)))))
         val cs' =
           List.foldl (fn (name, acc) => remove_rule name acc) cs
             ["truthI", "falseE", "andIS", "orES", "andI", "orE"]
         val variable = ``z : bool``
         fun has_intro part =
           not (List.null (unify_intro_candidates part variable))
         fun has_elim part =
           not (List.null (unify_elim_candidates part variable))
         fun no_intro part =
           List.null (unify_intro_candidates part variable)
         fun no_elim part =
           List.null (unify_elim_candidates part variable)
       in
         has_intro (safe0_part cs) andalso has_elim (safe0_part cs) andalso
         has_intro (safep_part cs) andalso has_elim (safep_part cs) andalso
         has_intro (unsafe_part cs) andalso has_elim (unsafe_part cs) andalso
         has_intro (dup_part cs) andalso has_elim (dup_part cs) andalso
         no_intro (safe0_part cs') andalso no_elim (safe0_part cs') andalso
         no_intro (safep_part cs') andalso no_elim (safep_part cs') andalso
         no_intro (unsafe_part cs') andalso no_elim (unsafe_part cs') andalso
         no_intro (dup_part cs') andalso no_elim (dup_part cs')
       end)

val _ =
  test
    ("clasetLib wrappers update by name and preserve choice semantics",
     fn () =>
       let
         fun safe_first tac = NORELSE (labelled p, tac)
         fun safe_second tac = NORELSE (labelled q, tac)
         fun unsafe_first tac = NAPPEND (labelled p, tac)
         fun unsafe_second tac = NAPPEND (labelled q, tac)
         val safe_cs =
           add_safe_wrapper ("one", safe_first)
             (add_safe_wrapper ("two", safe_second) empty_cs)
         val unsafe_cs =
           add_unsafe_wrapper ("one", unsafe_first)
             (add_unsafe_wrapper ("two", unsafe_second) empty_cs)
         val safe_cs' = del_safe_wrapper "two"
           (add_safe_wrapper ("one", safe_second) safe_cs)
         val unsafe_cs' = del_unsafe_wrapper "two"
           (add_unsafe_wrapper ("one", unsafe_second) unsafe_cs)
       in
         same_terms
           (labels (app_safe_wrappers safe_cs (labelled r)) label_goal) [q]
         andalso
         same_terms
           (labels (app_unsafe_wrappers unsafe_cs (labelled r)) label_goal)
           [q, p, r]
         andalso
         same_terms
           (labels (app_safe_wrappers safe_cs' (labelled r)) label_goal) [q]
         andalso
         same_terms
           (labels (app_unsafe_wrappers unsafe_cs' (labelled r)) label_goal)
           [q, r]
       end)

val _ =
  test
    ("clasetLib config uses VAR_EQ_TAC and Isabelle term sizes",
     fn () =>
       let
         val {hyp_subst_tac, size_of} = claset_config
         val variable_goal = ([``x : bool = p``], ``x : bool``)
       in
         size_of variable_goal = 4 andalso
         size_of ([], ``(\x : bool. x) p``) = 3 andalso
         (case #1 (hyp_subst_tac variable_goal) of
             [(_, goal)] => Term.aconv goal p
           | _ => false)
       end)


(* clasetLib: persistent state and theorem attributes. *)
fun has_named_rule name cs =
  List.exists (fn (_, (name', _)) => name = name') (rules_of cs)

val state_rule = DISCH p (ASSUME p)
val state_intro_rule = DISCH q (ASSUME q)
val state_export_rule = DISCH r (ASSUME r)
val state_temp_rule = DISCH ``p /\ q`` (ASSUME ``p /\ q``)
val state_elim_rule = DISCH ``p \/ q`` (ASSUME ``p \/ q``)
val state_dest_rule = DISCH ``~p`` (ASSUME ``~p``)
val state_pending_name = "claset_state_pending"
val state_sintro_name = "claset_state_sintro"
val state_intro_name = "claset_state_intro"
val state_export_name = "claset_state_export"
val state_temp_name = "claset_state_temp"
val state_spec = {kind = clasetRules.Intro, safe = true, prio = NONE}

fun persistent_rule_name name =
  KernelSig.name_toString (ThmSetData.toKName name)

val _ =
  test
    ("claset replays temporary updates in order at first demand",
     fn () =>
       let
         val _ = boolLib.save_thm (state_pending_name, state_rule)
         val _ = export_rule state_spec state_pending_name
         val _ = temp_delrule state_pending_name
       in
         not (has_named_rule (persistent_rule_name state_pending_name)
                (the_claset ()))
       end)

val state_attribute_cases =
  [("intro", {kind = clasetRules.Intro, safe = false, prio = NONE},
    state_rule),
   ("sintro", {kind = clasetRules.Intro, safe = true, prio = NONE},
    state_intro_rule),
   ("elim", {kind = clasetRules.Elim, safe = false, prio = NONE},
    state_export_rule),
   ("selim", {kind = clasetRules.Elim, safe = true, prio = NONE},
    state_temp_rule),
   ("dest", {kind = clasetRules.Dest, safe = false, prio = NONE},
    state_elim_rule),
   ("sdest", {kind = clasetRules.Dest, safe = true, prio = NONE},
    state_dest_rule)]

val _ =
  test
    ("claset attributes register and update the global state",
     fn () =>
       let
         fun add_attribute (attr, _, th) =
           let val name = state_sintro_name ^ "_" ^ attr
           in
             boolLib.save_thm (name ^ "[" ^ attr ^ "]", th);
             ()
           end
         fun has_attribute (_, spec, th) =
           List.exists
             (fn (spec', (_, th')) =>
                same_spec spec spec' andalso
                same_thm (canonical_rule_of (#kind spec) th) th')
             (rules_of (the_claset ()))
       in
         List.app add_attribute state_attribute_cases;
         List.all (fn (attr, _, _) => ThmAttribute.is_attribute attr)
           state_attribute_cases andalso
         List.all has_attribute state_attribute_cases
       end)

val _ =
  test
    ("claset local attributes and temporary additions are not persisted",
     fn () =>
       let
         val _ = boolLib.save_thm
           (state_intro_name ^ "[intro,local]", state_intro_rule)
         val _ = temp_add_rule state_spec (state_temp_name, state_temp_rule)
         val cs_before = the_claset ()
         val persisted = Option.valOf (merge_clasets ["min"])
         val _ = temp_delrule state_temp_name
         val cs_after = the_claset ()
       in
         has_named_rule state_intro_name cs_before andalso
         has_named_rule state_temp_name cs_before andalso
         not (has_named_rule state_intro_name persisted) andalso
         not (has_named_rule state_temp_name persisted) andalso
         has_named_rule state_intro_name cs_after andalso
         not (has_named_rule state_temp_name cs_after)
       end)

val _ =
  test
    ("claset persistent API updates state correctly",
     fn () =>
       let
         val _ = boolLib.save_thm (state_export_name, state_export_rule)
         val _ = export_rule state_spec state_export_name
         val exported = the_claset ()
         val merged = merge_clasets ["min"]
         val by_theory = claset_of_theory {thyname = "min"}
         val only_local = add_sintros [("local-only", state_rule)] empty_cs
         val scoped = with_claset only_local
           (fn () => has_named_rule "local-only" (the_claset ())) ()
         val _ = delrule (persistent_rule_name state_export_name)
       in
         has_named_rule (persistent_rule_name state_export_name) exported andalso
         Option.isSome merged andalso Option.isSome by_theory andalso
         scoped andalso
         not (has_named_rule (persistent_rule_name state_export_name)
                (the_claset ()))
       end)

val _ =
  test
    ("claset attributes reject arguments until priorities are implemented",
     fn () =>
       Option.isSome
         (hol_err_msg
           (fn () =>
             ThmAttribute.local_attribute
               {attrname = "intro", name = "bad-priority", args = ["10"],
                thm = state_rule})))


(* clasetLib: TypeBase hook and contribution registry. *)
fun typebase_specl [] th = th
  | typebase_specl (tm :: tms) th = typebase_specl tms (SPEC tm th)

fun typebase_distinct_elim th =
  let
    val (vars, _) = strip_forall (concl th)
    val core = typebase_specl vars th
    val eq = dest_neg (concl core)
    val r = variant (free_varsl (concl core :: hyp core)) (mk_var ("r", bool))
    val false_th = MP (NOT_ELIM core) (ASSUME eq)
  in
    GENL (vars @ [r])
      (DISCH eq (MP (SPEC r boolTheory.FALSITY) false_th))
  end

fun typebase_iff_dest th =
  let
    val (vars, _) = strip_forall (concl th)
  in
    GENL vars (#1 (EQ_IMP_RULE (typebase_specl vars th)))
  end

fun typebase_hook_tyinfo () =
  case List.filter
    (fn tyi => #2 (TypeBasePure.ty_name_of tyi) =
               "claset_hook_before_demand")
    (TypeBase.elts ()) of
      [tyi] => tyi
    | _ => raise Fail "missing TypeBase selftest datatype"

fun has_typebase_rule spec th =
  List.exists
    (fn (spec', (_, th')) =>
       same_spec spec spec' andalso
       same_thm (canonical_rule_of (#kind spec) th) th')
    (rules_of (the_claset ()))

val typebase_selim_spec =
  {kind = clasetRules.Elim, safe = true, prio = NONE}
val typebase_sdest_spec =
  {kind = clasetRules.Dest, safe = true, prio = NONE}

val _ =
  test
    ("claset catches up TypeBase facts before its first demand",
     fn () =>
       let
         val tyi = typebase_hook_tyinfo ()
         val distinct = Option.valOf (TypeBasePure.distinct_of tyi)
         val injective = Option.valOf (TypeBasePure.one_one_of tyi)
         val distinct_rules =
           List.concat
             (map (fn th => [typebase_distinct_elim th,
                             typebase_distinct_elim (Conv.GSYM th)])
                  (Drule.CONJUNCTS distinct))
         val injective_rules =
           map typebase_iff_dest (Drule.CONJUNCTS injective)
       in
         List.all (has_typebase_rule typebase_selim_spec) distinct_rules
           andalso
         List.all (has_typebase_rule typebase_sdest_spec) injective_rules
       end)

val tyinfo_idempotence_p = ``claset_tyinfo_idempotence_p : bool``
val tyinfo_idempotence_rule =
  DISCH tyinfo_idempotence_p
    (CONJ (ASSUME tyinfo_idempotence_p) (ASSUME tyinfo_idempotence_p))
val tyinfo_idempotence_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE}

fun tyinfo_idempotence_contribution _ =
  [(tyinfo_idempotence_spec,
    ("claset-tyinfo-idempotence", tyinfo_idempotence_rule))]

val tyinfo_idempotence_key = "claset-selftest-idempotence"

fun count_typebase_rules th =
  length
    (List.filter
       (fn (_, (_, th')) => same_thm (canonical_rule th) th')
       (rules_of (the_claset ())))

val _ =
  test
    ("claset TypeBase contributions silently deduplicate reprocessing",
     fn () =>
       let
         val _ = register_tyinfo_contribution
           (tyinfo_idempotence_key, tyinfo_idempotence_contribution)
         val _ = register_tyinfo_contribution
           (tyinfo_idempotence_key, tyinfo_idempotence_contribution)
       in
         count_typebase_rules tyinfo_idempotence_rule = 1
       end)

val ambient_seed_spoof_name = seed_export_identity "AMBIENT_ONLY"
val ambient_seed_spoof_rule = REFL ``ClasetHookA``

fun ambient_seed_spoof_contribution _ =
  [(tyinfo_idempotence_spec,
    (ambient_seed_spoof_name, ambient_seed_spoof_rule))]

val _ =
  test
    ("persistent theory clasets exclude ambient same-name rules",
     fn () =>
       let
         val body_exception = ref (NONE : exn option)

         fun restore_original_provider () =
           (register_tyinfo_contribution
              (tyinfo_idempotence_key, tyinfo_idempotence_contribution);
            if has_named_rule ambient_seed_spoof_name (the_claset ()) then
              raise Fail "ambient seed spoof survived provider restoration"
            else
              ())

         fun cleanup () =
           restore_original_provider ()
           handle cleanup_exception =>
             case !body_exception of
                 SOME _ =>
                   (* The body exception takes precedence when both fail.
                      Reporting the cleanup failure is therefore best-effort:
                      even WARNINGs_as_ERRs must not replace the body error. *)
                   (HOL_WARNING "rules selftest" "cleanup"
                      ("Failed to restore the temporary ambient spoof " ^
                       "contributor after the test body raised; preserving " ^
                       "the original body exception. Cleanup exception: " ^
                       General.exnMessage cleanup_exception)
                    handle _ => ())
               | NONE => raise cleanup_exception

         fun check () =
           let
             val _ = register_tyinfo_contribution
               (tyinfo_idempotence_key, ambient_seed_spoof_contribution)
             val persistent =
               Option.valOf
                 (persistent_claset_of_theory {thyname = seed_theory_name})
             val effective =
               Option.valOf (claset_of_theory {thyname = seed_theory_name})
             val persistent_names = map (#1 o #2) (rules_of persistent)
             val effective_names = map (#1 o #2) (rules_of effective)
             val untagged =
               untagged_theorems
                 {theorem_names = [ambient_seed_spoof_name],
                  persistent_rule_names = persistent_names,
                  permitted = []}
             fun named name = List.exists (fn name' => name = name')
           in
             not (named ambient_seed_spoof_name persistent_names) andalso
             named ambient_seed_spoof_name effective_names andalso
             untagged = [ambient_seed_spoof_name]
           end

         fun record_body_exception () =
           check ()
           handle body_exn =>
             (body_exception := SOME body_exn;
              raise body_exn)
       in
         Portable.finally cleanup record_body_exception ()
       end)

val tyinfo_multispec_p = ``claset_tyinfo_multispec_p : bool``
val tyinfo_multispec_rule =
  DISCH tyinfo_multispec_p (ASSUME tyinfo_multispec_p)
val tyinfo_multispec_intro =
  {kind = clasetRules.Intro, safe = true, prio = NONE}
val tyinfo_multispec_elim =
  {kind = clasetRules.Elim, safe = true, prio = NONE}

fun tyinfo_multispec_contribution _ =
  [(tyinfo_multispec_intro,
    ("claset-tyinfo-multispec-intro", tyinfo_multispec_rule)),
   (tyinfo_multispec_elim,
    ("claset-tyinfo-multispec-elim", tyinfo_multispec_rule))]

val _ =
  test
    ("claset TypeBase contributions keep cross-kind specifications",
     fn () =>
       let
         val _ = register_tyinfo_contribution
           ("claset-selftest-multispec", tyinfo_multispec_contribution)
         val rules = rules_of (the_claset ())
         fun present spec name =
           List.exists
             (fn (spec', (name', th')) =>
                name = name' andalso same_spec spec spec' andalso
                same_thm
                  (canonical_rule_of (#kind spec) tyinfo_multispec_rule)
                  th')
             rules
       in
         present tyinfo_multispec_intro "claset-tyinfo-multispec-intro"
           andalso
         present tyinfo_multispec_elim "claset-tyinfo-multispec-elim"
       end)

val tyinfo_replace_p = ``claset_tyinfo_replace_p : bool``
val tyinfo_replace_q = ``claset_tyinfo_replace_q : bool``
val tyinfo_replace_old_rule =
  DISCH tyinfo_replace_p
    (DISJ1 (ASSUME tyinfo_replace_p) tyinfo_replace_q)
val tyinfo_replace_new_rule =
  DISCH tyinfo_replace_q
    (DISJ2 tyinfo_replace_p (ASSUME tyinfo_replace_q))

fun tyinfo_replacement name th _ =
  [(tyinfo_idempotence_spec, (name, th))]

val _ =
  test
    ("replacing a TypeBase contribution removes its stale rules",
     fn () =>
       let
         val key = "claset-selftest-replacement"
         val old_name = "claset-tyinfo-replacement-old"
         val new_name = "claset-tyinfo-replacement-new"
         val _ = register_tyinfo_contribution
           (key, tyinfo_replacement old_name tyinfo_replace_old_rule)
         val _ = register_tyinfo_contribution
           (key, tyinfo_replacement new_name tyinfo_replace_new_rule)
         val rules = rules_of (the_claset ())
         fun named name = List.exists (fn (_, (name', _)) => name = name') rules
       in
         not (named old_name) andalso named new_name
       end)


(* clasetLib: per-invocation markers. *)
fun has_marker_rule spec th cs =
  List.exists
    (fn (spec', (_, th')) =>
       same_spec spec spec' andalso
       same_thm (canonical_rule_of (#kind spec) th) th')
    (rules_of cs)

val marker_sintro_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE}
val marker_intro_spec =
  {kind = clasetRules.Intro, safe = false, prio = NONE}
val marker_selim_spec =
  {kind = clasetRules.Elim, safe = true, prio = NONE}
val marker_elim_spec =
  {kind = clasetRules.Elim, safe = false, prio = NONE}
val marker_sdest_spec =
  {kind = clasetRules.Dest, safe = true, prio = NONE}
val marker_dest_spec =
  {kind = clasetRules.Dest, safe = false, prio = NONE}

val marker_cases =
  [("SIntro", SIntro, destSIntro, marker_sintro_spec,
    boolTheory.AND_INTRO_THM),
   ("Intro", Intro, destIntro, marker_intro_spec, boolTheory.AND_INTRO_THM),
   ("SElim", SElim, destSElim, marker_selim_spec, boolTheory.OR_ELIM_THM),
   ("Elim", Elim, destElim, marker_elim_spec, boolTheory.OR_ELIM_THM),
   ("SDest", SDest, destSDest, marker_sdest_spec, boolTheory.OR_ELIM_THM),
   ("Dest", Dest, destDest, marker_dest_spec, boolTheory.OR_ELIM_THM)]

val simpset_marker_cases =
  [("Simp", Simp, destSimp, boolTheory.AND_CLAUSES),
   ("Iff", Iff, destIff, boolTheory.IMP_CLAUSES)]

val classical_marker_theorems =
  [SIntro boolTheory.AND_INTRO_THM,
   Intro boolTheory.AND_INTRO_THM,
   SElim boolTheory.OR_ELIM_THM,
   Elim boolTheory.OR_ELIM_THM,
   SDest boolTheory.OR_ELIM_THM,
   Dest boolTheory.OR_ELIM_THM,
   Simp boolTheory.AND_CLAUSES,
   Iff boolTheory.IMP_CLAUSES,
   Del "claset-selftest"]

val marker_prefix = "__claset_marker_"

fun named_marker_is name th cs =
  case List.find (fn (_, (name', _)) => name = name') (rules_of cs) of
      SOME (_, (_, th')) => same_thm (canonical_rule th) th'
    | NONE => false

val _ =
  test
    ("claset markers round-trip and add their temporary rules",
     fn () =>
       List.all
         (fn (_, mark, dest, spec, th) =>
            let
              val marked = mark th
              val (cs, rest) = process_claset_tags [marked] empty_cs
            in
              (case dest marked of
                   SOME th' => same_thm th th'
                 | NONE => false) andalso
              List.null rest andalso has_marker_rule spec th cs
            end)
         marker_cases)

val _ =
  test
    ("simpset markers round-trip without becoming claset rules",
     fn () =>
       List.all
         (fn (_, mark, dest, th) =>
            let
              val marked = mark th
              val (cs, rest) = process_claset_tags [marked] empty_cs
            in
              (case dest marked of
                   SOME th' => same_thm th th'
                 | NONE => false) andalso
              List.null (rules_of cs) andalso
              ListPair.allEq
                (fn (left, right) => same_thm left right)
                (rest, [marked])
            end)
         simpset_marker_cases)

val _ =
  test
    ("generic simp-marker recognition excludes every claset marker",
     fn () =>
       List.all
         (not o markerLib.is_generic_simp_marker)
         classical_marker_theorems)

val _ =
  test
    ("Del removes a rule from the invocation claset only",
     fn () =>
       let
         val name = "claset-marker-deleted"
         val base = add_sintros [(name, boolTheory.AND_INTRO_THM)] empty_cs
         val marked = Del name
         val (cs, rest) = process_claset_tags [marked] base
       in
         destDel marked = SOME name andalso List.null rest andalso
         has_named_rule name base andalso not (has_named_rule name cs)
       end)

val _ =
  test
    ("claset markers receive contiguous lowest-unused names",
     fn () =>
       let
         val ths = [boolTheory.TRUTH, boolTheory.AND_INTRO_THM,
                    boolTheory.IMP_ANTISYM_AX]
         val (cs, rest) = process_claset_tags (map SIntro ths) empty_cs
       in
         List.null rest andalso
         ListPair.allEq
           (fn (index, th) =>
              named_marker_is (marker_prefix ^ Int.toString index) th cs)
           ([0, 1, 2], ths)
       end)

val _ =
  test
    ("claset marker allocation fills a name gap without dropping rules",
     fn () =>
       let
         val base =
           add_sintros
             [(marker_prefix ^ "1", boolTheory.TRUTH)] empty_cs
         val ths = [boolTheory.AND_INTRO_THM, boolTheory.IMP_ANTISYM_AX]
         val (cs, rest) = process_claset_tags (map SIntro ths) base
       in
         List.null rest andalso length (rules_of cs) = 3 andalso
         named_marker_is (marker_prefix ^ "0") (hd ths) cs andalso
         named_marker_is (marker_prefix ^ "1") boolTheory.TRUTH cs andalso
         named_marker_is (marker_prefix ^ "2") (List.last ths) cs
       end)

val _ =
  test
    ("a rejected duplicate marker does not consume its name",
     fn () =>
       let
         val first = boolTheory.AND_INTRO_THM
         val second = boolTheory.IMP_ANTISYM_AX
         val input = [SIntro first, SIntro first, SIntro second]
         val (cs, rest) = process_claset_tags input empty_cs
       in
         List.null rest andalso length (rules_of cs) = 2 andalso
         named_marker_is (marker_prefix ^ "0") first cs andalso
         named_marker_is (marker_prefix ^ "1") second cs
       end)

val _ =
  test
    ("deleting a marker makes its lowest name reusable",
     fn () =>
       let
         val first = boolTheory.AND_INTRO_THM
         val second = boolTheory.IMP_ANTISYM_AX
         val input = [SIntro first, Del (marker_prefix ^ "0"), SIntro second]
         val (cs, rest) = process_claset_tags input empty_cs
       in
         List.null rest andalso length (rules_of cs) = 1 andalso
         named_marker_is (marker_prefix ^ "0") second cs
       end)

val _ =
  test
    ("claset marker processing passes other markers and plain theorems through",
     fn () =>
       let
         val plain = boolTheory.TRUTH
         val cong = markerLib.Cong (ASSUME p)
         val excl = markerLib.Excl "simp-only"
         val input = [cong, excl, plain]
         val (cs, rest) = process_claset_tags input empty_cs
       in
         List.null (rules_of cs) andalso
         ListPair.allEq (fn (th1, th2) => same_thm th1 th2) (input, rest)
       end)


val _ =
  test
    ("claset marker processing preserves mixed leftovers in input order",
     fn () =>
       let
         val plain1 = boolTheory.TRUTH
         val plain2 = boolTheory.IMP_F
         val cong = markerLib.Cong (ASSUME p)
         val input =
           [plain1, SIntro boolTheory.AND_INTRO_THM, cong,
            Del (marker_prefix ^ "0"), plain2,
            SIntro boolTheory.IMP_ANTISYM_AX]
         val (cs, rest) = process_claset_tags input empty_cs
       in
         named_marker_is (marker_prefix ^ "0") boolTheory.IMP_ANTISYM_AX cs
           andalso
         ListPair.allEq (fn (th1, th2) => same_thm th1 th2)
           (rest, [plain1, cong, plain2])
       end)

val _ =
  test
    ("inert generic simp markers do not change invocation facts",
     fn () =>
       let
         val plain = boolTheory.TRUTH
         val markers =
           [markerLib.AC boolTheory.AND_CLAUSES boolTheory.OR_CLAUSES,
            markerLib.Cong boolTheory.AND_CLAUSES,
            markerLib.Split boolTheory.OR_CLAUSES,
            markerLib.Excl "claset-selftest",
            markerLib.ExclSF "claset-selftest",
            markerLib.FRAG "claset-selftest",
            markerLib.NoAsms,
            markerLib.IgnAsm [QUOTE "claset_ignored"],
            markerLib.Abbr [QUOTE "claset_abbreviation"]]
         val (baseline_cs, baseline_facts) =
           invocation_claset empty_cs [plain]
         val (with_markers_cs, with_markers_facts) =
           invocation_claset empty_cs
             (List.take (markers, 4) @ [plain] @
              List.drop (markers, 4))
       in
         List.all markerLib.is_generic_simp_marker markers andalso
         same_rules (rules_of baseline_cs) (rules_of with_markers_cs)
           andalso
         null (rules_of with_markers_cs) andalso
         ListPair.allEq (fn (left, right) => same_thm left right)
           (baseline_facts, with_markers_facts) andalso
         ListPair.allEq (fn (left, right) => same_thm left right)
           (with_markers_facts, [plain])
       end)

val _ =
  test
    ("content-bearing simp wrappers become invocation facts",
     fn () =>
       let
         val payload = boolTheory.IMP_CLAUSES
         val wrapped =
           markerLib.mk_Req0
             (markerLib.mk_ReqD (BoundedRewrites.Once payload))
         val (cs, facts) = invocation_claset empty_cs [wrapped]
       in
         markerLib.is_generic_simp_marker wrapped andalso
         null (rules_of cs) andalso
         ListPair.allEq (fn (left, right) => same_thm left right)
           (facts, [payload])
       end)
