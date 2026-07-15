open HolKernel Parse Tactic testutils boolSyntax
open NTactical clasetNet clasetRules

fun test (name, check) =
  (tprint name;
   if check () then OK () else die "failed")

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
    ("rule_index rejects premise-free elimination rules",
     fn () =>
       not (can (rule_index Elim) boolTheory.TRUTH))

fun info_of th = {rl = (th, NONE), dup_rl = (th, NONE)}
val safe_intro = {kind = Intro, safe = true, prio = NONE}
val safe_elim = {kind = Elim, safe = true, prio = NONE}

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
         merged_names = ["c", "d", "b", "a"]
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
         val spec = {kind = Dest, safe = false, prio = SOME 75}
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
         val spec = {kind = Intro, safe = true, prio = NONE}
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
         val spec = {kind = Dest, safe = true, prio = NONE}
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

val _ =
  test
    ("ext_info rejects premise-free eliminations and classifies safe rules",
     fn () =>
       let
         val safe_elim = {kind = Elim, safe = true, prio = NONE}
         val safe0 = ext_info safe_elim boolTheory.FALSITY
         val safep = ext_info safe_elim boolTheory.OR_ELIM_THM
       in
         same_thm (CLASSICAL_RULE boolTheory.FALSITY)
           (canonical_rule boolTheory.FALSITY) andalso
         not (can (ext_info safe_elim) boolTheory.TRUTH) andalso
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
