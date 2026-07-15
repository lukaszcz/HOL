open HolKernel Parse Tactic testutils
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
