open HolKernel testutils autoSeedTheory simpLib

val _ = intLinarith.instance
val _ = Theory.new_theory "seedCollectionSelftest"

fun check (name, predicate) =
  (tprint name;
   if predicate () then OK () else die "failed")

val _ =
  check
    ("Phase-8 named seed collections are registered",
     fn () =>
       List.all
         (fn name =>
           List.exists (equal name) (ThmSetData.all_set_types ()) andalso
           ThmAttribute.is_attribute name)
         ["algebra_simps", "field_simps"])

val _ =
  check
    ("seed collections expose usable stateful fragments",
     fn () =>
       not (null (seedCollections.algebra_rewrites ())) andalso
       (ignore (seedCollections.algebra_ss ()); true) andalso
       (ignore (seedCollections.field_ss ()); true))

val audit_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE}

val audit_good_cs =
  clasetLib.add_rule audit_spec
    ("audit_good", boolTheory.AND_INTRO_THM) clasetLib.empty_cs

val audit_bad_cs =
  clasetLib.add_rule audit_spec
    ("audit_bad", boolTheory.OR_INTRO_THM1) clasetLib.empty_cs

val audit_waiver =
  {rule = "audit_bad", reason = "selftest exercises waiver plumbing",
   date = "2026-08-10"}

fun failed_result (seedAudit.Failed _) = true
  | failed_result _ = false

fun waived_result (seedAudit.Waived _) = true
  | waived_result _ = false

val _ =
  check
    ("seed audit proves an invertible safe introduction rule",
     fn () =>
       let
         val report =
           seedAudit.audit_with
             {claset = audit_good_cs,
              budget = Time.fromSeconds 5, waivers = []}
       in
         #checked report = #proved report andalso
         List.exists
           (fn seedAudit.Proved {rule, ...} => rule = "audit_good"
             | _ => false)
           (#results report)
       end)

val _ =
  check
    ("seed audit reports an unwaivered non-invertible safe rule",
     fn () =>
       let
         val report =
           seedAudit.inspect
             {claset = audit_bad_cs,
              budget = Time.fromSeconds 1, waivers = []}
       in
         List.exists failed_result (#results report)
       end)

val slow_variables =
  List.tabulate
    (24, fn i =>
       Term.mk_var ("audit_slow_" ^ Int.toString i, Type.bool))
val slow_premise = hd slow_variables
val slow_conclusion =
  List.foldl
    (fn (alternative, conclusion) =>
      boolSyntax.mk_disj (conclusion, alternative))
    slow_premise (tl slow_variables)
val slow_theorem =
  DISCH slow_premise
    (List.foldl
       (fn (alternative, theorem) => DISJ1 theorem alternative)
       (ASSUME slow_premise) (tl slow_variables))
val slow_audit_cs =
  clasetLib.add_rule audit_spec
    ("audit_budget", slow_theorem) clasetLib.empty_cs

val _ =
  check
    ("seed audit interrupts a prover at the obligation budget",
     fn () =>
       let
         val timer = Timer.startRealTimer ()
         val report =
           seedAudit.inspect
             {claset = slow_audit_cs,
              budget = Time.fromReal 0.01, waivers = []}
         val elapsed = Timer.checkRealTimer timer
       in
         List.exists failed_result (#results report) andalso
         Time.< (elapsed, Time.fromReal 0.5)
       end)

val _ =
  check
    ("seed audit consumes a dated waiver",
     fn () =>
       let
         val report =
           seedAudit.audit_with
             {claset = audit_bad_cs,
              budget = Time.fromSeconds 1, waivers = [audit_waiver]}
       in
         length (#waivers report) = 1 andalso
         List.exists waived_result (#results report)
       end)

val _ =
  check
    ("seed audit rejects stale waivers in the passing direction",
     fn () =>
       let
         val stale =
           {rule = "audit_good", reason = "must be stale",
            date = "2026-08-10"}
         val report =
           seedAudit.inspect
             {claset = audit_good_cs,
              budget = Time.fromSeconds 5, waivers = [stale]}
       in
         List.exists failed_result (#results report)
       end)

val _ =
  check
    ("assembled Phase-8 seed and TypeBase safe corpus passes the audit",
     fn () =>
       let
         val report = seedAudit.audit {waivers = []}
       in
         #checked report = #proved report andalso null (#waivers report)
       end)

val expected_seeds =
  ["clasetSeed", "pairAutoSeed", "sumAutoSeed", "optionAutoSeed",
   "listAutoSeed", "pred_setAutoSeed", "arithmeticAutoSeed",
   "finite_mapAutoSeed", "integerAutoSeed", "realAutoSeed",
   "stringAutoSeed", "rich_listAutoSeed", "sortingAutoSeed"]

val _ =
  check
    ("autoSeed umbrella contains every per-theory seed",
     fn () =>
       let val ancestry = Theory.ancestry "autoSeed"
       in List.all (fn name => List.exists (equal name) ancestry)
            expected_seeds
       end)

fun starts_with prefix text =
  size text >= size prefix andalso
  String.substring (text, 0, size prefix) = prefix

fun is_seed name =
  String.isSubstring "AutoSeed$" name orelse
  starts_with "clasetSeed$" name

fun is_typebase name = starts_with "__claset_tyinfo_" name

fun same_decl
      ({spec = left_spec, thm = left_thm, ...} : clasetLib.aesop_rule)
      ({spec = right_spec, thm = right_thm, ...} : clasetLib.aesop_rule) =
  #kind left_spec = #kind right_spec andalso
  #safe left_spec = #safe right_spec andalso
  aconv (concl left_thm) (concl right_thm)

val _ =
  check
    ("seed declarations do not duplicate TypeBase contributions",
     fn () =>
       let
         val rules = clasetLib.all_rules (clasetLib.the_claset ())
         val seeds = List.filter (is_seed o #name) rules
         val typebase = List.filter (is_typebase o #name) rules
       in
         not
           (List.exists
             (fn seed => List.exists (same_decl seed) typebase)
             seeds)
       end)

fun rule_names () =
  map #name (clasetLib.all_rules (clasetLib.the_claset ()))

val _ =
  check
    ("loading the autoSeed umbrella twice is delta-idempotent",
     fn () =>
       let
         val rules_before = rule_names ()
         val algebra_before = length (seedCollections.algebra_rewrites ())
         val field_before = length (seedCollections.field_rewrites ())
         val split_before = length (splitLib.split_thms ())
         val _ = Theory.load_complete "autoSeed"
         val _ = Theory.load_complete "autoSeed"
       in
         rules_before = rule_names () andalso
         algebra_before = length (seedCollections.algebra_rewrites ()) andalso
         field_before = length (seedCollections.field_rewrites ()) andalso
         split_before = length (splitLib.split_thms ())
       end)

fun solved tactic goal =
  case Tactical.VALID tactic ([], goal) of
      ([], validation) => (ignore (validation []); true)
    | _ => false

val _ =
  check
    ("representative pair/list/set/map/string seed views are usable",
     fn () =>
       List.all
         (solved (clasimpLib.AUTO_TAC []))
         [``UNCURRY c p <=> !x y. p = (x,y) ==> c x y``,
          ``LIST_REL R [] ys <=> ys = []``,
          ``start <= finish ==>
            GENLIST (\offset. start + offset) (SUC finish - start) =
            GENLIST (\offset. start + offset) (finish - start) ++ [finish]``,
          ``x IN (s UNION t) <=> x IN s \/ x IN t``,
          ``INJ (\x : 'a. x) s UNIV``,
          ``FLOOKUP (FUNION n m) k = NONE <=>
            FLOOKUP n k = NONE /\ FLOOKUP m k = NONE``,
          ``ALL_DISTINCT (MAP FST association) ==>
            MEM (key, value) association ==>
            ALOOKUP association key = SOME value``,
          ``ALL_DISTINCT (MAP FST association) ==>
            (ALOOKUP association key = SOME value <=>
             MEM (key, value) association)``,
          ``STRLEN text = 0 <=> text = ""``])

val _ =
  check
    ("representative arithmetic and sorting seed views are usable",
     fn () =>
       solved (linarithLib.LINARITH_TAC [])
         ``(x : int) < y ==> x - y < 0`` andalso
       solved (clasimpLib.AUTO_TAC [])
         ``PERM ([] : 'a list) xs <=> xs = []``)

(* src/HOL/List.thy:1381,1222-1228,2826-2827,6208 @ f7e02b7e.  Isabelle
   decides these ambiently: set_upt turns an interval list into the
   interval set, map_fst_zip, map_snd_zip and nth_zip project a zip whose
   sides have equal length, and sorted_upt sorts an interval.  None of
   the goals below is a corpus entry; each is a consequence reached by a
   seed and then arithmetic, and excluding the five seeds leaves every
   one of them with a residual.  The last is the third eta-expanded,
   which meets its rule only because the simpset matches modulo eta. *)
val _ =
  check
    ("interval and zip seed views are usable",
     fn () =>
       List.all
         (solved (clasimpLib.AUTO_TAC []))
         [``!n item. MEM item (GENLIST (\offset. offset) (SUC n)) <=>
                     item <= n``,
          ``!lower upper item.
              lower <= item /\ item < upper ==>
              MEM item (GENLIST ($+ lower) (upper - lower))``,
          ``!start xs item.
              MEM item xs ==>
              MEM item (MAP SND (ZIP (GENLIST ($+ start) (LENGTH xs),
                                      xs)))``,
          ``!start xs index.
              index < LENGTH xs ==>
              MEM (FST (EL index (ZIP (GENLIST ($+ start) (LENGTH xs),
                                       xs))))
                  (GENLIST ($+ start) (LENGTH xs))``,
          ``!start count.
              SORTED $<= (GENLIST ($+ start) count ++ [start + count])``,
          ``!start xs item.
              MEM item xs ==>
              MEM item
                (MAP SND (ZIP (GENLIST (\offset. start + offset)
                                 (LENGTH xs),
                               xs)))``])

val _ =
  check
    ("universal image membership simplifies through an implication",
     fn () =>
       solved
         (simpLib.FULL_SIMP_TAC (clasimpLib.clasimp_ss ()) [])
         ``(!y. y IN IMAGE (f : 'a -> 'b) source ==> property y) ==>
           !x. x IN source ==> property (f x)``)

val _ =
  check
    ("collection local add/remove round-trips update both fragments",
     fn () =>
       let
         val theory = Theory.current_theory ()
         fun roundtrip attribute rewrites remove suffix theorem =
           let
             val prior_count = length (rewrites ())
             val _ =
               ThmAttribute.local_attribute
                 {name = suffix, attrname = attribute, args = [],
                  thm = theorem}
             val added = length (rewrites ()) = prior_count + 1
             val _ = remove (theory ^ "." ^ suffix)
           in
             added andalso length (rewrites ()) = prior_count
           end
       in
         roundtrip "algebra_simps" seedCollections.algebra_rewrites
           seedCollections.remove_algebra_simps
           "ALGEBRA_COLLECTION_ROUNDTRIP" boolTheory.AND_CLAUSES andalso
         roundtrip "field_simps" seedCollections.field_rewrites
           seedCollections.remove_field_simps
           "FIELD_COLLECTION_ROUNDTRIP" boolTheory.OR_CLAUSES
       end)

val _ =
  check
    ("Excl suppresses a named field collection member",
     fn () =>
       let
         val redex = ``inv (x : real)``
         val fragment = simpLib.empty_ss ++ seedCollections.field_ss ()
         fun result controls =
           boolSyntax.rhs
             (concl (Conv.QCONV (SIMP_CONV fragment controls) redex))
         val normal = result []
         val excluded =
           result
             [markerLib.Excl
                "realAutoSeed$REAL_INV_1OVER_FIELD"]
       in
         if not (aconv normal ``1 / (x : real)``) then
           raise Fail
             ("unexpected field rewrite: " ^ Parse.term_to_string normal)
         else if not (aconv excluded redex) then
           raise Fail
             ("Excl left rewrite active: " ^
              Parse.term_to_string excluded)
         else true
       end)

val _ =
  check
    ("collection removal updates both stateful fragments",
     fn () =>
       let
         val algebra_before = length (seedCollections.algebra_rewrites ())
         val field_before = length (seedCollections.field_rewrites ())
         val _ = seedCollections.remove_algebra_simps
           "arithmeticAutoSeed.ADD_ASSOC_ALGEBRA"
         val _ = seedCollections.remove_field_simps
           "realAutoSeed.REAL_INV_1OVER_FIELD"
         val algebra_after = length (seedCollections.algebra_rewrites ())
         val field_after = length (seedCollections.field_rewrites ())
       in
         algebra_after + 1 = algebra_before andalso
         field_after + 1 = field_before andalso
         (ignore (seedCollections.algebra_ss ()); true) andalso
         (ignore (seedCollections.field_ss ()); true)
       end)

(* A set written as an abstraction is a membership only after beta.  This
   is the shape a set-of-keys obligation has when the set former was
   unfolded before the goal reached the engine; the names are this file's
   own.  The bound is here because the failure this pins is a search that
   does not come back, not one that reports no proof. *)
val abstraction_subset_goal : Abbrev.goal =
  ([],
   ``(!seed_dom_key seed_dom_value.
        seed_dom_left seed_dom_key = SOME seed_dom_value ==>
        seed_dom_right seed_dom_key = SOME seed_dom_value) ==>
     (\seed_dom_key. seed_dom_left seed_dom_key <> NONE) SUBSET
     (\seed_dom_key. seed_dom_right seed_dom_key <> NONE)``)

(* A tactic that reports no proof has come back, which is what the bound is
   about; only the timeout distinguishes the two outcomes below. *)
fun within seconds interpret tactic goal =
  interpret
    (Timeout.apply (Time.fromSeconds seconds)
      (fn () =>
        SOME (Tactical.VALID tactic goal) handle HOL_ERR _ => NONE) ())
  handle Timeout.TIMEOUT _ => false

fun closes_within seconds =
  within seconds
    (fn SOME (remaining, _) => List.null remaining | NONE => false)

fun terminates_within seconds = within seconds (fn _ => true)

val _ =
  check
    ("FASTFORCE closes a subset between two abstractions",
     fn () =>
       closes_within 20 (clasimpLib.FASTFORCE_TAC []) abstraction_subset_goal)

(* The state the search above reaches once it has a witness: a negated
   equation to prove against a stored implication and a contradicting
   value.  A depth-first search used not to come back from here at all --
   the unsafe simp wrapper rebuilt the negation that the classical [~]
   introduction had just taken apart, and the two alternated for ever.
   Whether FAST search closes it is a question of strength and is left a
   pass either way; that it terminates and reports what it found is not. *)
val negated_equation_goal : Abbrev.goal =
  ([``!seed_neg_key seed_neg_value.
        seed_neg_left seed_neg_key = SOME seed_neg_value ==>
        seed_neg_right seed_neg_key = SOME seed_neg_value``,
    ``seed_neg_right seed_neg_x = NONE``],
   ``seed_neg_left seed_neg_x <> SOME seed_neg_y``)

val _ =
  check
    ("FASTFORCE terminates on a negated equation with a stored implication",
     fn () =>
       terminates_within 20 (clasimpLib.FASTFORCE_TAC [])
         negated_equation_goal)

(* src/HOL/Set.thy:551 @ f7e02b7e.  Neither goal is a corpus entry.  The
   claset's set equality was introduction-only, so a search that had to
   read an equality out of the hypotheses reported no proof without
   engaging at all; withholding SET_EQUALITY_CASES_AUTO leaves both of
   these unproved. *)
val _ =
  check
    ("a set equality among the hypotheses is usable by the search",
     fn () =>
       List.all
         (closes_within 20 (tableauLib.BLAST_TAC []))
         [([], ``(left : 'a set) UNION right = {} ==> left = {}``),
          ([], ``(left : 'a set) INTER right = left ==> left SUBSET right``)])
