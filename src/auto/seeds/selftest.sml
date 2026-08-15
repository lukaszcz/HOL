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
