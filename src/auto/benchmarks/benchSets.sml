structure benchSets =
struct

open HolKernel autoSeedTheory

val commit = "f7e02b7e"

fun exact theorem goal = Drule.PART_MATCH I theorem goal

fun entry id line method mapped excl goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method,
   recipe = benchLib.Invoke (mapped, []), excl = excl,
   provenance =
     {file = "src/HOL/Set.thy", line = line, commit = commit},
   representative = true}

fun example id line method mapped goal : benchLib.corpus_goal =
  let
    val arguments =
      [benchLib.RewriteAdd
           {name =
              "paritySetTranslation$source_compl_image_fixedpoint_iff",
            theorem =
              paritySetTranslationTheory.source_compl_image_fixedpoint_iff},
       benchLib.RewriteAdd
           {name = "parityTranslation$source_num_set_induction_iff",
            theorem =
              parityTranslationTheory.source_num_set_induction_iff},
       benchLib.RewriteAdd
           {name = "parityTranslation$source_mem_bigunion_image",
            theorem = parityTranslationTheory.source_mem_bigunion_image},
         benchLib.FactAdd
           {name = "parityTranslation$source_predicate_set_witness",
            theorem =
              parityTranslationTheory.source_predicate_set_witness},
         benchLib.RewriteAdd
           {name = "parityTranslation$source_nonempty_predicate_set",
            theorem =
              parityTranslationTheory.source_nonempty_predicate_set},
         benchLib.RewriteAdd
           {name = "parityTranslation$source_set_separates_image",
            theorem = parityTranslationTheory.source_set_separates_image},
         benchLib.RewriteAdd
           {name = "parityTranslation$source_nonnegative_neq_negative",
            theorem =
              parityTranslationTheory.source_nonnegative_neq_negative},
         benchLib.RewriteAdd
           {name = "parityTranslation$source_set_separates_two",
            theorem = parityTranslationTheory.source_set_separates_two},
         benchLib.RewriteAdd
           {name = "parityTranslation$source_exists_not_member",
            theorem = parityTranslationTheory.source_exists_not_member},
         benchLib.RewriteAdd
           {name = "parityTranslation$source_exists_singleton_superset",
            theorem =
              parityTranslationTheory.source_exists_singleton_superset}]
    val recipe =
      if id = "set_theory_L79" then
        benchLib.AllGoals
          (benchLib.Invoke (benchLib.Simp, arguments),
           benchLib.Invoke (benchLib.Blast, arguments))
      else if mapped = benchLib.Force then
        benchLib.AllGoals
          (benchLib.Invoke (benchLib.Simp, arguments),
           benchLib.Invoke (benchLib.Force, arguments))
      else if mapped = benchLib.Auto then
        benchLib.AllGoals
          (benchLib.Invoke (benchLib.Simp, arguments),
           benchLib.Invoke (benchLib.Auto, arguments))
      else
        benchLib.Invoke (mapped, arguments)
  in
    {id = id, goal = goal, source_method = method, recipe = recipe,
     excl = [],
     provenance =
       {file = "src/HOL/ex/Set_Theory.thy", line = line,
        commit = commit},
     representative = false}
  end

val example_goals =
  [example "set_theory_L18" 18 "by blast" benchLib.Blast
     ``xset = yset UNION zset <=>
       yset SUBSET xset /\ zset SUBSET xset /\
       !vset. yset SUBSET vset /\ zset SUBSET vset ==>
         xset SUBSET vset``,
   example "set_theory_L22" 22 "by blast" benchLib.Blast
     ``xset = yset INTER zset <=>
       xset SUBSET yset /\ xset SUBSET zset /\
       !vset. vset SUBSET yset /\ vset SUBSET zset ==>
         vset SUBSET xset``,
   example "set_theory_L36" 36 "by blast" benchLib.Blast
     ``BIGUNION (IMAGE (\x. f x UNION g x) family) =
       BIGUNION (IMAGE f family) UNION
       BIGUNION (IMAGE g family)``,
   example "set_theory_L40" 40 "by blast" benchLib.Blast
     ``BIGINTER (IMAGE (\x. f x INTER g x) family) =
       BIGINTER (IMAGE f family) INTER
       BIGINTER (IMAGE g family)``,
   example "set_theory_L44" 44 "by blast" benchLib.Blast
     ``(!x. x IN (sets : 'a set set) ==>
          !y. y IN sets ==> x SUBSET y) ==>
       ?z. sets SUBSET {z}``,
   example "set_theory_L48" 48 "by blast" benchLib.Blast
     ``(!x. x IN (sets : 'a set set) ==> BIGUNION sets SUBSET x) ==>
       ?z. sets SUBSET {z}``,
   example "set_theory_L79" 79
     "using lfp_unfold [OF monoI, of F] by blast" benchLib.Blast
     ``?fixed. fixed = COMPL (IMAGE g (COMPL (IMAGE f fixed)))``,
   example "set_theory_L156" 156 "by force" benchLib.Force
     ``?aset : int set. !x. x IN aset ==> x <= 0``,
   example "set_theory_L160" 160 "by force" benchLib.Force
     ``d IN fam ==> ?groups. !aset. aset IN groups ==>
       ?bset. bset IN fam /\ aset SUBSET bset``,
   example "set_theory_L164" 164 "by force" benchLib.Force
     ``P a ==> ?aset. (!x. x IN aset ==> P x) /\ ?y. y IN aset``,
   example "set_theory_L168" 168 "by auto" benchLib.Auto
     ``a < (b : int) /\ b < c ==>
       ?aset. a NOTIN aset /\ b IN aset /\ c NOTIN aset``,
   example "set_theory_L172" 172 "by force" benchLib.Force
     ``P (f b) ==> ?s aset. (!x. x IN aset ==> P x) /\ f s IN aset``,
   example "set_theory_L180" 180 "by force" benchLib.Force
     ``?aset. a NOTIN aset``,
   example "set_theory_L184" 184 "by force" benchLib.Force
     ``(!u v : int. u < 0 ==> u <> ABS v) ==>
       ?aset : int set. -2 IN aset /\ !y. ABS y NOTIN aset``,
   example "set_theory_L199" 199 "by auto" benchLib.Auto
     ``((!aset : num set.
          0 IN aset /\ (!x. x IN aset ==> SUC x IN aset) ==>
            n IN aset) /\
        P 0 /\ (!x. P x ==> P (SUC x))) ==> P n``]

val translated_goals : benchLib.corpus_goal list =
  [{id = "set_L461_ball_cong_simp",
    goal = Thm.concl parityTranslationTheory.source_ball_cong_simp,
    source_method =
      "by (simp add: simp_implies_def Ball_def)",
    recipe =
      benchLib.Invoke
        (benchLib.Simp,
         [benchLib.DefinitionAdd
            {name = "parityTranslation$source_ball_def",
             theorem = parityTranslationTheory.source_ball_def}]),
    excl = [],
    provenance =
      {file = "src/HOL/Set.thy", line = 461, commit = commit},
    representative = false},
   {id = "set_L471_bex_cong_simp",
    goal = Thm.concl parityTranslationTheory.source_bex_cong_simp,
    source_method =
      "by (simp add: simp_implies_def Bex_def cong: conj_cong)",
    recipe =
      benchLib.Invoke
        (benchLib.Simp,
         [benchLib.DefinitionAdd
            {name = "parityTranslation$source_bex_def",
             theorem = parityTranslationTheory.source_bex_def},
          benchLib.CongruenceAdd
            {name = "bool$AND_CONG",
             theorem = boolTheory.AND_CONG}]),
    excl = [],
    provenance =
      {file = "src/HOL/Set.thy", line = 471, commit = commit},
    representative = false},
   {id = "set_L972_image_cong_simp",
    goal = Thm.concl parityTranslationTheory.source_image_cong_simp,
    source_method = "using that image_cong [of M N f g] " ^
                    "by (simp add: simp_implies_def)",
    recipe =
      benchLib.Invoke
        (benchLib.Simp,
         [benchLib.DefinitionAdd
            {name = "parityTranslation$source_image_def",
             theorem = parityTranslationTheory.source_image_def},
          benchLib.FactAdd
            {name = "pred_set$IMAGE_CONG",
             theorem = pred_setTheory.IMAGE_CONG}]),
    excl = [],
    provenance =
      {file = "src/HOL/Set.thy", line = 972, commit = commit},
    representative = false},
   {id = "set_L994_image_add_0",
    goal = Thm.concl parityTranslationTheory.source_image_add_zero,
    source_method = "by auto",
    recipe =
      benchLib.Invoke
        (benchLib.Auto,
         [benchLib.DefinitionAdd
            {name = "parityTranslation$source_add_image_def",
             theorem = parityTranslationTheory.source_add_image_def},
          benchLib.DestAdd
            (benchLib.SafeRule,
             {name = "parityTranslation$source_abelian_monoid_is_monoid",
              theorem =
                parityTranslationTheory.source_abelian_monoid_is_monoid}),
          benchLib.RewriteAdd
            {name = "monoid$monoid_lid",
             theorem = monoidTheory.monoid_lid},
          benchLib.IntroAdd
            (benchLib.SafeRule,
             {name = "pred_set$IMAGE_CONG",
              theorem = pred_setTheory.IMAGE_CONG}),
          benchLib.RewriteAdd
            {name = "parityTranslation$source_add_image_preimage",
             theorem =
               parityTranslationTheory.source_add_image_preimage}]),
    excl = [],
    provenance =
      {file = "src/HOL/Set.thy", line = 994, commit = commit},
    representative = false}]

val goals =
  map benchLib.prepare_goal
    (example_goals @ translated_goals @ benchSetCorpus.goals)

val shortfalls : benchLib.shortfall list = benchSetShortfalls.entries

fun run level =
  benchLib.run_family
    {family = "sets", goals = goals, shortfalls = shortfalls,
     budget = benchLib.default_budget,
     battery = [benchLib.Blast, benchLib.Aesop], level = level}

end
