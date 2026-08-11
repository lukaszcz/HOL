structure benchSets =
struct

open HolKernel autoSeedTheory

val commit = "f7e02b7e"

fun exact theorem goal = Drule.PART_MATCH I theorem goal

fun entry id line method mapped excl goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method,
   mapped = mapped, excl = excl,
   provenance =
     {file = "src/HOL/Set.thy", line = line, commit = commit},
   representative = true}

fun example id line method mapped goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method,
   mapped = mapped, excl = [],
   provenance =
     {file = "src/HOL/ex/Set_Theory.thy", line = line,
      commit = commit},
   representative = false}

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

val goals = example_goals @ benchSetCorpus.goals

val shortfalls : benchLib.shortfall list =
  benchSetShortfalls.entries @
  [{id = "set_L461_ball_cong_simp", cause = benchLib.TranslationGap,
    date = "2026-08-10",
    note = "Isabelle's simplifier/meta connective has no HOL4 " ^
           "object-term translation"},
   {id = "set_L471_bex_cong_simp", cause = benchLib.TranslationGap,
    date = "2026-08-10",
    note = "Isabelle's simplifier/meta connective has no HOL4 " ^
           "object-term translation"},
   {id = "set_L972_image_cong_simp", cause = benchLib.TranslationGap,
    date = "2026-08-10",
    note = "Isabelle's simplifier/meta connective has no HOL4 " ^
           "object-term translation"},
   {id = "set_L994_image_add_0", cause = benchLib.TranslationGap,
    date = "2026-08-10",
    note = "Isabelle's polymorphic additive type class has no " ^
           "type-for-type HOL4 carrier"}]

fun run level =
  benchLib.run_family
    {family = "sets", goals = goals, shortfalls = shortfalls,
     budget = benchLib.default_budget,
     battery = [benchLib.Blast, benchLib.Aesop], level = level}

end
