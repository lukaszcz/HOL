Theory sortingAutoSeed
Ancestors
  sorting
Libs
  clasetLib clasimpLib

fun export_iff (name, theorem) =
  let
    val saved = save_thm (name, theorem)
  in
    ThmAttribute.store_at_attribute
      {name = name, attrname = "iff", args = [], thm = saved}
  end

val sintro_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE}
val intro_spec =
  {kind = clasetRules.Intro, safe = false, prio = NONE}
val dest_spec =
  {kind = clasetRules.Dest, safe = false, prio = NONE}
val forward_spec =
  {kind = clasetRules.Forward, safe = false, prio = SOME 10}

(* src/HOL/List.thy:5900-6433 @ f7e02b7e. *)
val _ =
  List.app export_iff
    [("SORTED_EQ_AUTO", sortingTheory.SORTED_EQ),
     ("SORTED_APPEND_AUTO", sortingTheory.SORTED_APPEND),
     ("PERM_NIL_1_AUTO",
      GEN_ALL (CONJUNCT1 (SPEC_ALL sortingTheory.PERM_NIL))),
     ("PERM_NIL_2_AUTO",
      GEN_ALL (CONJUNCT2 (SPEC_ALL sortingTheory.PERM_NIL))),
     ("PERM_SING_1_AUTO",
      GEN_ALL (CONJUNCT1 (SPEC_ALL sortingTheory.PERM_SING))),
     ("PERM_SING_2_AUTO",
      GEN_ALL (CONJUNCT2 (SPEC_ALL sortingTheory.PERM_SING))),
     ("PERM_CONS_IFF_AUTO", sortingTheory.PERM_CONS_IFF),
     ("PERM_APPEND_IFF_1_AUTO",
      GEN_ALL (CONJUNCT1 (SPEC_ALL sortingTheory.PERM_APPEND_IFF))),
     ("PERM_APPEND_IFF_2_AUTO",
      GEN_ALL (CONJUNCT2 (SPEC_ALL sortingTheory.PERM_APPEND_IFF)))]

val _ =
  List.app (clasetLib.export_rule sintro_spec)
    ["sorting.SORTED_NIL", "sorting.SORTED_SING",
     "sorting.PERM_REFL"]

val _ =
  List.app (clasetLib.export_rule intro_spec)
    ["sorting.SORTED_FILTER", "sorting.QSORT_SORTED",
     "sorting.QSORT_PERM"]

val _ = clasetLib.export_rule dest_spec "sorting.SORTED_TL"

val _ =
  List.app (clasetLib.export_rule forward_spec)
    ["sorting.SORTED_ALL_DISTINCT", "sorting.PERM_TRANS",
     "sorting.MEM_PERM", "sorting.PERM_EVERY",
     "sorting.ALL_DISTINCT_PERM", "sorting.SORTED_PERM_EQ"]
