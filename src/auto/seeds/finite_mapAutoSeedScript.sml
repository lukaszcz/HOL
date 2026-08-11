Theory finite_mapAutoSeed
Ancestors
  finite_map
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

(* src/HOL/Map.thy:354-396,565-575,854-931 @ f7e02b7e.
   Isabelle map addition is right-biased, whereas FUNION is left-biased. *)
Theorem FMAP_AUTO_FUNION_SOME[iff]:
  FLOOKUP (FUNION n m) k = SOME x <=>
  FLOOKUP n k = SOME x \/
  FLOOKUP n k = NONE /\ FLOOKUP m k = SOME x
Proof
  Cases_on `FLOOKUP n k` >>
  simp [finite_mapTheory.FLOOKUP_FUNION]
QED

Theorem FMAP_AUTO_FUNION_NONE[iff]:
  FLOOKUP (FUNION n m) k = NONE <=>
  FLOOKUP n k = NONE /\ FLOOKUP m k = NONE
Proof
  Cases_on `FLOOKUP n k` >>
  simp [finite_mapTheory.FLOOKUP_FUNION]
QED

Theorem FMAP_AUTO_FLOOKUP_DOM[iff]:
  k IN FDOM f <=> FLOOKUP f k <> NONE
Proof
  simp [finite_mapTheory.FLOOKUP_DEF]
QED

val _ =
  List.app export_iff
    [("FDOM_EQ_EMPTY_AUTO", finite_mapTheory.FDOM_EQ_EMPTY),
     ("FDOM_EQ_EMPTY_SYM_AUTO",
      finite_mapTheory.FDOM_EQ_EMPTY_SYM),
     ("FEMPTY_SUBMAP_AUTO", finite_mapTheory.FEMPTY_SUBMAP),
     ("SUBMAP_ANTISYM_AUTO", finite_mapTheory.SUBMAP_ANTISYM)]

val _ =
  List.app (clasetLib.export_rule sintro_spec)
    ["finite_map.SUBMAP_FEMPTY", "finite_map.SUBMAP_REFL"]

val _ =
  clasetLib.export_rule
    {kind = clasetRules.Forward, safe = false, prio = SOME 10}
    "finite_map.SUBMAP_TRANS"
