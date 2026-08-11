Theory stringAutoSeed
Ancestors
  string
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

(* src/HOL/String.thy:87-145,429-519 @ f7e02b7e. *)
val _ =
  List.app export_iff
    [("ORD_11_AUTO", stringTheory.ORD_11),
     ("CHR_11_AUTO", stringTheory.CHR_11),
     ("EXPLODE_11_AUTO", stringTheory.EXPLODE_11),
     ("IMPLODE_11_AUTO", stringTheory.IMPLODE_11),
     ("IMPLODE_EQ_EMPTYSTRING_1_AUTO",
      GEN_ALL
        (CONJUNCT1
          (SPEC_ALL stringTheory.IMPLODE_EQ_EMPTYSTRING))),
     ("IMPLODE_EQ_EMPTYSTRING_2_AUTO",
      GEN_ALL
        (CONJUNCT2
          (SPEC_ALL stringTheory.IMPLODE_EQ_EMPTYSTRING))),
     ("EXPLODE_EQ_NIL_1_AUTO",
      GEN_ALL (CONJUNCT1 (SPEC_ALL stringTheory.EXPLODE_EQ_NIL))),
     ("EXPLODE_EQ_NIL_2_AUTO",
      GEN_ALL (CONJUNCT2 (SPEC_ALL stringTheory.EXPLODE_EQ_NIL))),
     ("STRLEN_EQ_0_AUTO", stringTheory.STRLEN_EQ_0),
     ("STRCAT_EQ_EMPTY_AUTO", stringTheory.STRCAT_EQ_EMPTY)]

val _ =
  List.app (clasetLib.export_rule sintro_spec)
    ["string.FINITE_UNIV_char", "string.WF_char_lt"]
