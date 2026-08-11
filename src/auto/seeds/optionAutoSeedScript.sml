Theory optionAutoSeed
Ancestors
  option
Libs
  clasetLib clasimpLib

(* src/HOL/Option.thy:33-36 @ f7e02b7e *)
Theorem OPTION_NOT_NONE_EXISTS[iff]:
  !x. x <> NONE <=> ?y. x = SOME y
Proof
  Cases_on `x` >> simp []
QED

Theorem OPTION_ALL_NOT_SOME[iff]:
  !x. (!y. x <> SOME y) <=> x = NONE
Proof
  Cases_on `x` >> simp []
QED

fun export_iff (name, theorem) =
  let
    val saved = save_thm (name, theorem)
  in
    ThmAttribute.store_at_attribute
      {name = name, attrname = "iff", args = [], thm = saved}
  end

(* src/HOL/Option.thy:105-111 @ f7e02b7e *)
val _ =
  List.app export_iff
    [("OPTION_MAP_EQ_NONE_AUTO",
      CONJUNCT1 optionTheory.OPTION_MAP_EQ_NONE_both_ways),
     ("NONE_EQ_OPTION_MAP_AUTO",
      CONJUNCT2 optionTheory.OPTION_MAP_EQ_NONE_both_ways),
     ("OPTION_MAP_EQ_SOME_AUTO", optionTheory.OPTION_MAP_EQ_SOME)]
