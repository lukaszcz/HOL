Theory optionAutoSeed
Ancestors
  option
Libs
  clasetLib clasimpLib

(* src/HOL/Option.thy:33-36 @ f7e02b7e.  [not_None_eq] is declared [iff]
   there.  Its left side reads an arbitrary option through a constructor,
   so under HOL4's outermost-first traversal it would fire above every
   rule about the subject's own head; Isabelle's innermost-first order
   never offers it a subject that is not already normal.  [iff_bottom_up]
   is [iff] with the rewrite in the reducer the traversal reaches last,
   which is that order. *)
Theorem OPTION_NOT_NONE_EXISTS[iff_bottom_up]:
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
