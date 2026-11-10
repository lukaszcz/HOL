(* No conversion, Source or invocation permission is issued here. *)
signature SmtLib_GraphNumericStock =
sig
  type selection
  val select : Term.term -> selection
  val selection_data : selection -> {head : Term.term,laws : Thm.thm list}
  val for_head : Term.term -> Thm.thm list
  val rewrites : Thm.thm list
  (* Shared old helper values; initialization occurs once, not per producer. *)
  val exp_one_rewrites : Thm.thm list
  val INT_EXP_1 : Thm.thm
  val INT_EXP_BASE_1 : Thm.thm
  val INT_EXP_2 : Thm.thm
  val INT_EXP_3 : Thm.thm
  val select_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayNativeContract.contract -> Term.term -> selection
end
