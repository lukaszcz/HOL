signature SmtLib_OwnedBoundedScalarGen =
sig
  type plan
  type result
  val prepare : SmtReplayInvocationWork.portfolio ->
    SmtLib_OwnedConditionalPredicate.completed -> plan
  val plan_for : SmtReplayInvocationWork.portfolio -> plan ->
    {variable:Term.term,input:Term.term,original_hypothesis:Term.term,
     normalized_hypothesis:Term.term,statement:Term.term,
     types:Type.hol_type list,input_tag:Tag.tag,
     native_calls:int,subtotal:IntInf.int}
  val admit : SmtReplayInvocationWork.portfolio ->
    {plan:plan,check_type:Type.hol_type -> unit} -> unit
  val execute : SmtReplayInvocationWork.portfolio -> plan -> result
  val result_for : SmtReplayInvocationWork.portfolio -> result ->
    {statement:Term.term,hypotheses:Term.term list,
     tag:Tag.tag,native_calls:int}
end
