signature clasetStep =
sig
  include Abbrev

  type node = clasetGoal.node
  type goalpos = int

  datatype step_kind =
      Assumption of int
    | Contradiction of int * int
    | ModusPonens of {implication : int, antecedent : int}
    | RuleApplication of {elim : bool, theorem : thm}
    | Disch
    | Gen
    | HypSubst
    | Wrapper

  type created =
    {terms : clasetMeta.meta list, types : clasetMeta.tymeta list}
  type step_record
  type step = node * goalpos -> (step_record * node) seq.seq

  val kind_of : step_record -> step_kind
  val target_of : step_record -> goalpos
  val consumed_of : step_record -> int option
  val created_of : step_record -> created
  val eigenvariables_of : step_record -> string list
  val validation_of : step_record -> validation

  val safe_step : clasetLib.claset -> step
  val clarify_step : clasetLib.claset -> step
  val inst0_step : clasetLib.claset -> step
  val instp_step : clasetLib.claset -> step
  val inst_step : clasetLib.claset -> step
  val unsafe_step : clasetLib.claset -> step
  val dup_step : clasetLib.claset -> step
  val step : clasetLib.claset -> step
  val slow_step : clasetLib.claset -> step

  (* [depth_step cs part m] selects the duplicating or non-duplicating
     unsafe net through [part].  Safe and inst0 inferences cost nothing;
     an instp/part inference costs one unit. *)
  val depth_step : clasetLib.claset -> clasetLib.claset_part -> int -> step
end
