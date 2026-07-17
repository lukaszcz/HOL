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

  type step_record
  type step = node * goalpos -> (step_record * node) seq.seq

  val kind_of : step_record -> step_kind
  val target_of : step_record -> goalpos
  val consumed_of : step_record -> int option
  val eigenvariables_of : step_record -> string list
  val validation_of : step_record -> validation

  val safe_step : clasetLib.claset -> step
  val clarify_step : clasetLib.claset -> step
end
