(* Fixed actual num_transfer_rewrites; no arbitrary theorem/rule input. *)
signature SmtLib_GraphNumericRewriteCatalogue =
sig
  type owner
  type plan
  type catalogue
  val begin : SmtReplayInvocationWork.portfolio ->
    {check_type : Type.hol_type -> unit} -> owner
  val prepare : owner -> plan
  val execute : plan -> catalogue
  (* Metadata validation is allowed in an already-owned Work action. *)
  val validate_for : SmtReplayInvocationWork.portfolio -> catalogue -> unit
  val originals : catalogue -> Thm.thm list
  val checked_rules : catalogue -> SmtReplayProof.closed_fact list
  type policy_owner
  type policy_plan
  type policy_catalogue
  val begin_with_policy : SmtReplayInvocationWork.portfolio ->
    {check_type:Type.hol_type->unit,
     native_contract:SmtReplayNativeContract.contract} -> policy_owner
  val prepare_with_policy : policy_owner -> policy_plan
  val execute_with_policy : policy_plan -> policy_catalogue
  val validate_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_catalogue -> unit
  val originals_with_policy : policy_catalogue -> Thm.thm list
  val checked_rules_with_policy : policy_catalogue ->
    SmtReplayProof.closed_fact list
  val native_contract_for : SmtReplayInvocationWork.portfolio ->
    policy_catalogue -> SmtReplayNativeContract.contract

end
