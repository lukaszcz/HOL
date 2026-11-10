(* Fixed-catalogue conditional canonicalization; not a normalizer callback. *)
signature SmtLib_GraphNumericCanonical =
sig
  type owner
  type plan
  type catalogue
  val begin : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphNumericRewriteCatalogue.catalogue ->
    {check_type : Type.hol_type -> unit} -> owner
  val prepare : owner -> plan
  val execute : plan -> catalogue
  val validate_for : SmtReplayInvocationWork.portfolio -> catalogue -> unit
  val originals : catalogue -> Thm.thm list
  val checked_rules : catalogue -> SmtReplayProof.closed_fact list
  (* Original stock row and its exact theorem remain distinct from the
     derived ordered conditional clauses. No Source occurrence is invented. *)
  val origins : catalogue -> (int * Thm.thm) list
  type policy_owner
  type policy_plan
  type policy_catalogue
  val begin_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphNumericRewriteCatalogue.policy_catalogue ->
    {check_type : Type.hol_type -> unit} -> policy_owner
  val prepare_with_policy : policy_owner -> policy_plan
  val execute_with_policy : policy_plan -> policy_catalogue
  val validate_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_catalogue -> unit
  val originals_with_policy : policy_catalogue -> Thm.thm list
  val checked_rules_with_policy : policy_catalogue ->
    SmtReplayProof.closed_fact list
  (* Original stock row and its exact theorem remain distinct from the
     derived ordered conditional clauses. No Source occurrence is invented. *)
  val origins_with_policy : policy_catalogue -> (int * Thm.thm) list
  val native_contract_for : SmtReplayInvocationWork.portfolio ->
    policy_catalogue -> SmtReplayNativeContract.contract

end
