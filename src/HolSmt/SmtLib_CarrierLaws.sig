(* Root-owned exact stock law preparation; no new Source/Work/caller cap. *)
signature SmtLib_CarrierLaws =
sig
  type owner
  (* Metadata-only owner, retaining existing original G/S/W/root/caps. *)
  val begin : SmtReplayInvocationWork.portfolio ->
    {check_type : Type.hol_type -> unit} -> owner
  (* Lazy needed-law action. On a miss owns one W.with_step; call outside
     another action. Hits and validate are metadata-only, Busy permitted.
     2x2 flags map EXACT NUM/BAG forall/exists theorem pointers. *)
  val get : owner -> {natural : bool,universal : bool} ->
    SmtReplayProof.closed_fact
  val validate : owner -> unit
  type policy_owner
  val begin_with_policy : SmtReplayInvocationWork.portfolio ->
    {check_type:Type.hol_type -> unit} -> policy_owner
  val validate_with_policy : policy_owner -> unit
  val validate_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_owner -> unit
  val get_with_policy : policy_owner -> {natural:bool,universal:bool} ->
    SmtReplayProof.closed_fact
  val get_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_owner -> {natural:bool,universal:bool} ->
    SmtReplayProof.closed_fact

  type native_policy_owner
  val begin_native_with_policy : SmtReplayInvocationWork.portfolio ->
    {native_contract:SmtReplayNativeContract.contract,
     check_type:Type.hol_type -> unit} -> native_policy_owner
  val validate_native_with_policy_for :
    SmtReplayInvocationWork.portfolio -> native_policy_owner -> unit
  val native_contract_with_policy_for :
    SmtReplayInvocationWork.portfolio -> native_policy_owner ->
    SmtReplayNativeContract.contract
  val get_native_with_policy_for : SmtReplayInvocationWork.portfolio ->
    native_policy_owner -> {natural:bool,universal:bool} ->
    SmtReplayProof.closed_fact
end
