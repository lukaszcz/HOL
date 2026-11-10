(* Proof-native local Gamma evidence. No arbitrary theorem constructor. *)
signature SmtLib_OwnedLocalContextProof =
sig
  type owner
  type proof
  val begin : SmtReplayInvocationWork.portfolio ->
    {catalogue:SmtLib_OwnedLocalContextRules.catalogue,
     check_type:Type.hol_type -> unit} -> owner
  val assumption : owner -> int -> proof
  (* New local Gamma' slot ONLY from a completed SAME-context derivation;
     close_goal restores these hypotheses in reverse issuance order. *)
  val assume_derived : owner -> proof -> proof
  val truth : owner -> proof
  (* The first condition is this rule's authentic original assumption.
     Remaining conditions are proved by SAME-owner local proofs. *)
  val apply : owner ->
    {instance:SmtLib_LocalContextRuleMatch.instance,
     conditions:proof list} -> proof
  val rewrite : owner ->
    {equality:proof,premise:proof,reverse:bool} -> proof
  (* Explicit Gamma' to Gamma hypothesis transport; the conclusion and
     remaining actual hypotheses are retained, never made PURE facts. *)
  val replace_hyp : owner -> {hypothesis:proof,premise:proof} -> proof
  val conjunct : owner -> {premise:proof,left:bool} -> proof
  val describe_for : SmtReplayInvocationWork.portfolio -> proof ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     conclusion:Term.term,hypotheses:Term.term list}
  (* Closed conditional seed, actual original Gamma edges, old denial,
     then the existing authentic Q receiver (GEN/DISCH/CHOOSE). *)
  val close_goal : owner -> proof -> Thm.thm
end
