(* Candidate pairs are syntax DATA. Only the actual named constructor
   programme may later establish their equality as a proof. *)
signature SmtReplayValueAtomPairs =
sig
  type state
  (* SAME caller-owned action; actual packet/query owner is authenticated
     before any held Value backing. No caller guard or meter is adopted. *)
  val create : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    'proof SmtLib_GraphValueProof.packet -> state
  val demand : SmtReplayInvocationWork.portfolio -> state ->
    SmtLib_GraphParserValue.proof_term *
    SmtLib_GraphParserValue.proof_term -> bool
  val pairs_for : SmtReplayInvocationWork.portfolio -> state ->
    (SmtLib_GraphParserValue.proof_term *
     SmtLib_GraphParserValue.proof_term) list
  val demand_xor : SmtReplayInvocationWork.portfolio -> state ->
    SmtLib_GraphParserValue.proof_term -> unit
  val xors_for : SmtReplayInvocationWork.portfolio -> state ->
    SmtLib_GraphParserValue.proof_term list
end
