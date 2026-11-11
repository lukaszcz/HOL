(* Source-only bounded adapter; this interface authorizes no deferred fact. *)
signature CPC_GraphLexicalTransport =
sig
  type plan
  type prepared
  exception Adapter
  val new :
    {packet : 'proof SmtLib_GraphProof.packet,
     sources : SmtReplaySource.sources, validate : unit -> unit,
     ordinary_limit : int, check_type : Type.hol_type -> unit} -> plan
  val prepare : plan ->
    {target : SmtReplayGraph.node, step : CPC_Proof.step,
     premises : CPC_Proof.located_term list} -> prepared
  (* Optional closed-constructor computation budget; no theorem authority. *)
  (* Native proof templates still need exact packet/Source lifetime checks. *)
  val step : prepared -> CPC_Proof.step
  val premises : prepared -> CPC_Proof.located_term list
  (* This transports the caller's actual proof and explicit Hyp; it never
     marks a deferred target independently proved. *)
  val restore : prepared ->
    {theorem : Thm.thm, located : CPC_Proof.located_term} ->
      Thm.thm * CPC_Proof.located_term
end
