signature SmtReplayOwnedSourceGeneralizationConsumer =
sig
  (* Consumes only the genuine executed GEN result, never a caller law. *)
  val execute : SmtReplayInvocationWork.portfolio ->
    {generalized:SmtReplayProof.source_generalization,
     check_type:Type.hol_type -> unit} -> SmtReplayProof.source_realization
end
