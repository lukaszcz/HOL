(* One genuine named edge -> original Sources -> exact public Goal.
   The ordinary methods are those of CPC_SparseOwnedValueProofReplay, with
   their own invocation/preparation/completion types. *)
signature CPC_OwnedValueProofReplay =
sig
  include CPC_SparseOwnedValueProofReplay
  (* Explicit individual-Hyp Source realization. The ordinary
     methods above retain their original static backend. *)
  structure Sparse : CPC_SparseOwnedValueProofReplay
end
