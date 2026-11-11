(* Opt-in final original Goal transport for genuine checked Value packets.
   The ordinary methods are those of Z3_SparseOwnedValueProofReplay, with
   their own invocation/preparation/completion types. *)
signature Z3_OwnedValueProofReplay =
sig
  include Z3_SparseOwnedValueProofReplay
  (* Explicit individual-Hyp Source realization. The ordinary
     methods above retain their original static backend. *)
  structure Sparse : Z3_SparseOwnedValueProofReplay
end
