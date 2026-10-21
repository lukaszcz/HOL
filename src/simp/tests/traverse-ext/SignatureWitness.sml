(* Apply the TASK_08 signature to the actual installed engine, not a stub. *)
functor TraverseExtSignatureWitness (T : Task08TraverseExt) =
struct
  val lift = T.lift
end

structure SignatureWitness = TraverseExtSignatureWitness (TraverseExt)
