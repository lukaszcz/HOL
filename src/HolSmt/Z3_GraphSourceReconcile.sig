(* Copyright (c) 2026 The HOL4 contributors. *)
signature Z3_GraphSourceReconcile =
sig
  type plan
  (* Views must be returned by G.record_opened_view for this original ID
     and scope. Public Source records or closed semantic bridges do not
     establish syntax provenance. Discovery has a separate callback scope. *)
  val prepare : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {sources : SmtReplaySource.sources,
     replay : SmtReplayGraph.node list,
     views : (SmtReplayGraph.node * SmtReplayGraph.source) list,
     admission : {raw_limit : int, binder_limit : int, step_limit : int,
                  check_type : Type.hol_type -> unit}} -> plan
  val sources : plan -> SmtReplayGraph.node list
  val roots : plan -> SmtReplayGraph.node list
  val witness : plan -> int * SmtReplayGraph.node -> Thm.thm option
  (* Closed law witnesses in source occurrence order for unpriced graphs. *)
  val unpriced_witnesses :
    plan -> (SmtReplayGraph.node * Thm.thm) list option
  (* The block's assembler lazily validates on first use. Assemble the
     replay spelling from its original occurrence and a closed beta/eta
     equality; never assume the extra replay Source. *)
  val assemble : plan -> SmtReplayProof.block -> SmtReplayGraph.node ->
    SmtReplayProof.edge
end
