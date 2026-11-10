signature CPC_NativePrivateClosure =
sig
  datatype continuation = MissingAssignment | MissingNativeWitness
    | BinderAdapter | ScopedCommandAdapter | UnsupportedCommand
    | UnresolvedCycle | TemplateAdapter
  type statistics =
    {occurrences : int,assignments : int,native_witnesses : int,
     selected : int list,graph_nodes : int,captured_occurrences : int,
     proof_counts : (int * int) list}
  datatype outcome = Checked of
    {theorem : Thm.thm,contradiction : Thm.thm,statistics : statistics}
    | Continue of continuation
  (* Exact actual parser inventory; no raw source/hypotheses are supplied.
     Native REFL/contra recipes select the real DAG. Every private TRUST
     occurrence needs an independent recorded native witness after Resolve.
     Original Sources are mandatory; assignment equations are temporary
     explicit solver obligations discharged only by the core resolved proof. *)
  val check_packet :
    {packet : CPC_ProofParser.graph_proof SmtLib_GraphProof.packet,
     validate : unit -> unit,sources : SmtReplaySource.sources,
     template_limit : int,dag_limit : int,
     check_type : Type.hol_type -> unit} -> outcome
end
