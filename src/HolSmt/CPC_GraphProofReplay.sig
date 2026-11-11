(* Copyright (c) 2026 The HOL4 contributors. *)
signature CPC_GraphProofReplay =
sig
  exception OwnedEndpointAdapter
  exception NativeCompletionAdapter
  type worker = CPC_Proof.step * CPC_Proof.located_term list ->
    Thm.thm * CPC_Proof.located_term
  type clause_worker = CPC_Proof.step * CPC_Proof.located_term list ->
    {theorem:Thm.thm,located:CPC_Proof.located_term,
     clause:SmtClause.owned_witness option}
  (* Explicit continuation for declaration-generated obligations/patterns;
     no global policy or worker retry is installed. *)
  val prove_admitted_using :
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     sources:SmtReplaySource.sources,
     preprocessing:SmtLib_GraphPreprocess.validation option,
     work:SmtReplayInvocationWork.portfolio option,
     proof:CPC_ProofParser.graph_proof,ordinary_limit:int,template_limit:int,
     worker:(Term.term -> unit) -> worker,
     clause_worker:((Term.term -> unit) -> clause_worker) option,
     force_worker:worker option} -> Thm.thm
  val check_contradiction_admitted_using :
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     sources:SmtReplaySource.sources,
     preprocessing:SmtLib_GraphPreprocess.validation option,
     work:SmtReplayInvocationWork.portfolio option,
     proof:CPC_ProofParser.graph_proof,ordinary_limit:int,template_limit:int,
     worker:(Term.term -> unit) -> worker,
     clause_worker:((Term.term -> unit) -> clause_worker) option,
     force_worker:worker option} -> Thm.thm
  datatype producer_origin_gap = OriginTemplateQuota | OriginHypAlignment
  type producer_origin =
    {serial : int,target : SmtReplayGraph.node,
     equation : SmtReplayGraph.node * SmtReplayGraph.node,
     law_node : SmtReplayGraph.node,law : Thm.thm,
     checked_local_law : Thm.thm,
     premises : {index : int,node : SmtReplayGraph.node,
                 command_occurrence : int option} list,
     actual_hypotheses : int list,
     support_indices : (int * int) list,
     support : SmtReplaySupport.certificate,
     deferred : SmtReplayGraph.node option}
  datatype worker_event =
      CommandBegin of {serial : int,command : CPC_ProofParser.graph_command}
    | CommandEnd of {serial : int,node : SmtReplayGraph.node,
                     provenance : CPC_Proof.term_provenance}
    | CheckedLocalLaw of {serial : int,law : Thm.thm}
    | CheckedProducerOrigin of producer_origin
    | ProducerOriginUnavailable of {serial : int,gap : producer_origin_gap}
    | ForcedBegin of {serial : int,step : CPC_Proof.step}
    | ForcedEnd of {serial : int,theorem : Thm.thm,
                    located : CPC_Proof.located_term}
    | ForcedAbort of {serial : int}
    | InvocationEnd
    | InvocationAbort
  type observer = worker_event -> unit
  type observed_statistics =
    {nodes : SmtReplayGraph.node_statistics,
     proofs : SmtReplayProof.proof_statistics,
     schemas : SmtReplayCanonGraph.schema_statistics,
     assembly_hits : IntInf.int,assembly_misses : IntInf.int}
  val check_contradiction_preprocessed_observed_with_work_using :
    SmtReplayInvocationWork.portfolio ->
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,
     preprocessing : SmtLib_GraphPreprocess.validation,
     proof : CPC_ProofParser.graph_proof,ordinary_limit : int,
     template_limit : int,worker : worker,force_worker : worker option} ->
    {theorem : Thm.thm,statistics : observed_statistics}
  (* Only the actual pending factory callback can validate its private
     singleton-defer lease. This permits a temporary obligation, not a fact. *)
  type direct_deferred_request =
    {serial : int,step : CPC_Proof.step,target : SmtReplayGraph.node,
     theorem : Thm.thm,located : CPC_Proof.located_term,
     hypothesis : Term.term}
  type direct_deferred = direct_deferred_request -> unit option
  type owned_force_request =
    {serial : int,target : SmtReplayGraph.node,step : CPC_Proof.step,
     premises : CPC_Proof.located_term list}
  type owned_force_worker = owned_force_request ->
    Thm.thm * CPC_Proof.located_term
  type completion_request =
    {root : SmtReplayGraph.node,
     mandatory : {serial : int,target : SmtReplayGraph.node} list}
  type completion_result =
    {resolution : SmtReplayResolve.resolution,contradiction : Thm.thm,
     witnesses : {serial : int,original : SmtReplayGraph.node,
       target : SmtReplayGraph.node,witness : Thm.thm} list}
  type completion = completion_request -> completion_result option
  type owned_completion_request =
    {root : SmtReplayGraph.node,
     mandatory : {serial : int,target : SmtReplayGraph.node} list,
     prove : SmtReplayGraph.node -> Thm.thm}
  type owned_completion = owned_completion_request -> completion_result option
  (* A worker sees only operands admitted under the existing ordinary rule
     bound. Its result is closed over the recorded premise occurrences;
     unrelated hypotheses and unclean proof tags are rejected. *)
  val check_contradiction :
    {graph : SmtReplayGraph.graph, scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources, proof : CPC_ProofParser.graph_proof,
     ordinary_limit : int, template_limit : int, worker : worker} -> Thm.thm
  val prove :
    {graph : SmtReplayGraph.graph, scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources, proof : CPC_ProofParser.graph_proof,
     ordinary_limit : int, template_limit : int, worker : worker} -> Thm.thm
  (* Deferred TRUST requires an independent owned-ID fact, or a bounded
     forced checker which cannot defer the obligation a second time. *)
  val check_contradiction_using :
    {graph : SmtReplayGraph.graph, scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources, proof : CPC_ProofParser.graph_proof,
     ordinary_limit : int, template_limit : int, worker : worker,
     force_worker : worker option} -> Thm.thm
  (* Opt-in invocation lifecycle. Node/provenance events carry ownership
     information only; only CheckedLocalLaw carries a checked compact law.
     Old entry points use a no-op observer. Observer failure fails this
     invocation; abort notification never replaces the original exception. *)
  val check_contradiction_observing :
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,proof : CPC_ProofParser.graph_proof,
     ordinary_limit : int,template_limit : int,worker : worker,
     force_worker : worker option,observer : observer} -> Thm.thm
  (* Additive checked history discovery. The original observer API does
     not run this path. An unavailable origin conveys no source authority. *)
  (* Actual selected history closes after capture, while committed leases
     are live, before ordinary completion freezes or forces any obligation.
     NONE preserves the existing completion route. Exceptions remain fatal. *)
  (* The force callback receives the actual owned obligation. Its returned
     theorem still passes every existing independent closure/Source gate. *)
  (* prove is a dynamic callback lease over the same actual persistent
     forced worker and serial counter. It expires on return or exception. *)
  val check_contradiction_owned_proof_completing :
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,proof : CPC_ProofParser.graph_proof,
     ordinary_limit : int,template_limit : int,worker : worker,
     observer : observer,check_type : Type.hol_type -> unit,
     completion : owned_completion,direct_deferred : direct_deferred,
     owned_force_worker : owned_force_worker} -> Thm.thm
  val prove_using :
    {graph : SmtReplayGraph.graph, scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources, proof : CPC_ProofParser.graph_proof,
     ordinary_limit : int, template_limit : int, worker : worker,
     force_worker : worker option} -> Thm.thm
  (* SAME original Source object and graph as opaque preprocessing.
     Actual processed assertions are derived from original compact Sources;
     they do not extend the original permitted Hyp portfolio. *)
  val check_contradiction_preprocessed_using :
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,
     preprocessing : SmtLib_GraphPreprocess.validation,
     proof : CPC_ProofParser.graph_proof,ordinary_limit : int,
     template_limit : int,worker : worker,
     force_worker : worker option} -> Thm.thm
  val prove_preprocessed_using :
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,
     preprocessing : SmtLib_GraphPreprocess.validation,
     proof : CPC_ProofParser.graph_proof,ordinary_limit : int,
     template_limit : int,worker : worker,
     force_worker : worker option} -> Thm.thm
  val check_contradiction_preprocessed_with_work_using :
    SmtReplayInvocationWork.portfolio ->
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,
     preprocessing : SmtLib_GraphPreprocess.validation,
     proof : CPC_ProofParser.graph_proof,ordinary_limit : int,
     template_limit : int,worker : worker,
     force_worker : worker option} -> Thm.thm
  val prove_preprocessed_with_work_using :
    SmtReplayInvocationWork.portfolio ->
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,
     preprocessing : SmtLib_GraphPreprocess.validation,
     proof : CPC_ProofParser.graph_proof,ordinary_limit : int,
     template_limit : int,worker : worker,
     force_worker : worker option} -> Thm.thm
  val prove_preprocessed_with_clauses_and_work_using :
    SmtReplayInvocationWork.portfolio ->
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     sources:SmtReplaySource.sources,
     preprocessing:SmtLib_GraphPreprocess.validation,
     proof:CPC_ProofParser.graph_proof,ordinary_limit:int,
     template_limit:int,worker:worker,clause_worker:clause_worker,
     force_worker:worker option} -> Thm.thm
end
