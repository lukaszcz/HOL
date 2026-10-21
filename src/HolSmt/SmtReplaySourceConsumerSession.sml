(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplaySourceConsumerSession :> SmtReplaySourceConsumerSession =
struct
  structure S = SmtReplaySource
  structure W = SmtReplayWrapperSession
  val ERR = Feedback.mk_HOL_ERR "SmtReplaySourceConsumerSession"

  val start = W.start
  val discover = W.discover
  fun prepare sources original preprocessing =
    let
      val session = start sources original
      val _ = discover session (fn _ => preprocessing)
    in session end

  fun run session replay =
    let
      val graph = W.graph session
      val scope = W.scope session
      val sources = W.sources session
      (* Visibility of ancestor sources does not make a child scope their
         owner. Refuse before replay or cleanup can close a borrowed scope. *)
      val _ = if Portable.pointer_eq (graph,S.owning_graph sources)
          andalso scope = S.owning_scope sources then ()
        else raise ERR "run" "session does not own the original Source scope"
      fun finish () =
        let
          val _ = W.begin_replay session
          val theorem = replay graph scope sources (W.preprocessing session)
          val _ = W.accept session theorem
          val _ = W.close session
        in theorem end
    in finish () handle primary =>
      ((W.close session handle _ => ());raise primary) end

  fun prove_cpc_using session
      {proof,ordinary_limit,template_limit,worker,force_worker} =
    run session (fn graph => fn scope => fn sources => fn preprocessing =>
      CPC_GraphProofReplay.prove_preprocessed_using
        {graph = graph,scope = scope,sources = sources,
         preprocessing = preprocessing,proof = proof,
         ordinary_limit = ordinary_limit,template_limit = template_limit,
         worker = worker,force_worker = force_worker})

  fun prove_z3_using session {proof,template_limit,local_law,nnf} =
    run session (fn graph => fn scope => fn sources => fn preprocessing =>
      Z3_GraphProofReplay.check_proof_with_preprocessed_sources_using
        graph scope
        {sources = sources,preprocessing = preprocessing,proof = proof,
         template_limit = template_limit,local_law = local_law,nnf = nnf})
  val discover_with_work = W.discover_with_work
  val _ = CPC_GraphProofReplay.prove_preprocessed_with_work_using
  fun prove_cpc_with_work_using expected session
      {proof,ordinary_limit,template_limit,worker,force_worker} =
    let
      (* The expected pointer comes from the invocation, before old getters
         or cleanup can touch an unrelated held session. *)
      val _ = W.validate_with_work expected session
      val graph = W.graph session val scope = W.scope session
      val sources = W.sources session
      val _ = if Portable.pointer_eq (graph,S.owning_graph sources) andalso
          scope = S.owning_scope sources then () else
        raise ERR "prove_cpc_with_work_using"
          "session does not own original Source scope"
      fun finish () =
        let val _ = W.validate_with_work expected session
            val _ = W.begin_replay session
            val preprocessing = W.preprocessing_with_work expected session
            val theorem =
              CPC_GraphProofReplay.prove_preprocessed_with_work_using
              expected {graph = graph,scope = scope,sources = sources,
                preprocessing = preprocessing,proof = proof,
                ordinary_limit = ordinary_limit,template_limit = template_limit,
                worker = worker,force_worker = force_worker}
            val _ = W.validate_with_work expected session
            val _ = W.accept session theorem
            val _ = W.close session
        in theorem end
    in finish () handle primary =>
      ((W.close session handle _ => ());
       SmtReplayInvocationWork.close expected;raise primary) end

  val _ = CPC_GraphProofReplay.prove_preprocessed_with_clauses_and_work_using
  fun prove_cpc_with_clauses_and_work_using expected session
      {proof,ordinary_limit,template_limit,worker,clause_worker,
       force_worker} =
    let
      (* The expected pointer comes from the invocation, before old getters
         or cleanup can touch an unrelated held session. *)
      val _ = W.validate_with_work expected session
      val graph = W.graph session val scope = W.scope session
      val sources = W.sources session
      val _ = if Portable.pointer_eq (graph,S.owning_graph sources) andalso
          scope = S.owning_scope sources then () else
        raise ERR "prove_cpc_with_clauses_and_work_using"
          "session does not own original Source scope"
      fun finish () =
        let val _ = W.validate_with_work expected session
            val _ = W.begin_replay session
            val preprocessing = W.preprocessing_with_work expected session
            val theorem =
              CPC_GraphProofReplay.prove_preprocessed_with_clauses_and_work_using
              expected {graph = graph,scope = scope,sources = sources,
                preprocessing = preprocessing,proof = proof,
                ordinary_limit = ordinary_limit,template_limit = template_limit,
                worker = worker,clause_worker = clause_worker,
                force_worker = force_worker}
            val _ = W.validate_with_work expected session
            val _ = W.accept session theorem
            val _ = W.close session
        in theorem end
    in finish () handle primary =>
      ((W.close session handle _ => ());
       SmtReplayInvocationWork.close expected;raise primary) end

  val _ =
    Z3_GraphProofReplay.check_proof_with_preprocessed_sources_with_work_using
  fun prove_z3_with_work_using expected session
      {proof,template_limit,local_law,nnf} =
    let
      (* The expected pointer comes from the invocation, before old getters
         or cleanup can touch an unrelated held session. *)
      val _ = W.validate_with_work expected session
      val graph = W.graph session val scope = W.scope session
      val sources = W.sources session
      val _ = if Portable.pointer_eq (graph,S.owning_graph sources) andalso
          scope = S.owning_scope sources then () else
        raise ERR "prove_z3_with_work_using"
          "session does not own original Source scope"
      fun finish () =
        let val _ = W.validate_with_work expected session
            val _ = W.begin_replay session
            val preprocessing = W.preprocessing_with_work expected session
            val theorem =
        Z3_GraphProofReplay.check_proof_with_preprocessed_sources_with_work_using
              expected graph scope {sources = sources,
                preprocessing = preprocessing,proof = proof,
                template_limit = template_limit,local_law = local_law,nnf = nnf}
            val _ = W.validate_with_work expected session
            val _ = W.accept session theorem
            val _ = W.close session
        in theorem end
    in finish () handle primary =>
      ((W.close session handle _ => ());
       SmtReplayInvocationWork.close expected;raise primary) end


  (* Genuine SAME-Work discovery only. Policy replay engines are a separate
     migration boundary; the old finite prove functions are not reused. *)
  val discover_with_policy=W.discover_with_policy

  (* A private sum chooses only these two real checked engines. No public
     callback can supply a theorem or replace the selected programme. *)
  structure PolicyNativeContract=SmtReplayNativeContract
  structure PolicyWork=SmtReplayInvocationWork
  val _=CPC_PolicyGraphProofReplay.prove_with_policy
  val _=Z3_PolicyGraphProofReplay.prove_with_policy
  datatype policy_packet=
      PolicyCpc of CPC_ProofParser.graph_proof SmtLib_GraphProof.packet
    | PolicyZ3 of Z3_GraphProofParser.proof SmtLib_GraphProof.packet

  fun prove_policy_packet expected native session
      {packet,profiles,check_type,ordinal}=
    let
      (* Foreign expected ownership fails before retained session backing
         or cleanup. A refusal closes only the supplied expected Work. *)
      val _=PolicyNativeContract.validate_for expected native
      val _=W.validate_with_policy expected session
      fun finish ()=
        let
          val _=W.begin_replay session
          val preprocessing=W.preprocessing_with_policy expected session
          (* Both engine factories and their GP queries own their actions.
             This boundary creates no enclosing Work.with_step. *)
          val theorem=case packet of
              PolicyCpc actual=>
                CPC_PolicyGraphProofReplay.prove_with_policy expected native
                  {packet=actual,preprocessing=preprocessing,
                   profiles=profiles,check_type=check_type,ordinal=ordinal}
            | PolicyZ3 actual=>
                Z3_PolicyGraphProofReplay.prove_with_policy expected native
                  {packet=actual,preprocessing=preprocessing,
                   profiles=profiles,check_type=check_type,ordinal=ordinal}
          (* The engine has already performed its admitted SourceClose.
             Acceptance checks the exact retained original result live. *)
          val _=PolicyNativeContract.validate_for expected native
          val _=W.validate_with_policy expected session
          val _=W.accept session theorem
          val _=W.close session
        in theorem end
    in finish()handle primary=>
      ((W.close session handle _=>());PolicyWork.close expected;raise primary)
    end

  fun prove_cpc_with_policy expected native session
      {packet,profiles,check_type,ordinal}=
    prove_policy_packet expected native session
      {packet=PolicyCpc packet,profiles=profiles,
       check_type=check_type,ordinal=ordinal}
  fun prove_z3_with_policy expected native session
      {packet,profiles,check_type,ordinal}=
    prove_policy_packet expected native session
      {packet=PolicyZ3 packet,profiles=profiles,
       check_type=check_type,ordinal=ordinal}
end
