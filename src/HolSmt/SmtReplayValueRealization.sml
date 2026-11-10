(* Static ordinary Source specialization of the SAME complete programme. *)
structure SmtReplayValueRealization :> SmtReplayValueRealization =
  SmtReplayValueRealizationFn
    (struct
       structure P=SmtReplayProof
       structure GP=SmtLib_GraphPreprocess
       structure PV=SmtLib_GraphParserValue
       structure G=SmtReplayGraph
       type block=P.block
       type edge=P.edge
       type freeze_plan=P.policy_native_freeze_plan
       type batch=P.policy_realization_batch
       type receipt=P.policy_source_realization
       datatype requirement = ScopedBinderProgramme of PV.proof_term
         | SourceCorrespondence of {value:PV.proof_term,node:G.node}
       val prepare_freeze=P.prepare_native_realization_freeze_with_policy
       val execute_freeze=P.freeze_owned_realization_tables_with_policy
       val owner_for=P.policy_native_block_owner_for
       fun sources _ block=P.sources block
       fun source _ block index=P.source block index
       val assembler=GP.assembler_with_policy
       val prepare_batch=P.prepare_realization_batch_with_policy
       val execute_batch=P.execute_realization_batch_with_policy
       val receipt_theorem=P.policy_source_realization_theorem_for
     end)
