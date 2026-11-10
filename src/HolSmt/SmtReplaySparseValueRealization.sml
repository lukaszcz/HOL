(* Static sparse specialization of the SAME entire realization programme.
   The anonymous backend cannot be supplied or replaced by a caller. *)
structure SmtReplaySparseValueRealization :>
    SmtReplaySparseValueRealization =
  SmtReplayValueRealizationFn
    (struct
       structure P=SmtReplayProof
       structure GP=SmtLib_GraphPreprocess
       structure W=SmtReplayInvocationWork
       type block=P.policy_sparse_block
       type edge=P.policy_sparse_edge
       type freeze_plan=P.policy_sparse_freeze_plan
       type batch=P.policy_sparse_realization_batch
       type receipt=P.policy_sparse_result
       datatype requirement=datatype SmtReplayValueRealization.requirement
       (* All calls below run in the same owning phase/action as the
          ordinary static backend. There is no raw theorem intake. *)
       fun prepare_freeze expected
           {tables,contract,profiles,ordinal,check_type}=
         let
           (* Four forwarded fields and the actual request record. The
              original common worker still performs its ordinal query;
              this individual-Hyp programme needs no wide Context role. *)
           val _=W.spend_policy expected 5
         in P.prepare_policy_sparse_freeze_with_profiles expected
           {tables=tables,contract=contract,profiles=profiles,
            check_type=check_type}end
       val execute_freeze=P.execute_policy_sparse_freeze
       val owner_for=P.policy_sparse_owner_for
       val sources=P.policy_sparse_sources_for
       val source=P.policy_sparse_source_for
       val assembler=GP.assembler_sparse_with_policy
       fun prepare_batch expected block requests=
         let
           val _=W.spend_policy expected 1
           fun convert []=(W.spend_policy expected 1;[])
             | convert((target,edge)::rest)=
                 (W.spend_policy expected 5;
                  {target=target,edge=edge}::convert rest)
         in P.prepare_policy_sparse_realization_batch expected
           block(convert requests)end
       val execute_batch=P.execute_policy_sparse_realization_batch
       fun receipt_theorem expected receipt=
         let val data=P.policy_sparse_result_for expected receipt
             (* The opaque getter has already fenced actual Work and
                backing; this is the actual new field observation. *)
             val _=W.spend_policy expected 1
         in #theorem data end
     end)
