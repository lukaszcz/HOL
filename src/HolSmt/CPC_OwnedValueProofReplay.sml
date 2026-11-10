(* Actual CPC named Value edge through the SAME Source/Goal finalizer. *)
structure CPC_OwnedValueProofReplay :> CPC_OwnedValueProofReplay =
struct
  structure Input =
  struct
    structure Receiver=CPC_OwnedValueNamedReplay
    structure C=CPC_ProofParser
    type proof=CPC_GraphValueProofParser.proof
    type id=string
    type invocation=Receiver.invocation
    type requirement=Receiver.requirement
    type mode=unit
    datatype preparation=datatype Receiver.preparation
    val error=Feedback.mk_HOL_ERR "CPC_OwnedValueProofReplay"
    fun root expected (proof:proof)=
      let
        (* 14 owner fields, Invocation/ref/option/preparation publication,
           adoption/held refs, and final command ID projection. This new
           adapter pays its metadata before the receiver can freeze names. *)
        val _=SmtReplayInvocationWork.spend_policy expected 22
        fun last []=raise error "prepare" "empty actual CPC queue"
            | last [command]=
                (SmtReplayInvocationWork.spend_policy expected 1;command)
            | last (_::rest)=
                (SmtReplayInvocationWork.spend_policy expected 1;last rest)
      in case last(#commands proof)of
          C.GraphAssume(id,_)=>id
        | C.GraphAssumePush(id,_)=>id
        | C.GraphStep{step,...}=> #id step
      end
    fun prepare () expected query packet
        {assertions,native_contract,profiles,check_type}=
      Receiver.prepare_with_policy expected query packet
        {assertions=assertions,native_contract=native_contract,
         check_type=check_type}
    fun realization_profiles () profiles=SOME profiles
    val replay_next_with_policy=Receiver.replay_next_with_policy
    val step_with_policy_for=Receiver.step_with_policy_for
    val close=Receiver.close
  end
  structure Engine=SmtReplayValueFinalFn(Input)
  open Engine
  fun prepare_with_policy expected query packet options=
    Engine.prepare () expected query packet options
  (* Static opt-in instance; exactly the same private Input and
     complete Final worker, with authentic sparse Source closure. *)
  structure Sparse :> CPC_SparseOwnedValueProofReplay =
  struct
    structure Engine=SmtReplayValueFinalUsingFn
      (structure Input=Input
       structure Realization=SmtReplaySparseValueRealization)
    open Engine
    fun prepare_with_policy expected query packet options=
      Engine.prepare () expected query packet options
  end
end
