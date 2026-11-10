(* Same owned finalization programme, with actual Z3 registry modes. *)
structure Z3_OwnedValueProofReplay :> Z3_OwnedValueProofReplay =
struct
  structure Input =
  struct
    structure Receiver=Z3_OwnedValueNamedReplay
    type proof=Z3_GraphValueProofParser.proof
    type id=Z3_GraphProofParser.proof_id
    type invocation=Receiver.invocation
    type requirement=Receiver.requirement
    datatype mode=Recorded | Specialized | Raw | Retained | Binders
      | QuantifiedBinders
      | OwnedProgrammes
    datatype preparation=datatype Receiver.preparation
    val error=Feedback.mk_HOL_ERR "Z3_OwnedValueProofReplay"
    fun root _ (proof:proof)= #root proof
    fun prepare mode expected query packet
        {assertions,native_contract,profiles,check_type}=
      case mode of Raw=>Receiver.prepare_with_raw_resolution_with_policy
          expected query packet
          {assertions=assertions,native_contract=native_contract,
           profiles=profiles,check_type=check_type}
      | QuantifiedBinders=>
          Receiver.prepare_with_quantified_binders_with_policy
            expected query packet
            {assertions=assertions,native_contract=native_contract,
             profiles=profiles,check_type=check_type}
      | Binders=>Receiver.prepare_with_binders_with_policy
          expected query packet
          {assertions=assertions,native_contract=native_contract,
           profiles=profiles,check_type=check_type}
      | Retained=>
          Receiver.prepare_with_retained_specialization_with_policy
            expected query packet
            {assertions=assertions,native_contract=native_contract,
             profiles=profiles,check_type=check_type}
      | Specialized=>Receiver.prepare_with_specialization_with_policy
          expected query packet
          {assertions=assertions,native_contract=native_contract,
           profiles=profiles,check_type=check_type}
      | Recorded=>Receiver.prepare_with_original_sources_with_policy
          expected query packet
          {assertions=assertions,native_contract=native_contract,
           check_type=check_type}
      | OwnedProgrammes=>
          Receiver.prepare_with_owned_programmes_with_policy
            expected query packet
            {assertions=assertions,native_contract=native_contract,
             profiles=profiles,check_type=check_type}
    fun realization_profiles Recorded _=NONE
      | realization_profiles _ profiles=SOME profiles
    val replay_next_with_policy=Receiver.replay_next_with_policy
    val step_with_policy_for=Receiver.step_with_policy_for
    val close=Receiver.close
  end
  structure Engine=SmtReplayValueFinalFn(Input)
  open Engine
  fun prepare_with_policy expected query packet options=
    Engine.prepare Input.Recorded expected query packet options
  fun prepare_with_specialization_with_policy expected query packet options=
    Engine.prepare Input.Specialized expected query packet options
  fun prepare_with_raw_resolution_with_policy expected query packet options=
    Engine.prepare Input.Raw expected query packet options
  fun prepare_with_binders_with_policy expected query packet options=
    Engine.prepare Input.Binders expected query packet options
  fun prepare_with_quantified_binders_with_policy
      expected query packet options=
    Engine.prepare Input.QuantifiedBinders expected query packet options
  fun prepare_with_retained_specialization_with_policy
      expected query packet options=
    Engine.prepare Input.Retained expected query packet options
  fun prepare_with_owned_programmes_with_policy expected query packet options=
    Engine.prepare Input.OwnedProgrammes expected query packet options
  (* Static opt-in instance; exactly the same private Input and
     complete Final worker, with authentic sparse Source closure. *)
  structure Sparse :> Z3_SparseOwnedValueProofReplay =
  struct
    structure Engine=SmtReplayValueFinalUsingFn
      (structure Input=Input
       structure Realization=SmtReplaySparseValueRealization)
    open Engine
    fun prepare_with_policy expected query packet options=
      Engine.prepare Input.Recorded expected query packet options
    fun prepare_with_specialization_with_policy expected query packet options=
      Engine.prepare Input.Specialized expected query packet options
    fun prepare_with_raw_resolution_with_policy expected query packet options=
      Engine.prepare Input.Raw expected query packet options
    fun prepare_with_binders_with_policy expected query packet options=
      Engine.prepare Input.Binders expected query packet options
    fun prepare_with_quantified_binders_with_policy
        expected query packet options=
      Engine.prepare Input.QuantifiedBinders expected query packet options
    fun prepare_with_retained_specialization_with_policy
        expected query packet options=
      Engine.prepare Input.Retained expected query packet options
    fun prepare_with_owned_programmes_with_policy
        expected query packet options=
      Engine.prepare Input.OwnedProgrammes expected query packet options
  end
end
