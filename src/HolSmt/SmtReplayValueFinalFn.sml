(* Typed genuine named receiver hooks; no Source or theorem cast. *)
signature SmtReplayValueFinalInput =
sig
  type proof
  type id
  type invocation
  type requirement
  type mode
  datatype preparation=Prepared of invocation | Needs of requirement list
  val error : string -> string -> exn
  val root : SmtReplayInvocationWork.portfolio -> proof -> id
  val prepare : mode -> SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  val realization_profiles : mode ->
    SmtReplayGraph.policy_opaque_profile list ->
    SmtReplayGraph.policy_opaque_profile list option
  val replay_next_with_policy : SmtReplayInvocationWork.portfolio ->
    invocation -> {id:id,node:SmtLib_GraphParserValue.value} option
  val step_with_policy_for : SmtReplayInvocationWork.portfolio ->
    invocation -> id -> {block:SmtReplayOwnedValueProof.block,
      node:SmtLib_GraphParserValue.value,edge:SmtReplayOwnedValueProof.edge}
  val close : invocation -> unit
end

(* One genuine named edge -> original Sources -> exact public Goal. *)
signature SmtReplayValueFinal =
sig
  type proof
  type requirement
  type mode
  type invocation
  datatype preparation=Prepared of invocation
    | ReplayNeeds of requirement list
  datatype completion=Proved of
      {theorem:Thm.thm,
       dependencies:SmtReplayOwnedValueProof.source_lineage list}
    | RealizationNeeds of SmtReplayValueRealization.requirement list
  (* Outside an action. Actual Work/query/packet headers precede adoption.
     ReplayNeeds retains caller packet ownership. No Source is fabricated. *)
  val prepare : mode -> SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  (* Outside an action, once only. Genuine RealizationNeeds retains the
     live invocation until close. Success returns exact original Goal and
     allowed canonical Source hypotheses, then closes receiver and packet. *)
  val finish_with_policy : SmtReplayInvocationWork.portfolio ->
    invocation -> completion
  val close : invocation -> unit
end

(* SAME owned Value edge, Source realization and exact Goal programme. *)
functor SmtReplayValueFinalUsingFn
  (structure Input:SmtReplayValueFinalInput
   structure Realization:SmtReplayValueRealization
     where type requirement=SmtReplayValueRealization.requirement) :>
    SmtReplayValueFinal
      where type proof=Input.proof
      and type requirement=Input.requirement
      and type mode=Input.mode =
struct
  structure W=SmtReplayInvocationWork
  structure G=SmtReplayGraph
  structure S=SmtReplaySource
  structure NC=SmtReplayNativeContract
  structure Scope=SmtReplayOwnedScopeReceipt
  structure GP=SmtLib_GraphPreprocess
  structure VP=SmtLib_GraphValueProof
  structure PV=SmtLib_GraphParserValue
  structure Value=SmtReplayOwnedValueProof
  structure Real=Realization
  structure Goal=SmtReplayGoalClose
  structure N=SmtReplayNamedContext
  type proof=Input.proof
  type requirement=Input.requirement
  type mode=Input.mode
  val ERR=Input.error
  datatype phase=Ready|Running|Pending|Complete|Closed
  datatype invocation=Invocation of
    {work:W.portfolio,query:GP.graph_query,packet:Input.proof VP.packet,
     receiver:Input.invocation,contract:NC.contract,
     graph:G.graph,scope:G.scope,sources:S.sources,frame:Scope.receipt,
     root:Input.id,profiles:G.policy_opaque_profile list,
     realization_profiles:G.policy_opaque_profile list option,
     check_type:Type.hol_type -> unit,phase:phase ref}
  datatype preparation=Prepared of invocation
    | ReplayNeeds of Input.requirement list
  datatype completion=Proved of
      {theorem:Thm.thm,dependencies:Value.source_lineage list}
    | RealizationNeeds of Real.requirement list
  (* Passive opt-in snapshots only. Never toggle counters, activate a
     held owner or replace the proof operation's primary exception. *)
  fun native_phase expected label=
    ((if OS.Process.getEnv "HOL4_HOLSMT_REPLAY_DIAGNOSTICS"<>SOME "1"
      then ()else
      let val counts=Count.thm_count()
          val audit=W.audit_policy expected
      in TextIO.output(TextIO.stdErr,
        "VALUE_FINAL_NATIVE phase=" ^ label ^
        " charged=" ^ IntInf.toString(#charged audit) ^
        " ABS=" ^ Int.toString(#ABS counts) ^
        " AP_TERM=" ^ Int.toString(#AP_TERM counts) ^
        " AP_THM=" ^ Int.toString(#AP_THM counts) ^
        " MK_COMB=" ^ Int.toString(#MK_COMB counts) ^
        " ASSUME=" ^ Int.toString(#ASSUME counts) ^
        " INST=" ^ Int.toString(#INST counts) ^ "\n");
        TextIO.flushOut TextIO.stdErr
      end)handle _=>())
  fun header expected (Invocation{work,...})=
    if Portable.pointer_eq(expected,work)then ()else
      raise ERR "owner" "different original Work"
  fun live expected
      (owner as Invocation{query,packet,contract,phase,...})=
    (header expected owner;
     if !phase=Closed then raise ERR "owner" "invocation closed"else ();
     GP.validate_query_with_policy expected query;
     NC.validate_for expected contract;
     ignore(VP.contents_with_policy_for expected query packet))
  fun close (Invocation{receiver,packet,phase,...})=
    if !phase=Closed then ()else
      let val _=phase:=Closed
          val first=Exn.capture Input.close receiver
          val second=Exn.capture VP.close packet
      in case first of Exn.Exn primary=>raise primary
        | Exn.Res ()=>Exn.release second end
  fun protect expected owner action=action()handle primary=>
    (ignore(Exn.capture close owner);W.close expected;raise primary)
  fun prepare mode expected query packet
      {assertions,native_contract,profiles,check_type}=
    let
      (* Cleanup cannot touch a foreign held packet before its real owner
         has passed the actual packet header/query validator. *)
      val adopted=ref false
      val held=ref(NONE:Input.invocation option)
      fun run()=
        let
          val current=GP.query_nodes_with_policy_for expected query
          val sources=W.original_sources expected
          val graph=S.owning_graph sources
          val scope=S.owning_scope sources
          val _=if Portable.pointer_eq(#sources current,sources)andalso
              Portable.pointer_eq(#graph current,graph)andalso
              #scope current=scope then ()else
            raise ERR "prepare" "different actual original Source frame"
          val _=NC.validate_for expected native_contract
          val root=W.with_step expected(fn()=>
            let val data=VP.contents_with_policy_for expected query packet
                val _=W.spend_policy expected 1
                val _=adopted:=true
            in Input.root expected(#proof data)end)
          val prepared=Input.prepare mode expected query packet
            {assertions=assertions,native_contract=native_contract,
             profiles=profiles,check_type=check_type}
        in case prepared of Input.Needs needs=>
                ReplayNeeds needs
          | Input.Prepared receiver=>
              let val _=held:=SOME receiver
                  val frame=Scope.root_with_policy expected
                  val owner=Invocation
                    {work=expected,query=query,packet=packet,
                     receiver=receiver,contract=native_contract,
                     graph=graph,scope=scope,sources=sources,frame=frame,
                     root=root,profiles=profiles,check_type=check_type,
                     realization_profiles=Input.realization_profiles
                       mode profiles,
                     phase=ref Ready}
                  val _=W.with_step expected(fn()=>live expected owner)
              in Prepared owner end
        end
    in run()handle primary=>
      (ignore(Exn.capture(fn()=>Option.app Input.close(!held))());
       if !adopted then ignore(Exn.capture VP.close packet)else ();
       W.close expected;raise primary)
    end
  fun finish_with_policy expected owner=
    ((header expected owner;
      protect expected owner(fn()=>
      let
        val Invocation{query,packet,receiver,contract,graph,scope,sources,
          frame,
          root,profiles,realization_profiles,check_type,phase,...}=owner
        val _=W.with_step expected(fn()=>
          (live expected owner;W.spend_policy expected 1;
           if !phase=Ready then phase:=Running else
             raise ERR "finish" "unfinished or consumed invocation"))
        fun guard()=live expected owner
        fun checked ty=(guard();check_type ty;guard())
        fun replay()=
          case Input.replay_next_with_policy expected receiver of
              NONE=>()|SOME _=>replay()
        val _=native_phase expected "finish.before-replay"
        val _=replay()
        val _=native_phase expected "finish.after-replay"
        val final=Input.step_with_policy_for expected receiver root
        val input=W.with_step expected(fn()=>
          let val _=guard()
              val data=VP.contents_with_policy_for expected query packet
              val context= #context data
              val _=W.spend_policy expected 1
              val _=case PV.proof_view context
                  (PV.proof_term context (#node final))of
                  PV.ProofConstant atom=>
                    if Term.same_const atom boolSyntax.F then ()else
                      raise ERR "finish" "actual final node is not false"
                | _=>raise ERR "finish" "actual final node is not false"
          in Value.realization_input_for expected
            (#block final)(#edge final)end)
        val preparation=case realization_profiles of
            NONE=>Real.prepare expected input {check_type=checked}
          | SOME profiles=>Real.prepare_with_profiles expected input
              {profiles=profiles,check_type=checked}
        val _=native_phase expected "finish.after-realization-prepare"
      in case preparation of
          Real.Needs needs=>
            (W.with_step expected(fn()=>
              (guard();W.spend_policy expected 1;phase:=Pending));
             RealizationNeeds needs)
        | Real.Prepared planned=>
          let
            val realized=Real.execute expected planned
            val _=native_phase expected "finish.after-realization-execute"
            (* Only this genuine sealed result enters the shared closing
               programme. There is no raw theorem or caller receipt port. *)
            fun original()=
              (guard();ignore(Real.contradiction_for expected realized))
            val result=W.with_step expected(fn()=>
              let
                val proof=Real.contradiction_for expected realized
                val _=W.spend_policy expected 0
                val native=NC.for_work expected contract
                val current=W.original_sources expected
                val actual_graph=S.owning_graph current
                val actual_scope=S.owning_scope current
                val _=if Portable.pointer_eq(current,sources)andalso
                    Portable.pointer_eq(actual_graph,graph)andalso
                    actual_scope=scope then ()else
                  raise ERR "finish" "actual original Source frame changed"
                val data=Scope.description_with_policy_for expected frame
                val _=if Portable.pointer_eq(#graph data,graph)andalso
                    #scope data=scope andalso
                    Portable.pointer_eq(#sources data,sources)then ()else
                  raise ERR "finish" "actual Goal frame changed"
                val plan=Goal.prepare
                  {work=expected,contract=contract,native=native,
                   sources=sources,graph=graph,scope=scope,frame=frame,
                   proof=proof,guard=original,profiles=profiles,
                   check_type=checked,error=ERR "source_close",
                   type_weight=fn ceiling=>N.type_weight_using
                     (W.spend_policy expected)(ERR "native")ceiling,
                   counter=Goal.type_counter
                     (fn()=>ERR "native" "unfinished Type child")}
                val _=native_phase expected "finish.after-goal-prepare"
                val theorem=Goal.execute expected plan
                val _=native_phase expected "finish.after-goal-execute"
                val dependencies=Real.source_dependencies_for
                  expected realized
                val _=guard()
                val _=W.spend_policy expected 1
                val _=phase:=Complete
              in Proved{theorem=theorem,dependencies=dependencies}end)
            val _=close owner
          in result end
      end))handle primary=>(W.close expected;raise primary))
end

(* Static ordinary specialization; no mode branch or per-call adapter. *)
functor SmtReplayValueFinalFn (Input:SmtReplayValueFinalInput) =
  SmtReplayValueFinalUsingFn
    (structure Input=Input
     structure Realization=SmtReplayValueRealization)
