(* Unprivileged fixed kernel programme; no P receipt is issued.
   Guard, proof, native contract and Source frame come from the owning
   specialization. This module does not authenticate an arbitrary caller
   theorem as a checked graph or Value realization. *)
signature SmtReplayGoalClose =
sig
  type plan
  val type_counter : (unit -> exn) -> unit ->
    Type.hol_type -> IntInf.int
  (* Caller owns the SAME Work action and protects failures. All native
     Type/profile/result/Hyp work is quoted before the closing operations. *)
  val prepare :
    {work:SmtReplayInvocationWork.portfolio,
     contract:SmtReplayNativeContract.contract,
     native:SmtReplayNativeContract.limits,
     sources:SmtReplaySource.sources,graph:SmtReplayGraph.graph,
     scope:SmtReplayGraph.scope,frame:SmtReplayOwnedScopeReceipt.receipt,
     proof:Thm.thm,guard:unit -> unit,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit,error:string -> exn,
     type_weight:IntInf.int -> Type.hol_type -> IntInf.int,
     counter:unit -> Type.hol_type -> IntInf.int} -> plan
  (* Caller owns the SAME action. This returns an ordinary kernel theorem,
     never an opaque Source/Value/P receipt. The plan is consumed once. *)
  val execute : SmtReplayInvocationWork.portfolio -> plan -> Thm.thm
end
