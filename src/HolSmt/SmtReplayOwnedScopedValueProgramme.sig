(* Actual enclosing-packet compilation. This plan is not a scoped result. *)
signature SmtReplayOwnedScopedValueProgramme =
sig
  type plan
  type closed_child
  datatype requirement = NativeOpening of
    SmtLib_GraphParserValue.proof_term
  datatype preparation = Prepared of plan | Needs of requirement list
  (* Outside an action. Captured is the genuine enclosing quant-intro and
     immediate Bind, not a caller rule/frame/body. Compile the entire
     source-free queue with the SAME fixed/equality/Boolean/recorded Clause
     workers. No user Type callback or kernel operation runs here. *)
  val prepare : SmtReplayInvocationWork.portfolio ->
    SmtReplayOwnedScopedValueContext.context -> preparation
  (* Outside an action. Once only, after the entire finite preparation:
     genuine sparse ASSUMEs/shared workers, then the SAME closed-law
     simultaneous INST and actual REFL constructor witnesses. The result
     has empty hypotheses; it grants no parent GEN/ABS or Source rights. *)
  val execute : SmtReplayInvocationWork.portfolio -> plan ->
    {check_type:Type.hol_type -> unit} -> closed_child
  (* Concrete enclosing Binder producer already owns the SAME action.
     The opaque plan and real original Work remain mandatory; this is
     not an action flag, caller proof payload or substituted guard. *)
  val execute_in_action : SmtReplayInvocationWork.portfolio -> plan ->
    {check_type:Type.hol_type -> unit} -> closed_child
  (* SAME action; exact expected Work/packet/child lifetime before held
     proof backing. Only an actual enclosing BinderClose producer may
     consume this child and its real binding frame for generalization. *)
  val closed_child_data_for : SmtReplayInvocationWork.portfolio ->
    closed_child ->
    {context:SmtReplayOwnedScopedValueContext.context,
     binding:SmtLib_GraphValueProof.binding_frame,
     frame:SmtReplayOwnedScopeReceipt.receipt,
     native_contract:SmtReplayNativeContract.contract,
     body:SmtReplayGraph.node,theorem:Thm.thm}
  (* SAME action. Immutable forecast only: no mutable queue or native
     executor escapes the packet-owned plan. Parent binder/ALPHA admission
     remains separate and must precede parent generalization. *)
  val data_for : SmtReplayInvocationWork.portfolio -> plan ->
    {context:SmtReplayOwnedScopedValueContext.context,
     syntax:SmtReplayOwnedScopedValueSyntax.plan,
     conclusion:Term.term,hypotheses:Term.term list,
     assumptions:Term.term list,native_body:SmtReplayGraph.node,
     native_term:Term.term,type_ports:Type.hol_type list}
end
