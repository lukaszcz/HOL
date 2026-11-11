(* Proposed standalone producer. UNCOMPILED; no legacy selector change. *)
signature SmtLib_GraphLawTypeInstance =
sig
  type producer
  type plan
  type instance
  (* original is an already admitted genuine CLOSED original law plan.
     The SAME immutable P limit is checked, never replaced by a new cutoff.
     Actual original syntax/names are inspected after both size admissions.
     One original type per actual spelling excludes the rename retry.
     Repeated same-type binders are permitted; different-type collisions
     decline before INST_TYPE and remain an unfinished coverage gap. *)
  val begin_original : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {original : SmtReplayProof.closed_fact, template_limit : int,
     check_type : Type.hol_type -> unit} -> producer
  (* The SAME opaque invocation ledger is retained by producer/plan/instance.
     Only named H counters/reservations are hooked, not initial size/kernel
     internals or complete I/B/P/F/GP work. No external counter pairing. *)
  val begin_original_with_work : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {original : SmtReplayProof.closed_fact,template_limit : int,
     check_type : Type.hol_type -> unit,
     work : SmtReplayInvocationWork.portfolio} -> producer
  val original_theorem : producer -> Thm.thm
  val type_variables : producer -> Type.hol_type list
  (* Domain indices refer to the producer's original finite variable table.
     Order is retained; duplicate/invalid domains are rejected at this NEW
     API boundary. Residues use simultaneous substitution, without occurs
     checks or recursive substitution of a returned residue. *)
  val prepare : producer ->
    {bindings : (int * Type.hol_type) list} -> plan
  (* Retained repeated annotation portfolio prepared BEFORE INST_TYPE.
     DATA only; SAME owner/scope/epoch/cap, no action or new allowance.
     Type construction/lookup work remains the existing charged H envelope. *)
  (* Genuine empty original type-variable table only. SAME original
     repeated policy portfolio/cumulative budget; no INST_TYPE/import.
     Execute retains EXACT original theorem and checked closed plan. *)
  val prepare_identity : producer -> plan
  val planned_syntax : plan ->
    {raw : int,binder : int,typed_annotations : Type.hol_type list}
  (* Single use. INST_TYPE uses actual original_theorem, not a canonical
     private proof. The exact result is admitted into SAME graph/scope and
     recorded as a fresh CLOSED P law; its original is the typed theorem. *)
  val execute : plan -> instance
  val selected_original : instance -> Thm.thm
  val typed_theorem : instance -> Thm.thm
  val typed_plan : instance -> SmtReplayProof.closed_fact
  val validate_instance : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    int -> instance -> unit
  (* Checks the exact RETAINED opaque ledger, not a paired public counter.
     This is accounting ownership metadata, not original Root issuance. *)
  val validate_instance_with_work : SmtReplayGraph.graph ->
    SmtReplayGraph.scope -> int -> SmtReplayInvocationWork.portfolio ->
    instance -> unit
  val substitution : instance ->
    (Type.hol_type, Type.hol_type) Lib.subst
  (* Existing exact type-ID / complete-binder refusal remains unchanged.
     BAG instances still retain binders and do NOT become carrier transfer
     merely by passing to this strict specialization operation. *)
  val specialize : instance -> {operands : SmtReplayGraph.node list} ->
    {theorem : Thm.thm, holes : Term.term list}
  val charged : producer -> int
  (* Metadata only: no invented symbol-byte cap or global work claim. *)
  type policy_producer
  type policy_plan
  type policy_instance
  val begin_original_with_policy : SmtReplayGraph.graph ->
    SmtReplayGraph.scope ->
    {original:SmtReplayProof.closed_fact,check_type:Type.hol_type->unit,
     work:SmtReplayInvocationWork.portfolio,
     native_contract:SmtReplayNativeContract.contract} -> policy_producer
  val type_variables_with_policy : policy_producer -> Type.hol_type list
  val prepare_with_policy : policy_producer ->
    {bindings:(int*Type.hol_type) list} -> policy_plan
  val prepare_identity_with_policy : policy_producer -> policy_plan
  val planned_syntax_with_policy : policy_plan ->
    {raw:int,binder:int,typed_annotations:Type.hol_type list}
  val execute_with_policy : policy_plan -> policy_instance
  val typed_theorem_with_policy : policy_instance -> Thm.thm
  val typed_plan_with_policy : policy_instance -> SmtReplayProof.closed_fact
  val substitution_with_policy : policy_instance ->
    (Type.hol_type,Type.hol_type) Lib.subst
  val validate_instance_with_policy_for :
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     work:SmtReplayInvocationWork.portfolio} -> policy_instance -> unit
  val charged_with_policy : policy_producer -> int

end
