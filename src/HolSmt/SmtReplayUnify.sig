(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayUnify =
sig
  type result
  type assignment =
    {variable : SmtReplayGraph.node, residue : SmtReplayGraph.node}
  datatype assumption_kind =
      ConstructorEquation of SmtReplayGraph.node
    | SolverAssignment of assignment
    | BinderEquality of SmtReplayGraph.node * SmtReplayGraph.node
  type assumption = {kind : assumption_kind, equation : Term.term}
  datatype failure = TypeMismatch | RigidMismatch | OccursCheck
    | NeedsBinderAdmission | EscapingScope
  datatype outcome = Unified of result | NoMatch of failure

  (* Only explicitly listed SolverFlexible nodes visible in this scope solve.
     Other variables remain rigid. Failure produces no theorem. Caller
     admission owns bounded binder/type work; an unknown opaque dependency
     requests admission rather than claiming absence. Foreign nodes/scopes
     and invalid flexibility permissions are programming errors (HOL_ERR). *)
  val unify : SmtReplayGraph.graph ->
    {scope : SmtReplayGraph.scope, flexible : SmtReplayGraph.node list,
     equations : (SmtReplayGraph.node * SmtReplayGraph.node) list} -> outcome
  (* Deferred local binder equalities are explicit obligations. Supplying
     them does not certify them; the caller must provide bounded witnesses. *)
  val unify_using : SmtReplayGraph.graph ->
    {scope : SmtReplayGraph.scope, flexible : SmtReplayGraph.node list,
     equations : (SmtReplayGraph.node * SmtReplayGraph.node) list,
     binders : (SmtReplayGraph.node * SmtReplayGraph.node) list} -> outcome
  (* Demand local binder discovery after assignment dereferencing. Returned
     assignments undergo the same permission/type/occurs/scope checks as input
     equations. The relation is only an obligation: assembly still requires
     an independent checked witness, never this callback's metadata. *)
  val unify_with_binders : SmtReplayGraph.graph ->
    (SmtReplayGraph.node * SmtReplayGraph.node -> assignment list option) ->
    {scope : SmtReplayGraph.scope, flexible : SmtReplayGraph.node list,
     equations : (SmtReplayGraph.node * SmtReplayGraph.node) list,
     binders : (SmtReplayGraph.node * SmtReplayGraph.node) list} -> outcome
  val validate_result : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    result -> unit

  (* Retain the acyclic dependency order; residues may mention earlier/later
     assignments. These assumptions are solver obligations, never syntax
     definitions or a trusted semantic rewrite. *)
  val assignments : result -> assignment list
  val assumptions : result -> assumption list
  val roots : result -> SmtReplayGraph.node list
  val context : result -> Term.term
  (* Executable context/proof access rejects a closed result scope. *)
  val proofs : result ->
    ((SmtReplayGraph.node * SmtReplayGraph.node) * Thm.thm) list
  (* Exact dependency leaf projection from the recorded split tree. *)
  val projection : result -> int -> Thm.thm

  (* Results contain only compact theorems. The caller must independently
     discharge solver assignment obligations and close constructor facts
     before one simultaneous realization outside binders. *)
end
