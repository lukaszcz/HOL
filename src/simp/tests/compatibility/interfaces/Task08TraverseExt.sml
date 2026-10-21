(* Full traversal interface; consumer functors elaborate against this
   signature. TASK_09 supplies the engine, not a stub in this fixture. *)
signature Task08TraverseExt =
sig
  include Task08ReducerTypes
  type simp_prover_ctxt =
    {stack : term list, context_thms : thm list, recurse : term -> thm}
  type ssolver = {name : string, solve : simp_prover_ctxt -> term -> thm}
  type subgoaler = simp_prover_ctxt -> term -> thm
  type traverse_data =
    {rewriters : reducer list, limit : int option, dprocs : reducer list,
     travrules : Travrules.travrules, relation : term}
  type traverse_config =
    {subgoaler : subgoaler option, solvers : ssolver list,
     cond_depth : int option, term_ord : (term * term -> order) option}
  type xtraverse_data = traverse_data * traverse_config
  val default_config : traverse_config
  (* Default settings, contexts initialized once at construction. *)
  val TRAVERSE : traverse_data -> thm list -> conv
  (* Contexts refreshed per application, even at default settings. *)
  val XTRAVERSE : xtraverse_data -> thm list -> conv
  type child_first_policy =
    {charge : unit -> unit, keep_abstraction : term -> bool}
  datatype traversal_policy = ParentFirst | ChildFirst of child_first_policy
  val charge_only : (unit -> unit) -> child_first_policy
  val keep_abstraction : child_first_policy -> term -> bool
  val NORMALIZE_ARGUMENTS : child_first_policy -> conv -> conv
  val TRAVERSE_WITH_CONTEXT : traversal_policy -> xtraverse_data ->
    {reducer_context : thm list, solver_context : thm list} -> conv
  val CHILD_FIRST_WITH_OBSERVER : (term -> unit) -> child_first_policy ->
    xtraverse_data ->
    {reducer_context : thm list, solver_context : thm list} -> conv
  val ROOT_REWRITE : xtraverse_data -> thm list -> conv
  val ROOT_REWRITE_WITH_CONTEXT : xtraverse_data ->
    {reducer_context : thm list, solver_context : thm list} -> conv
end
