signature blastTerm =
sig
  (* This destructive term representation is private to the blast
     implementation.  In particular, it must not be put in clasetMeta's
     persistent stores or shared with the classical search engine. *)
  datatype term =
      Const of string * term list
    | Skolem of string * term option ref list
    | Free of string
    | Var of term option ref
    | Bound of int
    | Abs of string * term
    | $ of term * term

  type var = term option ref
  type state

  (* Pseudo-heads cannot collide with encoded HOL4 constants: real
     constants always have the fully qualified form "thy$name". *)
  val goal_name : string
  val false_name : string
  val const_name : {Thy : string, Name : string} -> string
  val mkGoal : term -> term
  val isGoal : term -> bool

  val newState : unit -> state
  val trailSize : state -> int
  (* Newest assignment first; used by blast's pruning test. *)
  val trailVars : state -> var list
  val clearTo : state -> int -> unit
  (* Normal measured rollback polls before each trail item.  If a poll raises,
     the remaining rollback is completed without callbacks before the exact
     exception is propagated. *)
  val clearToMeasured :
    (unit -> unit) -> state -> int -> unit

  val is_Var : term -> bool
  val dest_Var : term -> var
  val rand : term -> term
  val list_comb : term * term list -> term
  val strip_comb : term -> term * term list
  val head_of : term -> term

  val aconv : term * term -> bool
  val aconvMeasured : (unit -> unit) -> term * term -> bool
  val mem_term : term * term list -> bool
  val ins_term : term * term list -> term list
  val mem_var : var * var list -> bool
  val ins_var : var * var list -> var list
  val add_term_vars : term * var list -> var list
  val add_terms_vars : term list * var list -> var list
  val add_vars_vars : var list * var list -> var list
  val vars_in_vars : var list -> var list
  val add_term_vars_measured :
    (unit -> unit) -> term * var list -> var list
  val add_terms_vars_measured :
    (unit -> unit) -> term list * var list -> var list
  val vars_in_vars_measured : (unit -> unit) -> var list -> var list

  val incr_bv : int -> int -> term -> term
  val incr_boundvars : int -> term -> term
  val loose_bnos : term -> int list
  val subst_bound : term * term -> term
  val incr_boundvars_measured : (unit -> unit) -> int -> term -> term
  val loose_bnos_measured : (unit -> unit) -> term -> int list
  val subst_bound_measured :
    (unit -> unit) -> term * term -> term

  val norm : term -> term
  val normMeasured : (unit -> unit) -> term -> term
  val wkNorm : term -> term
  val varOccur : var -> term -> bool
  val varOccurMeasured : (unit -> unit) -> var -> term -> bool

  (* [vars] are variables local to the freshly converted rule.  Their
     assignments are deliberately off-trail; branch-variable assignments
     are trailed and are rolled back if unification fails. *)
  val unify : state -> var list * term * term -> bool
  (* As [unify], with checkpoints during recursive descent.  If a callback
     raises, all trailed branch assignments made since entry are rolled
     back before the exception is propagated.  Rule-local assignments are
     deliberately off-trail and belong to the discarded rule instance. *)
  val unifyMeasured :
    (unit -> unit) -> state -> var list * term * term -> bool
end
