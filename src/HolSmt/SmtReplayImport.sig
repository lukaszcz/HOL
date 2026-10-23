(* Copyright (c) 2026 The HOL4 contributors. *)

signature SmtReplayImport =
sig
  (* Bounded public application-path hint. Binder bodies remain opaque and
     every bucket hit still requires an exact physical-identity check. *)
  val pointer_bucket : int -> int -> Term.term -> int
  (* Same bounded programme with paid metadata observations, not a
     hash certificate or permission to use a native operand. *)
  val pointer_bucket_observed : (IntInf.int -> unit) -> int -> int ->
    Term.term -> int

  (* Count-only view: marker names may collide with free variables. Never
     use this view for binding, free-variable analysis or proof endpoints. *)
  val count_body : Term.term -> Term.term

  (* The raw Term.term_size metric excludes the binder variable slot. *)
  val bounded_raw_size : int -> Term.term -> int option
  (* Same metric; check the function Type before count-only opening of
     EVERY binder. The check must admit native classification of its range,
     not just its domain (standard count_body uses REFL/Beta at the range). *)
  val bounded_raw_size_with_type_check :
    (Type.hol_type -> unit) -> int -> Term.term -> int option

  (* Sealed success from the SAME genuine bounded raw-size programme.
     This is a syntax upper bound, not a theorem, Scope or Source receipt. *)
  type raw_bound
  val bounded_raw_size_with_bound :
    {limit:int,observe:unit -> unit} -> Term.term -> raw_bound option
  val bounded_raw_size_with_bound_observed :
    {limit:int,observe:unit -> unit} -> Term.term -> raw_bound option
  val raw_bound_data : raw_bound -> Term.term ->
    {raw_upper:IntInf.int,inc_upper:IntInf.int}
  (* App-only actual-pointer descent from an already bounded native root.
     A derived child's upper bound is inherited, not its exact raw count.
     The observer pays actual visits/comparisons/copies before each step. *)
  val raw_bound_subterm : raw_bound ->
    {target:Term.term,observe:unit -> unit} -> raw_bound option
  (* SmtResource's unfolded metric includes the binder variable slot. *)
  val bounded_binder_size : int -> Term.term -> int option
  (* Exact IntInf size under an explicit optional ceiling. NONE denotes
     finite excess, never absence of syntax. No default or raw-child grant. *)
  val raw_size_with_policy : SmtReplayResourcePolicy.limit ->
    Term.term -> IntInf.int option
  val binder_size_with_policy : SmtReplayResourcePolicy.limit ->
    Term.term -> IntInf.int option

end
