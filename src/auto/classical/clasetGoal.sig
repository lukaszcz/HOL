signature clasetGoal =
sig
  include Abbrev

  type store = clasetMeta.store
  type meta = clasetMeta.meta
  type tymeta = clasetMeta.tymeta

  type cgoal = {params : term list, asl : term list, w : term}
  type replay_script
  type binding_mark = {terms : meta list, types : tymeta list}
  type binding_marks = binding_mark list
  type node

  (* Assumptions, including markerLib labels and abbreviations, are kept in
     their original order and otherwise treated as opaque formulae. *)
  val from_goal : goal -> node
  val create : {goals : cgoal list, store : store, level : int} -> node

  val goals : node -> cgoal list
  val store : node -> store
  val replay : node -> replay_script
  val replay_length : node -> int
  val level : node -> int
  val binding_marks : node -> binding_marks
  val set_goals : cgoal list -> node -> node
  val set_store : store -> node -> node
  val set_level : int -> node -> node
  val set_binding_marks : binding_marks -> node -> node
  val empty_binding_marks : binding_marks

  val goal_at : node -> int -> cgoal
  val replace_goal : node ->
                     {pos : int, children : cgoal list, store : store} ->
                     node

  (* New assumptions are added at the head.  [cons_assumptions [q1,q2]]
     therefore produces q2 :: q1 :: asl, as successive DISCH steps do. *)
  val cons_assumption : term -> cgoal -> cgoal
  val cons_assumptions : term list -> cgoal -> cgoal
  val delete_assumption : int -> cgoal -> cgoal

  (* [children] strips only each premise's outer !-then-==> prefix.
     Assumption positions are one-based.  [elim_children] returns
     alternatives in the parent's assumption-list order. *)
  val children : node ->
      {pos : int, premises : term list, consumed : int option} ->
      cgoal list * store
  val elim_children : node -> {pos : int, premises : term list} ->
      {assumption : int, major : term, children : cgoal list,
       store : store} list

  (* Isabelle's size_of_term: atoms and abstractions count one;
     applications themselves count nothing. *)
  val term_size : term -> int
  val cgoal_size : store -> cgoal -> int
  val size : node -> int

  (* Equality and ordering ignore replay/search bookkeeping.  Parameters are
     canonically rebound, so both operations respect alpha-conversion. *)
  val canonical_rendering : node -> term
  val equal : node * node -> bool
  val compare : node * node -> order

  (* D24 materialization stub.  Metavariables are represented by marked free
     variables and are therefore rigid to HOL4 tactics.  This version can
     lift results only when the rendered goal is metavariable-free; the full
     marked-free round trip and validation replay are completed later. *)
  val render : node -> int -> goal
  val unrender : node -> int -> goal list * validation -> node option
end
