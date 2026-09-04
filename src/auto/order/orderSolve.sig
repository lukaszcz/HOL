signature orderSolve =
sig
  include Abbrev

  (* How many distinct terms a single refutation may relate.  The search
     is linear in the edges per source and the sources are the goal's own
     distinctions, so the bound is on the size of the relation graph a
     goal presents rather than on the depth of a chain. *)
  val node_limit : int ref

  (* [F] from a contradictory set of literals, with the literals'
     theorems as its hypotheses. *)
  val refute : orderData.context -> orderData.fact list -> thm option

  (* The term, proved by refuting its negation against the order the
     theorems supply.  Raises [HOL_ERR] when no context refutes it.
     [prove_using] takes the contexts already derived, which is what a
     repeatedly consulted decision procedure holds on to. *)
  val prove_using : orderData.context list -> thm list -> term -> thm
  val prove_with : thm list -> term -> thm
end
