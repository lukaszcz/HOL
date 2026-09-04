signature orderLib =
sig
  include Abbrev

  (* Decides a goal about a relation the goal itself says is an order.
     The assumptions supply both the axioms -- [transitive],
     [antisymmetric], [reflexive], [total], or any of the named orders
     that expand to them -- and the facts to chain. *)
  val ORDER_TAC : thm list -> tactic

  val ORDER_PROVE : term -> thm
  val ORDER_CONV : conv

  (* The same procedure as a simplifier decision procedure.  A decision
     procedure is asked about an atom wherever the traversal meets one,
     so this reaches both the atom a rewrite has left standing and the
     side condition of a conditional rewrite -- the side condition is
     simplified with the same simpset -- and a separate solver for the
     second position would decide nothing the first does not. *)
  val ORDER_REDUCER : Traverse.reducer
  val ORDER_ss : simpLib.ssfrag
end
