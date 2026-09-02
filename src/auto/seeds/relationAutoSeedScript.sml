Theory relationAutoSeed
Ancestors
  relation

(* src/HOL/Orderings.thy:620-658 @ f7e02b7e.  Isabelle reads the order
   axioms off the linorder class, so its simplifier is never told that
   the order is transitive: the class fact is in scope wherever the type
   is, and its order solver takes it from there.  A translated goal
   states the order as a premise about the relation instead, and a
   conditional rewrite whose side condition is [transitive R] -- the
   sorted_wrt bridge is one -- then stalls with the premise sitting
   unused beside it.  These take an order premise apart into the
   component the side condition asks for.

   Stated as implications rather than equivalences: the components do
   not reconstitute the order -- reflexivity, antisymmetry and
   transitivity are WeakOrder, but the simplifier would have to find all
   three to rewrite back -- and an equivalence would put the order
   predicate back on the goal it was just taken off. *)

Theorem PreOrder_components_AUTO[simp]:
  !R : 'a -> 'a -> bool.
    PreOrder R ==> reflexive R /\ transitive R
Proof
  simp[relationTheory.PreOrder]
QED

Theorem Order_components_AUTO[simp]:
  !R : 'a -> 'a -> bool.
    Order R ==> antisymmetric R /\ transitive R
Proof
  simp[relationTheory.Order]
QED

Theorem WeakOrder_components_AUTO[simp]:
  !R : 'a -> 'a -> bool.
    WeakOrder R ==> reflexive R /\ antisymmetric R /\ transitive R
Proof
  simp[relationTheory.WeakOrder]
QED

Theorem StrongOrder_components_AUTO[simp]:
  !R : 'a -> 'a -> bool.
    StrongOrder R ==> irreflexive R /\ transitive R
Proof
  simp[relationTheory.StrongOrder]
QED

Theorem LinearOrder_components_AUTO[simp]:
  !R : 'a -> 'a -> bool.
    LinearOrder R ==>
    antisymmetric R /\ transitive R /\ trichotomous R
Proof
  simp[relationTheory.LinearOrder, relationTheory.Order]
QED

Theorem StrongLinearOrder_components_AUTO[simp]:
  !R : 'a -> 'a -> bool.
    StrongLinearOrder R ==>
    irreflexive R /\ transitive R /\ trichotomous R
Proof
  simp[relationTheory.StrongLinearOrder, relationTheory.StrongOrder]
QED

Theorem WeakLinearOrder_components_AUTO[simp]:
  !R : 'a -> 'a -> bool.
    WeakLinearOrder R ==>
    reflexive R /\ antisymmetric R /\ transitive R /\ trichotomous R
Proof
  simp[relationTheory.WeakLinearOrder, relationTheory.WeakOrder]
QED
