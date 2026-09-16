Theory relationAutoSeed
Ancestors
  relation
Libs
  clasetLib

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

(* src/HOL/Wellfounded.thy:1136 @ f7e02b7e.  [wf_inv_image] is a [simp]
   rule and a safe [intro] there; relation states the same content as
   WF_inv_image and declares it to neither, so a well-foundedness goal
   about an inverse image is inert in both halves of the layer.
   Declared unsafe rather than [sintro]: a safe introduction owes
   seedAudit the inversion WF (inv_image R f) ==> WF R, which is false
   -- a constant f empties the inverse image whatever R is. *)
Theorem WF_inv_image_AUTO[simp, intro]:
  !relation function.
    WF relation ==> WF (inv_image relation function)
Proof
  METIS_TAC [relationTheory.WF_inv_image]
QED

(* src/HOL/Relation.thy:1680 @ f7e02b7e.  [in_inv_image] is simp there:
   Isabelle's simpset reads an inverse image at a pair without being
   told to, which is how a proof that unfolds a definition built on
   [inv_image] carries on into the underlying relation.  relation
   states the same content unapplied, as the constant's definition,
   and declares it to no simpset. *)
Theorem IN_INV_IMAGE_AUTO[simp]:
  !relation function left right.
    inv_image relation function left right <=>
    relation (function left) (function right)
Proof
  simp[relationTheory.inv_image_def]
QED
