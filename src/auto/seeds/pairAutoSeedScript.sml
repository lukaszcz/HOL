Theory pairAutoSeed
Ancestors
  pair
Libs
  clasetLib clasimpLib

fun export_at attr (name, theorem) =
  let
    val saved = save_thm (name, theorem)
  in
    ThmAttribute.store_at_attribute
      {name = name, attrname = attr, args = [], thm = saved}
  end

fun export_iff entry = export_at "iff" entry

(* src/HOL/Product_Type.thy:520,524 @ f7e02b7e.  [split_paired_All] and
   [split_paired_Ex] are simp there and declared to no simpset here, so
   a quantifier over a pair is never taken apart.  Declared [iff] and
   not [simp]: as a rewrite it fires on every pair quantifier, and the
   translated goals quantify over pairs constantly -- measured, that
   stalls the list/map family.  As an iff rule it reaches the classical
   search, which applies it to a goal rather than to every subterm. *)
val _ =
  List.app export_iff
    [("FORALL_PROD_AUTO", pairTheory.FORALL_PROD),
     ("EXISTS_PROD_AUTO", pairTheory.EXISTS_PROD)]

(* src/HOL/Product_Type.thy:604-637 @ f7e02b7e *)
Theorem UNCURRY_AUTO_IFF[iff]:
  !c p. UNCURRY c p <=> !x y. p = (x,y) ==> c x y
Proof
  Cases_on `p` >> simp [UNCURRY_DEF]
QED

(* src/HOL/Product_Type.thy:600,607 @ f7e02b7e.  Isabelle states
   [case_prodI2'] and [case_prodE'] separately from the two above, and
   declares both safe, because a paired abstraction can be applied to
   further arguments: the rule above is about a proposition and this one
   about a predicate.  The two do not overlap -- [UNCURRY c p] there is
   a boolean and here it is a function. *)
Theorem UNCURRY_APPLIED_AUTO_IFF[iff]:
  !c p z. UNCURRY c p z <=> !x y. p = (x,y) ==> c x y z
Proof
  Cases_on `p` >> simp [UNCURRY_DEF]
QED

(* src/HOL/Product_Type.thy:788-791 @ f7e02b7e *)
Theorem CURRY_AUTO_IFF[iff]:
  !f x y. CURRY f x y <=> f (x,y)
Proof
  simp [pairTheory.CURRY_DEF]
QED
