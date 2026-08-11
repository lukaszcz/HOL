Theory pairAutoSeed
Ancestors
  pair
Libs
  clasetLib clasimpLib

(* src/HOL/Product_Type.thy:604-637 @ f7e02b7e *)
Theorem UNCURRY_AUTO_IFF[iff]:
  !c p. UNCURRY c p <=> !x y. p = (x,y) ==> c x y
Proof
  Cases_on `p` >> simp [UNCURRY_DEF]
QED

(* src/HOL/Product_Type.thy:788-791 @ f7e02b7e *)
Theorem CURRY_AUTO_IFF[iff]:
  !f x y. CURRY f x y <=> f (x,y)
Proof
  simp [pairTheory.CURRY_DEF]
QED
