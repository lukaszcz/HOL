open Parse boolSyntax
fun proof ss input output = let
  val th = simpLib.SIMP_CONV ss [] input
in check "ordinary recipe complete proof"
  (null (Thm.hyp th) andalso Term.aconv (lhs (Thm.concl th)) input andalso
   Term.aconv (rhs (Thm.concl th)) output) end
val _ = proof boolSimps.bool_ss ``(\x:bool. x /\ T) p`` ``p:bool``
val _ = proof (simpLib.++ (boolSimps.bool_ss,numSimps.REDUCE_ss))
  ``(2 + 3):num`` ``5:num``
val _ = proof (simpLib.++ (boolSimps.bool_ss,combinSimps.COMBIN_ss))
  ``I (p:bool)`` ``p:bool``
