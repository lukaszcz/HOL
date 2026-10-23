open HolKernel Parse boolLib testutils
structure O = simpLib
structure S = simpExtLib
val checks = ref 0
fun check label ok =
  (checks := !checks + 1; tprint label;
   if ok then OK () else die label)
fun same (a,b) = aconv (concl a) (concl b) andalso
  HOLset.equal (hypset a,hypset b)
fun total cv = QCONV (TRY_CONV cv)
val ordinary = O.++ (boolSimps.bool_ss,listSimps.LIST_EQ_ss)
val tracked = S.++ (boolSimpsExt.bool_ss,listSimpsExt.LIST_EQ_ss)
fun compare (tm,expected) = let
  val ot = total (O.SIMP_CONV ordinary []) tm
  val tt = total (S.SIMP_CONV tracked []) tm
  val xt = total (TraverseExt.XTRAVERSE
    (S.xtraversedata_for_ss tracked) []) tm
in
  check "LIST_EQ ordinary/tracked/configured complete theorem"
    (same (ot,tt) andalso same (tt,xt));
  check "LIST_EQ expected result"
    (null (hyp tt) andalso aconv (lhs (concl tt)) tm andalso
     aconv (rhs (concl tt)) expected)
end
val _ = check "LIST_EQ exact original fragment name, no native rewrites"
  (S.frag_name listSimpsExt.LIST_EQ_ss = SOME "list EQ" andalso
   S.frag_name listSimpsExt.LIST_EQ_ss = O.frag_name listSimps.LIST_EQ_ss
   andalso null (S.frag_rewrites listSimpsExt.LIST_EQ_ss))
val _ = List.app compare
  [(``[a;b] = [a;c:'a]``, ``b = c:'a``),
   (``SNOC x l = l ++ [c:'a]``, ``x = c:'a``),
   (``(prefix:'a list) ++ l = prefix ++ r``, ``l = r:'a list``),
   (``l ++ (suffix:'a list) = r ++ suffix``, ``l = r:'a list``),
   (``(l:'a list) = r``, ``(l:'a list) = r``),
   (``(p:bool) = q``, ``(p:bool) = q``),
   (``(f:'a -> 'b) x``, ``(f:'a -> 'b) x``)]
val _ = let
  val tm = ``[a;b] = [a;d:'a]``
  val rule = ASSUME ``b = c:'a``
  val ot = total (O.SIMP_CONV ordinary [rule]) tm
  val tt = total (S.SIMP_CONV tracked [rule]) tm
in check "LIST_EQ retains supplied rule hypotheses"
     (same (ot,tt) andalso not (null (hyp tt)) andalso
      aconv (rhs (concl tt)) ``c = d:'a``) end
val only = S.++ (pureSimpsExt.pure_ss,listSimpsExt.LIST_EQ_ss)
val _ = ignore (S.traversedata_for_ss only)
val _ = ignore (S.xtraversedata_for_ss only)
val _ = check "LIST_EQ conversion creates no native source handles"
  (null (S.rewrite_source_handles only))
val _ = let
  val tm = ``SNOC x l = l ++ [c:'a]``
  val excluded = S.-* (only,["LIST_EQ_SIMP_CONV"])
  val removed = S.remove_ssfrags ["list EQ"] only
  val _ = check "LIST_EQ conversion exclusion uses original name"
    (same (total (S.SIMP_CONV excluded []) tm,REFL tm))
  val _ = check "LIST_EQ named fragment removal"
    (same (total (S.SIMP_CONV removed []) tm,REFL tm))
in check "LIST_EQ original set survives persistent removal"
     (aconv (rhs (concl (total (S.SIMP_CONV only []) tm))) ``x = c:'a``)
end
val _ = check "LIST_EQ registers in extension catalog"
  (case S.lookup_named_frag "list EQ" of
     SOME frag => S.frag_name frag = SOME "list EQ" | NONE => false)
val _ = ignore (O.register_frag (O.named_rewrites "list EQ" [TRUTH]))
val _ = check "ordinary registry entry cannot replace extension recipe"
  (case (O.lookup_named_frag "list EQ", S.lookup_named_frag "list EQ") of
     (SOME ordinary,SOME tracked) =>
       length (O.frag_rewrites ordinary) = 1 andalso
       null (S.frag_rewrites tracked)
   | _ => false)
val _ = print ("LIST_TRACKED_RECIPE_CHECKS=" ^ Int.toString (!checks) ^ "\n")
val _ = OS.Process.exit OS.Process.success
