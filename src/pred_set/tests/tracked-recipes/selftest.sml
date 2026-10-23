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
val catalog =
  [("SET_SPEC",pred_setSimps.SET_SPEC_ss,pred_setSimpsExt.SET_SPEC_ss),
   ("GSPEC_SIMP",pred_setSimps.GSPEC_SIMP_ss,
                  pred_setSimpsExt.GSPEC_SIMP_ss)]
fun compare ordinary tracked (tm,expected) = let
  val ot = total (O.SIMP_CONV ordinary []) tm
  val tt = total (S.SIMP_CONV tracked []) tm
  val xt = total (TraverseExt.XTRAVERSE
    (S.xtraversedata_for_ss tracked) []) tm
in
  check "pred_set ordinary/tracked/configured complete theorem"
    (same (ot,tt) andalso same (tt,xt));
  check ("pred_set expected result: " ^ term_to_string tm ^ " -> " ^
         term_to_string (rhs (concl tt)))
    (null (hyp tt) andalso aconv (lhs (concl tt)) tm andalso
     aconv (rhs (concl tt)) expected)
end
val _ = List.app (fn (name,ofrag,tfrag) =>
  check (name ^ ": exact fragment name, no native rewrites")
    (O.frag_name ofrag = SOME name andalso
     S.frag_name tfrag = SOME name andalso
     null (S.frag_rewrites tfrag))) catalog
val setO = O.++ (boolSimps.bool_ss,pred_setSimps.SET_SPEC_ss)
val setT = S.++ (boolSimpsExt.bool_ss,pred_setSimpsExt.SET_SPEC_ss)
val _ = List.app (compare setO setT)
  [(``(a:'a) IN {x | P x}``, ``P (a:'a):bool``),
   (``(a:'a) IN {x | T}``, ``T``),
   (``(a:'a) IN {x | F}``, ``F``),
   (``(a:'a) IN {f x | P x}``, ``?x:'b. (a = f x) /\ P x``),
   (``{x:'a | T}``, ``{x:'a | T}``),
   (``(a:'a) IN s``, ``(a:'a) IN s``)]
val gspecO = O.++ (boolSimps.bool_ss,pred_setSimps.GSPEC_SIMP_ss)
val gspecT = S.++ (boolSimpsExt.bool_ss,pred_setSimpsExt.GSPEC_SIMP_ss)
val _ = List.app (compare gspecO gspecT)
  [(``{x:'a | T}``, ``UNIV:'a set``),
   (``{x:'a | F}``, ``{}:'a set``),
   (``{f (x:'a) | F}``, ``{}:'b set``),
   (``{(x:'a,y:'b) | F}``, ``{}:('a # 'b) set``),
   (``{x:'a | P x}``, ``{x:'a | P x}``),
   (``GSPEC (\x:'a. (c:'b,T))``, ``GSPEC (\x:'a. (c:'b,T))``),
   (``(f:'a -> 'b) x``, ``(f:'a -> 'b) x``)]
val bothO = O.++ (setO,pred_setSimps.GSPEC_SIMP_ss)
val bothT = S.++ (setT,pred_setSimpsExt.GSPEC_SIMP_ss)
val _ = compare bothO bothT
  (``(a:'a) IN {x | P x /\ T}``, ``P (a:'a):bool``)
val _ = let
  val rule = ASSUME ``P (a:'a) = (q:bool)``
  val tm = ``(a:'a) IN {x | P x}``
  val ot = total (O.SIMP_CONV bothO [rule]) tm
  val tt = total (S.SIMP_CONV bothT [rule]) tm
in check "SET_SPEC retains supplied rule hypotheses"
     (same (ot,tt) andalso not (null (hyp tt)) andalso
      aconv (rhs (concl tt)) ``q:bool``) end
val _ = List.app (fn (name,_,frag) => let
  val only = S.++ (pureSimpsExt.pure_ss,frag)
  val _ = ignore (S.traversedata_for_ss only)
  val _ = ignore (S.xtraversedata_for_ss only)
in check (name ^ ": conversion never invents native sources")
     (null (S.rewrite_source_handles only)) end) catalog
val _ = let
  val tm = ``(a:'a) IN {x | P x}``
  val excluded = S.-* (bothT,["SET_SPEC_CONV"])
  val removed = S.remove_ssfrags ["SET_SPEC"] bothT
  val _ = check "SET_SPEC original conversion-name exclusion"
    (same (total (S.SIMP_CONV excluded []) tm,REFL tm))
  val _ = check "SET_SPEC named fragment removal"
    (same (total (S.SIMP_CONV removed []) tm,REFL tm))
  val tm = ``{x:'a | T}``
  val excluded = S.-* (bothT,["GSPEC_SIMP_CONV"])
  val removed = S.remove_ssfrags ["GSPEC_SIMP"] bothT
  val _ = check "GSPEC_SIMP original conversion-name exclusion"
    (same (total (S.SIMP_CONV excluded []) tm,REFL tm))
  val _ = check "GSPEC_SIMP named fragment removal"
    (same (total (S.SIMP_CONV removed []) tm,REFL tm))
in check "ordered recipe leaves original tracked set intact"
     (aconv (rhs (concl (total (S.SIMP_CONV bothT []) tm)))
       ``UNIV:'a set``) end
val _ = List.app (fn (name,_,_) =>
  check (name ^ ": registered in extension catalog")
    (case S.lookup_named_frag name of
       SOME frag => S.frag_name frag = SOME name | NONE => false)) catalog
val _ = List.app (fn (name,_,_) => let
  val _ = O.register_frag (O.named_rewrites name [TRUTH])
in check (name ^ ": ordinary registry cannot replace tracked recipe")
     (case (O.lookup_named_frag name,S.lookup_named_frag name) of
        (SOME ofrag,SOME tfrag) => length (O.frag_rewrites ofrag) = 1 andalso
          null (S.frag_rewrites tfrag)
      | _ => false) end) catalog
val _ = print ("PRED_SET_TRACKED_RECIPE_CHECKS=" ^
               Int.toString (!checks) ^ "\n")
val _ = OS.Process.exit OS.Process.success
