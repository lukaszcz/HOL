(* Opt-in integer defaults: compare conclusions AND complete hypothesis sets. *)
open HolKernel Parse boolLib testutils
structure O = simpLib
structure S = simpExtLib
val (_,Term) = parse_from_grammars
  (valOf (grammarDB {thyname="integer_word"}))
val checks = ref 0
fun check label ok =
  (checks := !checks + 1; tprint label;
   if ok then OK () else die label)
fun same (a,b) = aconv (concl a) (concl b) andalso
  HOLset.equal (hypset a,hypset b)
fun total cv = QCONV (TRY_CONV cv)
fun compare label os ts rules tm = let
  val ot = total (O.SIMP_CONV os rules) tm
  val tt = total (S.SIMP_CONV ts rules) tm
  val xt = total (TraverseExt.XTRAVERSE
    (S.xtraversedata_for_ss ts) rules) tm
in check label (same (ot,tt) andalso same (tt,xt)) end
fun expected label ts tm result = let
  val th = total (S.SIMP_CONV ts []) tm
in check label (null (hyp th) andalso aconv (lhs (concl th)) tm andalso
                aconv (rhs (concl th)) result) end

(* INT_SIZES_ss is hidden by integer_wordLib's signature. Inspect the public
   ordinary log in this test only; production recipes never read/replay it. *)
val wordLogged = BasicProvers.apply_logged_updates {theories=["integer_word"]}
  pureSimps.pure_ss
val wordOrdinary = valOf (List.find
  (fn f => O.frag_name f = SOME "int sizes") (O.ssfrags_of wordLogged))
val fragments =
  [(intReduce.INT_REDUCE_ss,intReduceExt.INT_REDUCE_ss,
    "INT_REDUCE","Integer calculation",Term `(-23:int) + 19`,Term `-4:int`),
   (wordOrdinary,integer_wordLibExt.INT_SIZES_ss,
    "int sizes","INT_SIZES_CONV",Term `integer_word$INT_MAX(:8)`,
    Term `127:int`)]
val ro = O.++ (pureSimps.pure_ss,intReduce.INT_REDUCE_ss)
val rt = S.++ (pureSimpsExt.pure_ss,intReduceExt.INT_REDUCE_ss)
val wo = O.++ (pureSimps.pure_ss,wordOrdinary)
val wt = S.++ (pureSimpsExt.pure_ss,integer_wordLibExt.INT_SIZES_ss)
val _ = List.app (fn (ofrag,tfrag,name,cvname,tm,result) => let
  val os = O.++ (pureSimps.pure_ss,ofrag)
  val ts = S.++ (pureSimpsExt.pure_ss,tfrag)
  val _ = check "exact original fragment name and empty rewrites"
    (O.frag_name ofrag = SOME name andalso S.frag_name tfrag = SOME name
     andalso null (O.frag_rewrites ofrag) andalso
     null (S.frag_rewrites tfrag))
  val _ = check "extension recipe registered under original name"
    (case S.lookup_named_frag name of
       SOME f => S.frag_name f = SOME name | NONE => false)
  val _ = ignore (S.traversedata_for_ss ts)
  val _ = ignore (S.xtraversedata_for_ss ts)
  val _ = check "conversion has no synthetic native rewrite sources"
    (null (S.rewrite_source_handles ts))
  val _ = compare "literal conversion-name exclusion agrees"
    (O.-* (os,[cvname])) (S.-* (ts,[cvname])) [] tm
  val _ = expected "literal conversion-name exclusion works"
    (S.-* (ts,[cvname])) tm tm
  val _ = compare "named fragment removal agrees"
    (O.remove_ssfrags [name] os) (S.remove_ssfrags [name] ts) [] tm
  val _ = expected "named fragment removal works"
    (S.remove_ssfrags [name] ts) tm tm
  val eo = O.++ (O.exclude_ssfrags [name] os,ofrag)
  val et = S.++ (S.exclude_ssfrags [name] ts,tfrag)
  val _ = compare "fragment prohibition survives later addition" eo et [] tm
  val _ = expected "fragment prohibition works" et tm tm
  val _ = compare "zero traversal limit agrees"
    (O.limit 0 os) (S.limit 0 ts) [] tm
  val _ = expected "zero traversal limit works" (S.limit 0 ts) tm tm
in expected "original set unaffected by controls" ts tm result end) fragments

(* All original integer keys: exponent, both ABS keys, fifteen binary keys.
   Also exercise both signs, nesting, non-literal arguments and wrong heads. *)
val reductions = map (fn (a,b) => (Term a,Term b))
  [(`(-2:int) ** 5`, `-32:int`),
   (`ABS (-7:int)`, `7:int`), (`ABS (7:int)`, `7:int`),
   (`(-23:int) + 19`, `-4:int`), (`(4:int) - 7`, `-3:int`),
   (`(-6:int) * 7`, `-42:int`), (`(-23:int) / 5`, `-5:int`),
   (`(-23:int) % 5`, `2:int`), (`(2:int) = 3`, `F`),
   (`(-2:int) < 3`, `T`), (`(-2:int) <= -3`, `F`),
   (`(3:int) > -2`, `T`), (`(3:int) >= 3`, `T`),
   (`(3:int) int_divides -12`, `T`), (`(5:int) int_divides 12`, `F`),
   (`integer$int_rem (-23) 5`, `-3:int`),
   (`integer$int_quot (-23) 5`, `-4:int`),
   (`int_min (-7) 3`, `-7:int`), (`int_max (-7) 3`, `3:int`),
   (`((-2:int) * 3) + 4`, `-2:int`), (`(2:int) ** 0`, `1:int`),
   (`(x:int) + 3`, `(x:int) + 3`), (`(x:int) ** 2`, `(x:int) ** 2`),
   (`(2:int) ** n`, `(2:int) ** n`), (`ABS (&n:int)`, `ABS (&n:int)`),
   (`ABS (-x:int)`, `ABS (-x:int)`),
   (`integer$int_add (2:int)`, `integer$int_add (2:int)`),
   (`(2:num) + 3`, `(2:num) + 3`)]
val _ = List.app (fn (tm,result) =>
  (compare "INT_REDUCE ordinary/tracked/configured full theorem" ro rt [] tm;
   expected "INT_REDUCE expected result" rt tm result)) reductions

val sizes = map (fn (a,b) => (Term a,Term b))
  [(`integer_word$INT_MIN(:8)`, `-128:int`),
   (`integer_word$INT_MAX(:8)`, `127:int`),
   (`integer_word$UINT_MAX(:8)`, `255:int`),
   (`integer_word$INT_MIN(:1)`, `-1:int`),
   (`integer_word$INT_MAX(:1)`, `0:int`),
   (`integer_word$UINT_MAX(:1)`, `1:int`),
   (`integer_word$INT_MIN(:32)`, `-2147483648:int`),
   (`integer_word$INT_MAX(:32)`, `2147483647:int`),
   (`integer_word$UINT_MAX(:32)`, `4294967295:int`),
   (`integer_word$INT_MIN(:'a)`, `integer_word$INT_MIN(:'a)`),
   (`integer_word$INT_MAX(:'a)`, `integer_word$INT_MAX(:'a)`),
   (`integer_word$UINT_MAX(:'a)`, `integer_word$UINT_MAX(:'a)`),
   (`words$INT_MAX(:8)`, `words$INT_MAX(:8)`),
   (`(2:int) + 3`, `(2:int) + 3`)]
val _ = List.app (fn (tm,result) =>
  (compare "INT_SIZES ordinary/tracked/configured full theorem" wo wt [] tm;
   expected "INT_SIZES expected result" wt tm result)) sizes

val os = O.++ (ro,wordOrdinary)
val ts = S.++ (rt,integer_wordLibExt.INT_SIZES_ss)
val _ = check "combined installation preserves original order"
  (O.ssfrag_names_of os = S.ssfrag_names_of ts andalso
   List.take (S.ssfrag_names_of ts,2) = ["int sizes","INT_REDUCE"])
val _ = compare "composed integer and word conversion"
  os ts [] (Term `integer_word$INT_MAX(:8) + 1`)
val _ = expected "composed result" ts
  (Term `integer_word$INT_MAX(:8) + 1`) (Term `128:int`)
val _ = let
  val rule = ASSUME (Term `(x:int) = 3`)
  val tm = Term `x + integer_word$INT_MAX(:8)`
  val _ = compare "conversion composition retains supplied hypotheses"
    os ts [rule] tm
  val th = total (S.SIMP_CONV ts [rule]) tm
in check "precise used hypothesis and computed result"
  (HOLset.equal (hypset th,hypset rule) andalso
   aconv (rhs (concl th)) (Term `130:int`)) end

(* Installed native Once controls coexist with conversions: spending and
   control-preserving fragment removal must not manufacture fresh sources. *)
val _ = let
  val rule = ASSUME (Term `(integer_recipe_f:int -> int) x = y`)
  val bo = O.++ (os,O.rewrites [Once rule])
  val bt = S.++ (ts,S.rewrites [Once rule])
  val co = total (O.SIMP_CONV bo [])
  val ct = total (S.SIMP_CONV bt [])
  val tm = lhs (concl rule)
  val _ = check "bounded native rule first use preserves full theorem"
    (same (co tm,rule) andalso same (ct tm,rule))
  val _ = check "integer recipes do not refresh installed allowance"
    (same (co tm,REFL tm) andalso same (ct tm,REFL tm))
  val hs = S.rewrite_source_handles bt
  val kept = S.remove_ssfrags_preserving_controls ["int sizes"] bt
  val kept2 = S.remove_ssfrags_preserving_controls ["INT_REDUCE"] kept
in check "removing both conversions preserves native identity and quota"
  (length hs = 1 andalso
   ListPair.allEq S.same_rewrite_source
     (hs,S.rewrite_source_handles kept2) andalso
   same (total (S.SIMP_CONV kept2 []) tm,REFL tm)) end

val _ = print ("INTEGER_RECIPE_CHECKS=" ^ Int.toString (!checks) ^ "\n")
val _ = OS.Process.exit OS.Process.success
