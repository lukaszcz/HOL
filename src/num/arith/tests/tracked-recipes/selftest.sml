(* Opt-in numeral defaults: ordinary and tracked proofs, names and controls.
   Compare the entire theorem, not just its right-hand side. *)
open HolKernel Parse boolLib boolSyntax testutils
structure O = simpLib
structure S = simpExtLib
val checks = ref 0
fun check label ok =
  (checks := !checks + 1; tprint label;
   if ok then OK () else die label)
fun same (a,b) = aconv (concl a) (concl b) andalso
  HOLset.equal (hypset a,hypset b)
fun thms xs ys = ListPair.allEq same (xs,ys)
fun total cv = QCONV (TRY_CONV cv)
fun compare label os ts rules tm =
  check label (same (total (O.SIMP_CONV os rules) tm,
                    total (S.SIMP_CONV ts rules) tm))
fun expected label ss rules tm output = let
  val th = total (S.SIMP_CONV ss rules) tm
in check label (aconv (lhs (concl th)) tm andalso
                aconv (rhs (concl th)) output) end

val ordinaryDefaults =
  [numSimps.REDUCE_ss,numSimps.ARITH_RWTS_ss,numSimps.MOD_ss]
val trackedDefaults =
  [numSimpsExt.REDUCE_ss,numSimpsExt.ARITH_RWTS_ss,numSimpsExt.MOD_ss]
val _ = check "exact numeral logged append order"
  (map O.frag_name ordinaryDefaults = map S.frag_name trackedDefaults andalso
   map S.frag_name trackedDefaults =
     map SOME ["REDUCE","ARITH_RWTS","MOD"])
val _ = ListPair.appEq (fn (ofrag,tfrag) =>
  check "fragment name and exact ordered rewrite ingredients"
    (O.frag_name ofrag = S.frag_name tfrag andalso
     thms (O.frag_rewrites ofrag) (S.frag_rewrites tfrag)))
  (ordinaryDefaults,trackedDefaults)
val os = List.foldl (fn (f,s) => O.++ (s,f))
  boolSimps.bool_ss ordinaryDefaults
val ts = List.foldl (fn (f,s) => S.++ (s,f))
  boolSimpsExt.bool_ss trackedDefaults
val _ = check "installed order matches ordinary (history is newest first)"
  (map O.frag_name (O.ssfrags_of os) =
   map S.frag_name (S.ssfrags_of ts) andalso
   List.take (S.ssfrag_names_of ts,3) = ["MOD","ARITH_RWTS","REDUCE"])
(* Exercise the actual public ordinary log, not a guess at its order. *)
val logged = BasicProvers.apply_logged_updates {theories=["numeral"]}
  boolSimps.bool_ss
val _ = check "actual ordinary numeral log has these three defaults"
  (List.filter (fn n => List.exists (fn k => n=k)
     ["REDUCE","ARITH_RWTS","MOD","ARITH_DP","ARITH_NORM","SUC_FILTER"])
     (O.ssfrag_names_of logged) = ["MOD","ARITH_RWTS","REDUCE"])

(* Every ground reducer key, including the SUC guard and non-ground refusal. *)
val ro = O.++ (boolSimps.bool_ss,numSimps.REDUCE_ss)
val rt = S.++ (boolSimpsExt.bool_ss,numSimpsExt.REDUCE_ss)
val reductions =
  [(``EVEN 12``, ``T``), (``ODD 13``, ``T``),
   (``PRE 4``, ``3:num``), (``SUC 4``, ``5:num``),
   (``DIV2 9``, ``4:num``), (``6 * 7``, ``42:num``),
   (``23 + 19``, ``42:num``), (``4 - 7``, ``0:num``),
   (``23 DIV 5``, ``4:num``), (``23 MOD 5``, ``3:num``),
   (``2 EXP 10``, ``1024:num``), (``2 < 3``, ``T``),
   (``2 <= 3``, ``T``), (``3 > 2``, ``T``), (``3 >= 2``, ``T``),
   (``MIN 7 3``, ``3:num``), (``MAX 7 3``, ``7:num``),
   (``(2:num) = 3``, ``F``), (``SUC (SUC 2) + SUC 3``, ``8:num``),
   (``x + 3``, ``x + 3:num``), (``SUC x + 3``, ``SUC x + 3``)]
val _ = List.app (fn (tm,result) =>
  (compare "REDUCE ordinary/tracked proof" ro rt [] tm;
   expected "REDUCE expected result" rt [] tm result)) reductions
val _ = check "REDUCE conversions invent no equality rewrite sources"
  (null (S.rewrite_source_handles
    (S.++ (pureSimpsExt.pure_ss,numSimpsExt.REDUCE_ss))))

val arithmeticInputs =
  [``x + 0``, ``0 + x:num``, ``SUC x = 2``, ``2 = SUC x``,
   ``x * 1``, ``0 * x:num``, ``x - x``, ``x - 0``,
   ``x < x + c``, ``y + x < x + w``, ``x <= SUC x``,
   ``MIN x 0``, ``MAX x x``, ``(x MOD 1) + 0``, ``x DIV 1``,
   ``(x MOD n) MOD n``, ``~(x EXP n = 0)``]
val _ = List.app (compare "ARITH_RWTS ordinary/tracked proof" os ts [])
  arithmeticInputs
val _ = expected "local derived arithmetic rewrite" ts []
  ``x < x + c`` ``0 < c``
val _ = expected "symmetric SUC rewrite" ts [] ``2 = SUC x`` ``x = 1``

(* Compiled native sources retain both theory and local recipe names.
   Check every name against the ordered ordinary theorem ingredients. *)
val theoryNames =
  ["ADD_0", "ADD_EQ_0", "ADD_INV_0_EQ", "MULT_EQ_0", "MULT_EQ_1", "MULT_0",
   "MULT_RIGHT_1", "MULT_LEFT_1", "SUB_EQUAL_0", "SUC_SUB1", "SUB_0",
   "ADD_SUB", "SUB_EQ_0", "SUB_LESS_EQ", "SUB_MONO_EQ", "SUB_RIGHT_GREATER",
   "SUB_RIGHT_LESS", "SUB_RIGHT_GREATER_EQ", "SUB_RIGHT_LESS_EQ",
   "EXP_EXP_INJECTIVE", "EXP_BASE_INJECTIVE", "EXP_BASE_LT_MONO",
   "EXP_BASE_LE_MONO", "EXP_EXP_LT_MONO", "EXP_EXP_LE_MONO",
   "LESS_EQ_0", "LESS_EQ_ADD", "LESS_EQ_REFL", "LESS_MONO_ADD_EQ",
   "ADD_MONO_LESS_EQ", "EQ_MONO_ADD_EQ", "LESS_MONO_EQ", "LESS_EQ_MONO",
   "LESS_MULT_MONO", "MULT_SUC_EQ", "MULT_MONO_EQ", "NOT_SUC_LESS_EQ",
   "MULT_EXP_MONO", "LE_MULT_LCANCEL", "LE_MULT_RCANCEL", "LT_MULT_LCANCEL",
   "LT_MULT_RCANCEL", "LT_MULT_CANCEL_LBARE", "LT_MULT_CANCEL_RBARE",
   "LE_MULT_CANCEL_LBARE", "LE_MULT_CANCEL_RBARE", "ZERO_LESS_EQ",
   "MIN_0", "MAX_0", "MIN_IDEM", "MAX_IDEM", "MIN_LE", "MAX_LE", "MIN_LT",
   "MAX_LT", "MIN_MAX_EQ", "MIN_MAX_LT", "X_MOD_Y_EQ_X", "DIV_1", "MOD_1",
   "LESS_MOD", "ZERO_MOD", "MOD_MOD", "NUMERAL_MULT_EQ_DIV", "MOD_LESS",
   "DIV_LESS", "NOT_EXP_0", "NOT_ODD_EQ_EVEN", "NOT_SUC_ADD_LESS_EQ",
   "NOT_SUC_LESS_EQ_0"]
val localNames =
  ["SUC_EQ_1", "SUC_EQ_2", "ADD_0'", "ADD_INV_0_EQ'", "MULT_0'",
   "MULT_EQ_SUC0", "PRE", "ADD_SUB'", "LESS_0", "SUC_GT0", "GEQ0",
   "X_LT_SUC", "X_LE_SUC", "X_LT_X_PLUS", "X_LT_PLUS_X", "X_LE_X_PLUS",
   "X_LE_PLUS_X", "GEQ_REFL", "LESS_MONO_ADD_EQ'", "ADD_MONO_LESS_EQ",
   "EQ_MONO_ADD_EQ", "X_PLUS_LT_PLUS_X", "PLUS_X_LT_X_PLUS", "INV_SUC_EQ",
   "GT_REFL", "LESS_REFL", "NOT_LESS_0"]
val names = map (fn n => {Thy="arithmetic",Name=n}) theoryNames @
            map (fn n => {Thy="",Name=n}) localNames
val reference = S.++ (pureSimpsExt.pure_ss,S.rewrites_with_names
  (ListPair.zipEq (names,O.frag_rewrites numSimps.ARITH_RWTS_ss)))
val native = S.++ (pureSimpsExt.pure_ss,numSimpsExt.ARITH_RWTS_ss)
val _ = check "all compiled arithmetic names and proofs are exact"
  (ListPair.allEq (fn ((n,a),(m,b)) => n=m andalso same (a,b))
    (map S.source_rewrite (S.rewrite_source_handles reference),
     map S.source_rewrite (S.rewrite_source_handles native)))

(* MOD's MODEQ rewrites live in its relational reducer, not native handles.
   These cases need the weakener, modular congruences and side-condition
   solver; the final case requires the exponent congruence as well. *)
val _ = check "MOD has no invented native equality sources"
  (null (S.rewrite_source_handles
    (S.++ (pureSimpsExt.pure_ss,numSimpsExt.MOD_ss))))
val modInputs =
  [(``(6 * x + 7 + 6 * y) MOD 6``, ``1:num``, []),
   (``(4 + 3 * n + 1) MOD n``, ``5 MOD n``, [ASSUME ``0 < n``]),
   (``(SUC (n + x)) MOD n``, ``SUC x MOD n``, [ASSUME ``0 < n``]),
   (``((n + x) EXP k) MOD n``, ``(x EXP k) MOD n``,
    [ASSUME ``0 < n``])]
val _ = List.app (fn (tm,result,rules) =>
  (compare "MOD ordinary/tracked complete proof" os ts rules tm;
   expected "MOD expected result" ts rules tm result)) modInputs
val _ = let
  val rules = [ASSUME ``0 < n``]
  val tm = ``(4 + 3 * n + 1) MOD n``
  val th = total (S.SIMP_CONV ts rules) tm
in check "MOD retains precisely the used side-condition hypothesis"
  (HOLset.equal (hypset th,hypset (hd rules))) end

(* Traversal limits, literal conversion/rule exclusions, fragment removal,
   future fragment prohibition, and a surviving native bounded rule. *)
val _ = compare "zero traversal limit agrees"
  (O.limit 0 os) (S.limit 0 ts) [] ``23 + 19``
val _ = expected "zero traversal limit prevents conversion"
  (S.limit 0 ts) [] ``23 + 19`` ``23 + 19:num``
val noRedO = O.-* (ro,["REDUCE_CONV (arithmetic reduction)"])
val noRedT = S.-* (rt,["REDUCE_CONV (arithmetic reduction)"])
val _ = compare "literal REDUCE conversion exclusion agrees"
  noRedO noRedT [] ``23 + 19``
val _ = expected "literal REDUCE exclusion works"
  noRedT [] ``23 + 19`` ``23 + 19:num``
val noAddO = O.-* (os,["arithmetic.ADD_0"])
val noAddT = S.-* (ts,["arithmetic.ADD_0"])
val _ = compare "theory-qualified arithmetic exclusion agrees"
  noAddO noAddT [] ``x + 0``
val _ = expected "theory-qualified arithmetic exclusion works"
  noAddT [] ``x + 0`` ``x + 0:num``
val _ = compare "removing MOD preserves other defaults"
  (O.remove_ssfrags ["MOD"] os) (S.remove_ssfrags ["MOD"] ts) []
  ``(6 * x + 7 + 6 * y) MOD 6``
val _ = let
  val excludedO = O.exclude_ssfrags ["REDUCE"] os
  val excludedT = S.exclude_ssfrags ["REDUCE"] ts
  val prohibitedO = O.++ (excludedO,numSimps.REDUCE_ss)
  val prohibitedT = S.++ (excludedT,numSimpsExt.REDUCE_ss)
  val _ = compare "excluded fragment cannot return on later addition"
    prohibitedO prohibitedT [] ``23 + 19``
in expected "fragment prohibition remains effective"
     prohibitedT [] ``23 + 19`` ``23 + 19:num`` end
val _ = let
  val rule = ASSUME ``(num_recipe_f:num -> num) x = y``
  val boundedO = O.++ (os,O.rewrites [Once rule])
  val boundedT = S.++ (ts,S.rewrites [Once rule])
  val cvO = total (O.SIMP_CONV boundedO [])
  val cvT = total (S.SIMP_CONV boundedT [])
  val tm = lhs (concl rule)
  val _ = check "bounded rule first use preserves entire theorem"
    (same (cvO tm,rule) andalso same (cvT tm,rule))
  val _ = check "installed allowance is not refreshed by numeral defaults"
    (same (cvO tm,REFL tm) andalso same (cvT tm,REFL tm))
  val hs = S.rewrite_source_handles boundedT
  val replay = S.remove_ssfrags_preserving_controls ["MOD"] boundedT
in check "removing relational recipe retains native identities and quota"
  (ListPair.allEq S.same_rewrite_source
     (hs,S.rewrite_source_handles replay) andalso
   same (total (S.SIMP_CONV replay []) tm,REFL tm)) end

val _ = print ("NUMERAL_RECIPE_CHECKS=" ^ Int.toString (!checks) ^ "\n")
val _ = OS.Process.exit OS.Process.success
