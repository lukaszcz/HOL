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
val ordinaryDefaults =
  [realSimps.REAL_REDUCE_ss,realSimps.RMULCANON_ss,realSimps.RMULRELNORM_ss]
val trackedDefaults =
  [realSimpsExt.REAL_REDUCE_ss,realSimpsExt.RMULCANON_ss,
   realSimpsExt.RMULRELNORM_ss]
val _ = check "real logged default names and append order"
  (map O.frag_name ordinaryDefaults = map S.frag_name trackedDefaults andalso
   map S.frag_name trackedDefaults =
     map SOME ["REAL_REDUCE","RMULCANON","RMULRELNORM"])
val _ = ListPair.appEq (fn (ofrag,tfrag) => let
  val ors = O.frag_rewrites ofrag
  val trs = S.frag_rewrites tfrag
  val _ = ListPair.appEq (fn ((i,a),b) =>
    if same (a,b) then () else
      (print ("Ingredient " ^ Int.toString i ^ "\n");
       print (thm_to_string a ^ "\n" ^ thm_to_string b ^ "\n")))
    (Lib.enumerate 0 ors,trs)
in
  check "exact ordered real rewrite ingredients and hypotheses"
    (ListPair.allEq same (ors,trs))
end) (ordinaryDefaults,trackedDefaults)
val os = List.foldl (fn (f,s) => O.++ (s,f))
  (O.++ (boolSimps.bool_ss,numSimps.REDUCE_ss)) ordinaryDefaults
val ts = List.foldl (fn (f,s) => S.++ (s,f))
  (S.++ (boolSimpsExt.bool_ss,numSimpsExt.REDUCE_ss)) trackedDefaults
val logged = BasicProvers.apply_logged_updates {theories=["real"]}
  boolSimps.bool_ss
val _ = check "actual ordinary real log selects exactly these defaults"
  (List.filter (fn n => List.exists (fn k => n=k)
     ["REAL_REDUCE","RMULCANON","RMULRELNORM","RADDCANON","REAL_ARITH",
      "real","real_ac"]) (O.ssfrag_names_of logged) =
   ["RMULRELNORM","RMULCANON","REAL_REDUCE"])
val _ = check "installed default fragment order agrees"
  (O.ssfrag_names_of os = S.ssfrag_names_of ts)
fun compare label os ts rules tm = let
  val ot = total (O.SIMP_CONV os rules) tm
  val tt = total (S.SIMP_CONV ts rules) tm
  val xt = total (TraverseExt.XTRAVERSE
    (S.xtraversedata_for_ss ts) rules) tm
in
  check label (same (ot,tt) andalso same (tt,xt)); tt
end
fun example (tm,result,rules) = let
  val th = compare "ordinary/tracked/configured complete real theorem"
             os ts rules tm
  val ok = aconv (lhs (concl th)) tm andalso
           aconv (rhs (concl th)) result
  val _ = if ok then () else
    print (thm_to_string th ^ "\nExpected: " ^ term_to_string result ^ "\n")
in check "real expected result and exact input" ok end
val _ = List.app example
  [(``(1:real) / 2 + 1 / 3``, ``(5:real) / 6``, []),
   (``(6:real) / 8``, ``(3:real) / 4``, []),
   (``~(6:real) / 9``, ``~(2:real) / 3``, []),
   (``~(6:real) / 8``, ``~(3:real) / 4``, []),
   (``(6:real) / 3``, ``(2:real)``, []),
   (``(2:real) / 3``, ``(2:real) / 3``, []),
   (``(0:real) / 3``, ``(0:real)``, []),
   (``(2:real) * 3``, ``(6:real)``, []),
   (``(1:real) / 2 - 1``, ``~(1:real) / 2``, []),
   (``(2:real) / 3 / (4 / 5)``, ``(5:real) / 6``, []),
   (``~((1:real) / 2)``, ``~(1:real) / 2``, []),
   (``abs (~(3:real) / 4)``, ``(3:real) / 4``, []),
   (``max ((1:real) / 2) (2 / 3)``, ``(2:real) / 3``, []),
   (``min (~(1:real) / 2) (2 / 3)``, ``~(1:real) / 2``, []),
   (``NUM_FLOOR ((7:real) / 2)``, ``3:num``, []),
   (``NUM_CEILING ((7:real) / 2)``, ``4:num``, [boolTheory.LET_THM]),
   (``((2:real) / 3) pow 2``, ``(4:real) / 9``, []),
   (``(1:real) / 2 < 2 / 3``, ``T``, []),
   (``(2:real) / 3 <= 1 / 2``, ``F``, []),
   (``(1:real) / 2 > 1 / 3``, ``T``, []),
   (``(1:real) / 2 >= 2 / 3``, ``F``, []),
   (``(2:real) / 4 = 1 / 2``, ``T``, []),
   (``(y:real) * x``, ``(x:real) * y``, []),
   (``(x:real) * x``, ``(x:real) pow 2``, []),
   (``(x:real) * 2 * 3``, ``(6:real) * x``, []),
   (``(2:real) * x = 2 * y``, ``(x:real) = y``, []),
   (``(2:real) * x <= 2 * y``, ``(x:real) <= y``, []),
   (``~(2:real) * x < ~2 * y``, ``(y:real) < x``, []),
   (``(c:real) * x = c * y``, ``(c:real) = 0 \/ (x:real) = y``, []),
   (``(c:real) * x <= c * y``, ``(c:real) * x <= c * y``, []),
   (``(c:real) * x < c * y``, ``(c:real) * x < c * y``, []),
   (``(c:real) * x <= c * y``, ``(x:real) <= y``,
      [ASSUME ``(0:real) < c``]),
   (``(c:real) * x < c * y``, ``(y:real) < x``,
      [ASSUME ``(c:real) < 0``]),
   (``(c:real) * x = c * y``, ``(x:real) = y``,
      [ASSUME ``~((c:real) = 0)``]),
   (``(x:real) + y``, ``(x:real) + y``, []),
   (``(f:real -> real) x``, ``(f:real -> real) x``, []),
   (``(x:real) / 3``, ``(x:real) / 3``, [])]
val _ = let
  val rule = ASSUME ``(0:real) < c``
  val th = total (S.SIMP_CONV ts [rule]) ``(c:real) * x <= c * y``
in check "side-condition solver retains precisely its hypothesis"
     (HOLset.equal (hypset th,hypset rule)) end

(* The reduction recipe's anonymous native sources must stay anonymous;
   conversion-only recipes must not invent equality source handles. *)
val red = S.++ (pureSimpsExt.pure_ss,realSimpsExt.REAL_REDUCE_ss)
val _ = check "anonymous reduction source metadata"
  (not (null (S.rewrite_source_handles red)) andalso
   List.all (fn h => not (isSome (#1 (S.source_rewrite h))))
     (S.rewrite_source_handles red))
val _ = List.app (fn frag =>
  check "conversion-only real recipes have no native rewrite sources"
    (null (S.rewrite_source_handles (S.++ (pureSimpsExt.pure_ss,frag)))))
  [realSimpsExt.RMULCANON_ss,realSimpsExt.RMULRELNORM_ss]
val _ = List.app (fn name =>
  check "extension catalog owns real recipe"
    (case S.lookup_named_frag name of
       SOME frag => S.frag_name frag = SOME name | NONE => false))
  ["REAL_REDUCE","RMULCANON","RMULRELNORM"]

val _ = ignore (compare "one-step traversal limit agrees"
  (O.limit 1 os) (S.limit 1 ts) [] ``(6:real) / 8 + 1 / 2``)
val _ = ignore (compare "zero traversal limit agrees"
  (O.limit 0 os) (S.limit 0 ts) [] ``(6:real) / 8``)
val _ = check "zero traversal limit prevents reduction"
  (same (total (S.SIMP_CONV (S.limit 0 ts) []) ``(6:real) / 8``,
         REFL ``(6:real) / 8``))
fun excluded name ofrag tfrag tm = let
  val ordinary = O.++ (boolSimps.bool_ss,ofrag)
  val tracked = S.++ (boolSimpsExt.bool_ss,tfrag)
  val th = compare "original conversion name exclusion agrees"
    (O.-* (ordinary,[name])) (S.-* (tracked,[name])) [] tm
in check "conversion exclusion is effective" (same (th,REFL tm)) end
(* The historical dotted conversion name is deliberately preserved.
   Strict -* parses it as a theory-qualified name and rejects realSimps,
   which is a structure, not a theory.  Do not silently rename/fix it. *)
fun rejects f = (f (); false) handle HOL_ERR _ => true
val _ = check "dotted real conversion name has ordinary strict-name behavior"
  (rejects (fn () => ignore (O.-* (os,["realSimps.elim_common_factor"])))
   andalso rejects (fn () =>
     ignore (S.-* (ts,["realSimps.elim_common_factor"]))))
val _ = let
  val tm = ``(6:real) / 8``
  val th = compare "removing REAL_REDUCE removes common-factor conversion"
    (O.remove_ssfrags ["REAL_REDUCE"]
      (O.++ (boolSimps.bool_ss,realSimps.REAL_REDUCE_ss)))
    (S.remove_ssfrags ["REAL_REDUCE"]
      (S.++ (boolSimpsExt.bool_ss,realSimpsExt.REAL_REDUCE_ss))) [] tm
in check "common-factor recipe removal is effective" (same (th,REFL tm)) end
val _ = excluded "REALMULCANON"
  realSimps.RMULCANON_ss realSimpsExt.RMULCANON_ss ``(y:real) * x``
val _ = excluded "RMUL_LEQNORM"
  realSimps.RMULRELNORM_ss realSimpsExt.RMULRELNORM_ss
  ``(2:real) * x <= 2 * y``
val _ = excluded "RMUL_LTNORM"
  realSimps.RMULRELNORM_ss realSimpsExt.RMULRELNORM_ss
  ``(2:real) * x < 2 * y``
(* Isolate each equality key: another overlapping equality conversion
   must not accidentally satisfy the test for the selected conversion. *)
val eqnames = map (fn i => "RMUL_EQNORM" ^ Int.toString i) [1,2,3,4,5,6]
val _ = List.app (fn (name,tm) => let
  val others = List.filter (fn n => n <> name) eqnames
  val ordinary = O.-*
    (O.++ (boolSimps.bool_ss,realSimps.RMULRELNORM_ss),others)
  val tracked = S.-*
    (S.++ (boolSimpsExt.bool_ss,realSimpsExt.RMULRELNORM_ss),others)
  val th = compare "isolated original equality conversion key" ordinary
             tracked [] tm
  val _ = check "isolated equality key really normalizes"
    (not (same (th,REFL tm)))
  val blocked = S.-* (tracked,[name])
in check "isolated equality conversion original name excludes it"
     (same (total (S.SIMP_CONV blocked []) tm,REFL tm)) end)
  (ListPair.zipEq (eqnames,
    [``(2:real) * x = 2 * y``, ``(2:real) * x = 2 * y``,
     ``(x:real) / 2 = y / 3``, ``(x:real) / 2 = y / 3``,
     ``(x:real) pow 2 = x pow 3``, ``(x:real) pow 2 = x pow 3``]))
val _ = let
  val tm = ``(y:real) * x``
  val oset = O.++ (boolSimps.bool_ss,realSimps.RMULCANON_ss)
  val tset = S.++ (boolSimpsExt.bool_ss,realSimpsExt.RMULCANON_ss)
  val th = compare "fragment removal agrees"
    (O.remove_ssfrags ["RMULCANON"] oset)
    (S.remove_ssfrags ["RMULCANON"] tset) [] tm
  val _ = check "fragment removal is effective" (same (th,REFL tm))
  val blocked = S.++ (S.exclude_ssfrags ["RMULCANON"] tset,
                      realSimpsExt.RMULCANON_ss)
in check "excluded real fragment cannot return on addition"
     (same (total (S.SIMP_CONV blocked []) tm,REFL tm)) end
val _ = let
  val rule = ASSUME ``(real_recipe_f:real -> real) x = y``
  val boundedO = O.++ (os,O.rewrites [Once rule])
  val boundedT = S.++ (ts,S.rewrites [Once rule])
  val cvO = total (O.SIMP_CONV boundedO [])
  val cvT = total (S.SIMP_CONV boundedT [])
  val tm = lhs (concl rule)
  val _ = check "bounded native rule first use retains exact hypothesis"
    (same (cvO tm,rule) andalso same (cvT tm,rule))
  val _ = check "real defaults do not refresh spent rule allowance"
    (same (cvO tm,REFL tm) andalso same (cvT tm,REFL tm))
  val hs = S.rewrite_source_handles boundedT
  val replay = S.remove_ssfrags_preserving_controls ["RMULRELNORM"] boundedT
in check "removal preserves surviving source identities and spent quota"
  (ListPair.allEq S.same_rewrite_source
     (hs,S.rewrite_source_handles replay) andalso
   same (total (S.SIMP_CONV replay []) tm,REFL tm)) end
val _ = ignore (O.register_frag (O.named_rewrites "REAL_REDUCE" [TRUTH]))
val _ = check "ordinary registry replacement cannot replace tracked recipe"
  (case S.lookup_named_frag "REAL_REDUCE" of
     SOME frag => ListPair.allEq same
       (S.frag_rewrites frag,S.frag_rewrites realSimpsExt.REAL_REDUCE_ss)
   | NONE => false)
val _ = print ("REAL_RECIPE_CHECKS=" ^ Int.toString (!checks) ^ "\n")
val _ = OS.Process.exit OS.Process.success
