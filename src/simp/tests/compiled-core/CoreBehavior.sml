(* Compiler-focused public baseline contracts. Other compilation effects,
   exclusions, makers, duplicate history and printers reuse Routes.sml. *)
open HolKernel Parse boolLib simpLib boolSimps congLib Paired
(* Check actual fresh-process imports, not just a source dependency grep.
   All three ordinary entry modules above must remain extension-free. *)
val _ = List.app (fn name =>
  if List.exists (fn s => s = name) (Meta.loaded ()) orelse
     Option.isSome (#lookupStruct PolyML.globalNameSpace name)
  then raise Fail ("ordinary module imported extension " ^ name)
  else ())
  ["TraverseExt","Cond_rewrExt","OpeningExt","TravrulesExt",
   "simpExtLib","congExtLib","pureSimpsExt","boolSimpsExt",
   "combinSimpsExt","numSimpsExt","pred_setSimpsExt","listSimpsExt",
   "intReduceExt","integer_wordLibExt","realSimpsExt","SimpTracking",
   "simpMarkerTheory","simpMarkerLib","splitLib","SplitData",
   "splitPersistLib"]
val _ = new_theory "compiled_core_behavior"
fun same (a,b) = aconv (concl a) (concl b) andalso
  HOLset.equal (hypset a,hypset b)
fun apply ss tm = Conv.QCONV (SIMP_CONV ss []) tm
fun check label ss tm th = Paired.check label (same (apply ss tm,th))
fun constant name = (new_constant (name,bool); mk_const (name,bool))
val p = constant "core_p"
val q = constant "core_q"
val r = constant "core_r"
val s = constant "core_s"
val pq = ASSUME (mk_eq (p,q))
val rs = ASSUME (mk_eq (r,s))
val combined = CONJ pq rs
val pq = CONJUNCT1 combined
val rs = CONJUNCT2 combined
val named = rewrites_with_names [({Thy="bool",Name="core_source"},combined)]
val installed = pureSimps.pure_ss ++ named
val _ = check "source first expansion" installed p pq
val _ = check "source second expansion" installed r rs
val _ = check "qualified deletion wrong theory preserves"
  (installed -* ["min.core_source"]) p pq
val _ = check "qualified deletion removes first only"
  (installed -* ["bool.core_source.1"]) p (REFL p)
val _ = check "qualified deletion keeps second"
  (installed -* ["bool.core_source.1"]) r rs
val _ = check "source deletion removes all expansions"
  (installed -* ["core_source"]) r (REFL r)
val _ = check "source deletion is persistent" installed p pq
(* One shared bound for both maker expansions, consumed by this compiled
   simpset across applications; recompilation obtains a fresh allowance.
   Only one branch changes; no tagged BOUNDED assumption may escape. *)
val bounded = pureSimps.pure_ss ++ rewrites [Once combined]
val input = mk_conj (p,r)
val leftOnly = MK_COMB (AP_TERM conjunction pq,REFL r)
fun boundedResult () = apply bounded input
val first = boundedResult ()
val second = boundedResult ()
val fresh = apply (pureSimps.pure_ss ++ rewrites [Once combined]) input
val _ = Paired.check "bounded shared persistent allowance and recompile"
  (same (second,REFL input) andalso same (first,fresh) andalso
   same (first,leftOnly))
val zero = limit 0 installed
val _ = check "zero limit survives empty addition"
  (zero ++ empty_ssfrag) p (REFL p)
val _ = check "unlimit restores compiled rules" (unlimit zero) p pq
val _ = check "empty addition preserves rules and hypotheses"
  (installed ++ empty_ssfrag) p pq
val _ = Paired.check "empty addition records history"
  (length (ssfrags_of (installed ++ empty_ssfrag)) =
   length (ssfrags_of installed) + 1)
(* Full printer bytes are paired, not normalized or golden-updated. *)
val _ = List.app (fn width => Paired.observe
  ("pp.simpset." ^ Int.toString width)
  (String.toString (PP.pp_to_string width pp_simpset
    (limit 3 (installed ++ name_ss "core_empty" empty_ssfrag))))) [40,80]
val data : relsimpdata = {refl=boolTheory.EQ_REFL,
  trans=boolTheory.EQ_TRANS,weakenings=[],subsets=[],rewrs=[pq]}
val viaFrag = pureSimps.pure_ss ++ relsimp_ss data
val viaDirect = add_relsimp data pureSimps.pure_ss
val _ = check "relsimp fragment compiles reducer" viaFrag p pq
val _ = check "relsimp direct compiles reducer" viaDirect p pq
val _ = check "relsimp merge compiles reducer"
  (pureSimps.pure_ss ++ merge_ss [relsimp_ss data,empty_ssfrag]) p pq
val _ = Paired.check "relsimp history retained"
  (length (ssfrags_of viaFrag) = 2 andalso
   null (frag_rewrites (hd (ssfrags_of viaFrag))))
val info = valOf (TypeBase.fetch bool)
val info = TypeBasePure.put_simpls {rewrs=[pq,rs],convs=[]} info
val direct = tyi_to_ssdata info
val _ = check "TypeBase data compiles first rule"
  (pureSimps.pure_ss ++ direct) p pq
val _ = check "TypeBase data compiles second rule"
  (pureSimps.pure_ss ++ direct) r rs
val _ = TypeBase.register_update_fn (fn x =>
  if TypeBasePure.ty_name_of x = TypeBasePure.ty_name_of info then info else x)
val _ = TypeBase.write [info]
val lookup = type_ssfrag bool
val _ = Paired.check "TypeBase lookup preserves fragment payload"
  (frag_name lookup = frag_name direct andalso
   ListPair.allEq same (frag_rewrites lookup,frag_rewrites direct))
val _ = check "TypeBase lookup compiles" (pureSimps.pure_ss ++ lookup) p pq
val _ = Paired.observe "complete" "TASK16-compiled-core-behavior-v1"
