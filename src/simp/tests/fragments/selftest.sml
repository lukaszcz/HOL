(* Maintained behavior and retained-graph fixture, run through testutils. *)
open HolKernel boolSyntax Drule simpLib Paired FragmentInputs
val _ = new_theory "fragment_contracts"
fun csv ns = String.concatWith "," (map Int.toString ns)
val _ = List.app (fn n => let
  fun sample (w as {label,build,...}:workload) = let
    val f = build ()
    val _ = verify w f
    val _ = proof w f
    val words = graph w f
    val _ = Paired.observe ("graph." ^ label) (csv [n,words])
  in Paired.check (label ^ " " ^ Int.toString n) (words >= 0) end
  val _ = List.app sample (workloads n)
  (* One fresh ref per element: objSize sensitivity/units control. *)
  val cells = List.tabulate (n,fn i => ref i)
  val words = PolyML.objSize ((),cells,()) - PolyML.objSize ((),[],())
  val _ = Paired.observe "control.cells" (csv [n,words])
in Paired.check ("cells " ^ Int.toString n) (words = 5 * n) end) sizes

val _ = Paired.check "empty" (frag_name empty_ssfrag = NONE andalso
  null (frag_rewrites empty_ssfrag) andalso
  frag_name (merge_ss []) = NONE andalso null (frag_rewrites (merge_ss [])))
val calls = ref 0
val source = named_rewrites "update" [extra]
val changed = ssf_upd_rewrs (fn rs =>
  (calls := !calls + 1; required (length rs = 1); [])) source
val _ = Paired.check "update callback and persistence"
  (!calls = 1 andalso frag_name changed = SOME "update" andalso
   null (frag_rewrites changed) andalso sameList (frag_rewrites source,[extra]))
val _ = Paired.check "update exception identity"
  (let exception Callback
   in ((ssf_upd_rewrs (fn _ => raise Callback) source; false)
       handle Callback => true) end)
val _ = Paired.check "anonymous registration rejects"
  ((register_frag (rewrites []); false) handle HOL_ERR _ => true)
val registered = register_frag (named_rewrites "TASK15_registry" [extra])
val _ = Paired.check "named registration"
  (case lookup_named_frag "TASK15_registry" of
     SOME f => frag_name f = frag_name registered andalso
               sameList (frag_rewrites f,[extra]) andalso
               Lib.mem "TASK15_registry" (all_named_frags ())
   | NONE => false)
val _ = register_frag (named_rewrites "TASK15_registry" [])
val _ = Paired.check "named registration replacement"
  (case lookup_named_frag "TASK15_registry" of
     SOME f => null (frag_rewrites f) | NONE => false)
val (yes,no) = partition_ssfrags ["update"]
  [source,rewrites [],name_ss "other" empty_ssfrag,source]
val _ = Paired.check "partition preserves duplicates and order"
  (map frag_name yes = [SOME "update",SOME "update"] andalso
   map frag_name no = [NONE,SOME "other"])
(* Name metadata must survive SSFRAG/update/merge, not merely frag_rewrites. *)
val f = SSFRAG {name=NONE,convs=[],ac=[],filter=NONE,dprocs=[],congs=[],
  rewrs=[(SOME {Thy="",Name="TASK15_named"},extra)]}
val f = merge_ss [ssf_upd_rewrs I f,empty_ssfrag]
val ss = empty_ss ++ f
val th = Conv.QCONV (SIMP_CONV (ss -* ["TASK15_named"]) []) input
val _ = Paired.check "rewrite name survives update and merge"
  (sameTh (th,REFL input))
val _ = Paired.check "missing TypeBase rejects"
  ((type_ssfrag (mk_vartype "'task15_missing"); false)
   handle HOL_ERR _ => true)
val _ = Paired.observe "complete" "TASK15-fragments-v1"
