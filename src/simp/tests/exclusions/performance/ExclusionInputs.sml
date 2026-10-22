(* TASK17: public ordinary APIs only. Inputs and verification are untimed.
   Distinct constant keys avoid measuring an accidentally quadratic input net.
   ASSUME proofs intentionally retain their exact singleton hypothesis sets. *)
structure ExclusionInputs =
struct
  open HolKernel boolSyntax simpLib
  val _ = new_theory "task17_exclusion_performance"
  val sizes = [0,10,1000,10000]
  val labels = ["empty_list", "missing", "matching", "batched", "qualified",
    "partial", "literal_namespace", "literal_exact", "dproc_only", "mixed",
    "replay"]
  fun required b = if b then () else raise Fail "exclusion invariant"
  fun same (a,b) = aconv (concl a) (concl b) andalso
    HOLset.equal (hypset a,hypset b)
  fun rule i = let
    val name = "task17_c" ^ Int.toString i
    val _ = new_constant (name,bool)
  in ASSUME (mk_eq (mk_const (name,bool),T)) end
  val rules = List.tabulate (10000,rule)
  fun rname i = "task17_r" ^ Int.toString i
  fun nsname i = "task17_ns::r" ^ Int.toString i
  fun dpname i = "task17_dp" ^ Int.toString i
  val makerCalls = ref 0
  val collectorCalls = ref 0
  exception Context
  fun reducer name = Traverse.REDUCER
    {name=SOME name, initial=Context,
     addcontext=fn (ct,_) => (collectorCalls := !collectorCalls + 1; ct),
     apply=fn _ => fn _ => raise Conv.UNCHANGED}
  fun maker th = (makerCalls := !makerCalls + 1; [th])
  val makerFrag = SSFRAG {name=SOME "task17_maker", filter=SOME maker,
    rewrs=[], convs=[], ac=[], congs=[], dprocs=[reducer "task17_collector"]}
  fun named name rs = rewrites_with_names
    (ListPair.zip (map (fn i => {Thy="bool",Name=name i})
       (List.tabulate (length rs,I)),rs))
  type workload = {label:string, build:unit -> simpset,
    verify:simpset -> unit, makers:int, collectors:int}
  fun workloads n = let
    val rs = List.take (rules,n)
    val indices = List.tabulate (n,I)
    val data = name_ss "task17_data" (named rname rs)
    val net = empty_ss ++ data
    val ns = empty_ss ++ name_ss "task17_nsdata" (named nsname rs)
    (* At nonzero sizes one parent expands to distinct .1/.2 rewrites.
       Exactly n compiled rewrites remain; deleting .1 must keep .2 alive. *)
    fun expand (rw as (th,tag)) = case rs of
        first::second::_ =>
          if same (th,first) then [rw,(second,tag)] else [rw]
      | _ => [rw]
    val splitter = SSFRAG {name=SOME "task17_splitter",filter=SOME expand,
      rewrs=[],convs=[],ac=[],congs=[],dprocs=[]}
    val partialRs = if n = 0 then [] else hd rs :: List.drop (rs,2)
    val partial = empty_ss ++ splitter ++
      name_ss "task17_partialdata" (named rname partialRs)
    val dps = map (reducer o dpname) indices
    val dpfrag = SSFRAG {name=SOME "task17_dps", filter=NONE,
      rewrs=[], convs=[], ac=[], congs=[], dprocs=dps}
    val dp = empty_ss ++ dpfrag
    (* Installing net BEFORE dprocs avoids O(n) collector setup callbacks. *)
    val mixed = net ++ dpfrag
    val drop = named_rewrites "task17_drop" []
    val replay = ((empty_ss ++ makerFrag ++ data) -* ["task17_missing"])
                   ++ drop
    val _ = makerCalls := 0
    val _ = collectorCalls := 0
    val probes = if n = 0 then [] else [0,Int.min (1,n-1),n div 2,n-1]
    val batch = [0,n div 2,Int.max (0,n-1)]
    fun dpnames ss = map (#name o Traverse.dest_reducer)
      (#dprocs (traversedata_for_ss ss))
    fun checkProof removed source ss = let
      val {rewriters,travrules,relation,limit,...} = traversedata_for_ss ss
      (* Opaque dprocs are checked by exact ordered names separately. Project
         only the ordinary net for proof tests so an inert dproc's UNCHANGED
         does not mask rewriting. No production rewriter API is added. *)
      val conv = Conv.TRY_CONV (Conv.QCONV (Traverse.TRAVERSE
        {rewriters=rewriters,travrules=travrules,
         relation=relation,limit=limit,dprocs=[]} []))
      fun one i = let
        val rw = List.nth (rs,i)
        val tm = lhs (concl rw)
        val expected = if removed i then REFL tm else rw
      in required (same (Conv.QCONV conv tm,expected)) end
      val _ = List.app one probes
      val _ = required (same (Conv.QCONV conv T,REFL T))
      val _ = required (map frag_name (ssfrags_of ss) = source)
    in () end
    fun w label source pats removed dpremoved hasNet : workload = let
      val names = map frag_name (ssfrags_of source)
      val originalDP = dpnames source
      val expectedDP = List.filter (fn name => not (dpremoved name)) originalDP
      fun verify ss =
        (required (dpnames ss = expectedDP andalso
                   dpnames source = originalDP);
         if hasNet then
           (checkProof removed names ss;
            checkProof (fn _ => false) names source)
         else (checkProof (fn _ => true) names ss;
               checkProof (fn _ => true) names source))
    in {label=label,build=fn () => source -* pats, verify=verify,
        makers=0,collectors=0} end
    fun no _ = false
    fun first i = i = 0
    val replayNames = [SOME "task17_data",SOME "task17_maker"]
    val replayW : workload = {label="replay",
      build=fn () => remove_ssfrags ["task17_drop"] replay,
      verify=fn ss => (checkProof no replayNames ss;
        checkProof no (SOME "task17_drop" :: replayNames) replay;
        required (dpnames ss = [SOME "task17_collector"] andalso
                  dpnames replay = [SOME "task17_collector"])),
      makers=n,collectors=1}
    (* Original inputs must remain persistent through every operation. *)
    val _ = checkProof no [SOME "task17_data"] net
    val _ = checkProof no [SOME "task17_nsdata"] ns
  in
    [w "empty_list" mixed [] no no true,
     w "missing" mixed ["task17_missing"] no no true,
     w "matching" mixed [rname 0] first no true,
     w "batched" mixed (map rname batch @ ["task17_missing"])
       (fn i => Lib.mem i batch) no true,
     w "qualified" mixed ["bool." ^ rname 0] first no true,
     w "partial" partial [rname 0 ^ ".1"] first no true,
     (* Namespace-looking text is LITERAL, not a namespace selector. *)
     w "literal_namespace" ns ["task17_ns::"] no no true,
     w "literal_exact" ns [nsname 0] first no true,
     w "dproc_only" dp [dpname 0] no (fn s => s = SOME (dpname 0)) false,
     w "mixed" mixed [rname 0,dpname 0,"task17_missing"] first
       (fn s => s = SOME (dpname 0)) true,
     replayW]
  end
end
