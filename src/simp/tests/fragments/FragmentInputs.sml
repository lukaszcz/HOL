(* Public baseline APIs only. No casts or extension instrumentation. *)
structure FragmentInputs =
struct
  open HolKernel boolSyntax Drule simpLib
  val sizes = [0,1,10,100,1000,10000]
  fun required b = if b then () else raise Fail "fragment probe invariant"
  fun sameTh (a,b) =
    aconv (concl a) (concl b) andalso HOLset.equal (hypset a,hypset b)
  fun sameList (a,b) = ListPair.allEq sameTh (a,b)
  fun rule i = CONJUNCT1 (SPEC
    (mk_var ("fragment_x" ^ Int.toString i,bool)) boolTheory.AND_CLAUSES)
  val rules = List.tabulate (10000,rule)
  fun thname i = {Thy="",Name="fragment_rule" ^ Int.toString i}
  val extra = rule 10001
  val acPair = (boolTheory.CONJ_ASSOC,boolTheory.CONJ_SYM)
  val result = mk_var ("fragment_target",bool)
  val input = lhs (concl (CONJUNCT1 (SPEC result boolTheory.AND_CLAUSES)))
  val boolInfo = valOf (TypeBase.fetch bool)
  val typeRules = ref ([]:thm list)
  (* TypeBase.write normally adds standard simplifications. Its public update
     hook runs after that stage and gives this isolated probe exact counts. *)
  val _ = TypeBase.register_update_fn (fn info =>
    if TypeBasePure.ty_name_of info = TypeBasePure.ty_name_of boolInfo then
      TypeBasePure.put_simpls {rewrs= !typeRules,convs=[]} info else info)
  type workload = {label:string, build:unit -> ssfrag,
                   expected:thm list, name:string option, ac:bool}
  fun workloads n = let
    val rs = List.take (rules,n)
    val nrs = ListPair.zip (List.tabulate (n,thname),rs)
    val raw = map (fn (nm,th) => (SOME nm,th)) nrs
    val frag = rewrites rs
    val named = name_ss "A" frag
    val acs = List.tabulate (n,fn _ => acPair)
    val acfrag = ac_ss acs
    val info = TypeBasePure.put_simpls {rewrs=rs,convs=[]} boolInfo
    (* An isolated child owns this registry. Lookup has exactly n rewrites;
       datatype creation and TypeBase mutation are outside all timers. *)
    val _ = typeRules := rs
    val _ = TypeBase.write [info]
    fun w label build expected name ac : workload =
      {label=label,build=build,expected=expected,name=name,ac=ac}
  in
    [w "rewrites" (fn () => rewrites rs) rs NONE false,
     w "rewrites_with_names" (fn () => rewrites_with_names nrs) rs NONE false,
     w "named_rewrites" (fn () => named_rewrites "A" rs) rs (SOME "A") false,
     w "named_rewrites_with_names"
       (fn () => named_rewrites_with_names "A" nrs) rs (SOME "A") false,
     w "SSFRAG" (fn () => SSFRAG
       {name=NONE,rewrs=raw,convs=[],ac=[],filter=NONE,dprocs=[],congs=[]})
       rs NONE false,
     w "update" (fn () => ssf_upd_rewrs List.rev named)
       (List.rev rs) (SOME "A") false,
     w "add_named_rwt" (fn () => add_named_rwt (thname n,extra) frag)
       (extra::rs) NONE false,
     w "merge" (fn () => merge_ss [frag,empty_ssfrag]) rs NONE false,
     w "merge_duplicate" (fn () => merge_ss [frag,frag]) (rs @ rs) NONE false,
     w "merge_named" (fn () => merge_ss [named,name_ss "B" frag])
       (rs @ rs) (SOME "A, B") false,
     w "named_merge" (fn () => named_merge_ss "C" [frag,frag])
       (rs @ rs) (SOME "C") false,
     w "ac_create" (fn () => ac_ss acs) [] NONE (n > 0),
     w "ac_merge" (fn () => merge_ss [acfrag,acfrag]) [] NONE (n > 0),
     (* tyi_to_ssdata intentionally reverses TypeBase's rewrite list. *)
     w "type_create" (fn () => tyi_to_ssdata info)
       (List.rev rs) (SOME "Datatype min$bool") false,
     w "type_lookup" (fn () => type_ssfrag bool)
       (List.rev rs) (SOME "Datatype min$bool") false]
  end
  fun verify ({expected,name,...}:workload) f =
    required (frag_name f = name andalso sameList (frag_rewrites f,expected))
  fun proof ({expected,ac,...}:workload) f = let
    val swapped = mk_conj (result,T)
    val (acInput,acOther) =
      if Cond_rewr.ac_term_ord (input,swapped) = GREATER
      then (input,swapped) else (swapped,input)
    val tm = if ac then acInput else input
    val th = Conv.QCONV (SIMP_CONV (empty_ss ++ f) []) tm
    val (l,r) = dest_eq (concl th)
    val want = if ac then acOther
               else if null expected then tm else result
  in required (aconv l tm andalso aconv r want andalso null (hyp th)) end
  (* Equal-arity roots subtract shared inputs, callbacks and static module
     dependencies. This is retained graph words, NOT cumulative allocation. *)
  fun graph w f = PolyML.objSize (w,empty_ssfrag,f) -
                  PolyML.objSize (w,empty_ssfrag,empty_ssfrag)
end
