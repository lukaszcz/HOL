(* Public provider contracts. Keep the ordinary oracle independent: the seed
   and TypeBase fold below follow BasicProvers.initial_simpset/init_state_of;
   the batch oracle follows its finaliser, not the current ambient srw_ss. *)
open HolKernel Parse boolLib boolSyntax testutils
val _ = trackedSimpDefaults.initial_recipe []
structure D = trackedSimpDefaults
structure S = simpExtLib
structure O = simpLib
val checks = ref 0
fun check label ok =
  (checks := !checks + 1; tprint label;
   if ok then OK () else die label)
fun same (a,b) = aconv (concl a) (concl b) andalso
  HOLset.equal (hypset a,hypset b)
fun thms xs ys = ListPair.allEq same (xs,ys)
fun run ss tm = QCONV (TRY_CONV (S.SIMP_CONV ss [])) tm
fun orun ss tm = QCONV (TRY_CONV (O.SIMP_CONV ss [])) tm
fun proof label ss tm th = check label (same (run ss tm,th))
fun compare label os ts inputs = List.app
  (fn tm => check label (same (orun os tm,run ts tm))) inputs
fun handles ss = S.rewrite_source_handles ss
fun identical (a,b) = ListPair.allEq S.same_rewrite_source
  (handles a,handles b)
fun names ss = map S.frag_name (S.ssfrags_of ss)
fun build steps = D.build {seed=fn () => pureSimpsExt.pure_ss,steps=steps}
fun set steps = D.value (build steps)
fun error f = case Exn.capture f () of
    Exn.Exn (HOL_ERR e) => SOME
      {origin_structure=Feedback.top_structure_of e,
       origin_function=Feedback.top_function_of e,
       message=Feedback.message_of e}
  | _ => NONE
exception Foreign of int
fun foreign f = case Exn.capture f () of
    Exn.Exn (Foreign 73) => true | _ => false
fun unchanged f = case Exn.capture f () of
    Exn.Exn Conv.UNCHANGED => true | _ => false
val _ = pairTheory.PAIR
val saved = Context.snapshot ()
val ordinaryBefore = BasicProvers.srw_ss ()
val ordinaryNames = map O.frag_name (O.ssfrags_of ordinaryBefore)
val input = ``(provider_f:bool -> bool) x``
val a = ASSUME ``(provider_f:bool -> bool) x = y``
val b = ASSUME ``(provider_f:bool -> bool) x = z``
val c = ASSUME ``(provider_g:bool -> bool) x = w``
val ka = {Thy="bool",Name="provider_a"}
val kb = {Thy="bool",Name="provider_b"}
val kc = {Thy="bool",Name="provider_c"}
val examples =
  [``(\x:bool. x /\ T) p``, ``~(p \/ q)``,
   ``p ==> (p /\ q)``, ``?x:bool. (x = p) /\ Q x``,
   ``I (p:bool)``, ``K (p:bool) q``, ``T = p``,
   ``Abbrev (x = (p /\ T))``, ``lab :- (p /\ T)``,
   ``hide (p /\ T)``, ``bool_CASE T (p:bool) q``]

(* Independent initial recipe, and the real BasicProvers initialization from
   its min state (no later theory declarations or arbitrary current SRW). *)
val ordinarySeed = List.foldl (fn (f,ss) => O.++ (ss,f)) O.empty_ss
  [pureSimps.PURE_ss,boolSimps.BOOL_ss,boolSimps.NOT_ss,
   boolSimps.CONG_ss,boolSimps.UNWIND_ss,combinSimps.COMBIN_ss,
   boolSimps.NORMEQ_ss,boolSimps.ABBREV_ss,boolSimps.LABEL_CONG_ss,
   boolSimps.HIDE_ss]
val seed = D.initial_seed ()
val _ = check "initial seed exact BasicProvers fragment order"
  (names seed = map O.frag_name (O.ssfrags_of ordinarySeed))
val _ = compare "initial seed complete ordinary theorem"
  ordinarySeed seed examples
val tyb = TypeBase.theTypeBase ()
val ordinaryInitialized = List.foldl
  (fn (tyi,ss) => (O.++ (ss,O.tyi_to_ssdata tyi)
                   handle HOL_ERR _ => ss))
  ordinarySeed (TypeBasePure.listItems tyb)
val initialized = D.value (D.build (D.initial_recipe (D.typebase_steps tyb)))
val fromMin = BasicProvers.merge_simpsets ["min"]
val _ = check "initialization fragment order matches actual min initialization"
  (names initialized = map O.frag_name (O.ssfrags_of fromMin) andalso
   names initialized = map O.frag_name (O.ssfrags_of ordinaryInitialized))
val _ = compare "initial recipe differential BasicProvers min initialization"
  fromMin initialized examples
val _ = compare "independent initial TypeBase fold complete theorem"
  ordinaryInitialized initialized examples
val freshSeed = D.initial_seed ()
val _ = check "initial_seed creates fresh native installation events"
  (not (null (handles seed)) andalso
   not (S.same_rewrite_source (hd (handles seed),hd (handles freshSeed))))
val _ = check "initial_recipe preserves supplied ordered steps"
  (case #steps (D.initial_recipe [D.LocalDelta (D.Add (ka,a)),
                                D.LocalDelta (D.Remove "provider_a")]) of
     [D.LocalDelta (D.Add (k,th)),D.LocalDelta (D.Remove n)] =>
       k=ka andalso same (th,a) andalso n="provider_a"
   | _ => false)

(* A maker sees the input order before compilation; a nonconfluent pair makes
   reversal observable in proofs as well as in the fragment ingredients. *)
val seen = ref ([] : thm list)
val maker = S.SSFRAG {name=SOME "provider-maker",
  filter=SOME (fn rw => (seen := !seen @ [#1 rw]; [rw])),
  rewrs=[],convs=[],congs=[],ac=[],dprocs=[]}
val batch = set [D.Fragment maker,
  D.TheoryBatch ("batch",[D.Add (ka,a),D.Remove "provider_missing",
                         D.Add (kb,b)])]
val _ = check "TheoryBatch reverses additions before installing named fragment"
  (thms (!seen) [b,a] andalso
   case S.ssfrags_of batch of
     f::_ => S.frag_name f = SOME "batch" andalso
             thms (S.frag_rewrites f) [b,a]
   | _ => false)
val ordinaryBatch = O.++ (pureSimps.pure_ss,
  O.named_rewrites_with_names "batch" [(kb,b),(ka,a)])
val _ = compare "TheoryBatch nonconfluent priority matches finaliser"
  ordinaryBatch batch [input]
val forward = O.++ (pureSimps.pure_ss,
  O.named_rewrites_with_names "batch" [(ka,a),(kb,b)])
val _ = check "batch fixture distinguishes reversed addition priority"
  (not (same (orun forward input,orun ordinaryBatch input)))
val removed = set [D.TheoryBatch ("removed",
  [D.Remove "provider_a",D.Add (ka,a),D.Add (kb,b),
   D.Remove "provider_b",D.Add (kc,c)])]
val _ = proof "batch removals occur after all additions" removed input
  (REFL input)
val _ = proof "unremoved batch source retains hypotheses" removed
  (lhs (concl c)) c
val _ = check "empty batch still installs its named fragment"
  (List.exists (fn n => n=SOME "empty-batch")
    (names (set [D.TheoryBatch ("empty-batch",[])])))
(* Distinct malformed strict names make removal order observable: if removals
   reverse, the second error wins. Also detects grouped -* calls. *)
val _ = check "TheoryBatch removals retain supplied order"
  (case error (fn () => set [D.TheoryBatch ("bad-removals",
    [D.Remove "provider_bad_first.rule",
     D.Remove "provider_bad_second.rule"])]) of
     SOME {message,...} =>
       String.isSubstring "provider_bad_first" message
   | NONE => false)
val localSet = set [D.LocalDelta (D.Add (ka,a)),
  D.LocalDelta (D.Remove "provider_a"),D.LocalDelta (D.Add (kb,b))]
val _ = proof "LocalDelta applies Add/Remove in declaration order"
  localSet input b
val localRemoved = set [D.LocalDelta (D.Add (ka,a)),
                        D.LocalDelta (D.Remove "provider_a")]
val _ = proof "LocalDelta Remove deletes installed rule"
  localRemoved input (REFL input)
val frag = S.named_rewrites "explicit-fragment" [a]
val _ = proof "Fragment installs caller's typed ingredients"
  (set [D.Fragment frag]) input a

(* Ordered TypeBase steps do not consult or mutate ambient TypeBase. *)
val boolInfo = valOf (TypeBase.fetch bool)
val pairInfo = valOf (TypeBase.fetch
  (mk_thy_type {Thy="pair",Tyop="prod",Args=[bool,bool]}))
fun info base rw = TypeBasePure.put_simpls {rewrs=[rw],convs=[]} base
val boolCustom = info boolInfo a
val pairCustom = info pairInfo b
val privateBase = TypeBasePure.insert
  (TypeBasePure.insert TypeBasePure.empty pairCustom) boolCustom
val orderedInfo = TypeBasePure.listItems privateBase
val steps = D.typebase_steps privateBase
val _ = check "typebase_steps preserves listItems order and payload"
  (ListPair.allEq
    (fn (D.TypeInfo i,j) => TypeBasePure.ty_name_of i =
         TypeBasePure.ty_name_of j andalso
         thms (#rewrs (TypeBasePure.simpls_of i))
              (#rewrs (TypeBasePure.simpls_of j))
      | _ => false) (steps,orderedInfo) andalso
   null (D.typebase_steps TypeBasePure.empty))
val typeSet = set steps
val typeOracle = List.foldl
  (fn (i,ss) => O.++ (ss,O.tyi_to_ssdata i))
  pureSimps.pure_ss orderedInfo
val _ = compare "TypeInfo order differential with independent initial fold"
  typeOracle typeSet [input]
val _ = proof "TypeInfo installs supplied simpls not ambient bool simpls"
  (set [D.TypeInfo boolCustom]) input a
val _ = check "TypeInfo batch precedes later explicit Update"
  (same (run (set (steps @ [D.Update S.clear_rules])) input,
         REFL input))
val invalidInfo = TypeBasePure.mk_nondatatype_info
  (alpha,{nchotomy=NONE,induction=NONE,size=NONE,encode=NONE})
val _ = proof "TypeInfo ignores construction HOL_ERR and keeps earlier rules"
  (set [D.LocalDelta (D.Add (ka,a)),D.TypeInfo invalidInfo]) input a
(* Faults in installation, not conversion invocation. Only TypeInfo catches
   HOL_ERR; the same maker must still reject Fragment/LocalDelta/Update. *)
fun badMaker exn = S.SSFRAG {name=SOME "throwing-maker",
  filter=SOME (fn _ => raise exn),rewrs=[],convs=[],congs=[],ac=[],
  dprocs=[]}
val boom = Feedback.mk_HOL_ERR "provider-test" "maker" "sentinel"
val caught = set [D.Fragment (badMaker boom),D.TypeInfo boolCustom,
                  D.Update (fn _ => pureSimpsExt.pure_ss),
                  D.LocalDelta (D.Add (kc,c))]
val _ = proof "TypeInfo ignores installation HOL_ERR and continues"
  caught (lhs (concl c)) c
val _ = check "TypeInfo keeps original set when installation fails"
  (null (handles (set [D.Fragment (badMaker boom),
                       D.TypeInfo boolCustom])))
val _ = check "TypeInfo propagates foreign installation exception"
  (foreign (fn () => set [D.Fragment (badMaker (Foreign 73)),
                          D.TypeInfo boolCustom]))
val _ = check "LocalDelta does not swallow installation HOL_ERR"
  (Option.isSome (error (fn () => set [D.Fragment (badMaker boom),
                                      D.LocalDelta (D.Add (ka,a))])))
val _ = check "Fragment does not swallow installation HOL_ERR"
  (Option.isSome (error (fn () => set [D.Fragment (badMaker boom),
                                      D.Fragment frag])))
val _ = check "TheoryBatch does not swallow installation HOL_ERR"
  (Option.isSome (error (fn () => set [D.Fragment (badMaker boom),
     D.TheoryBatch ("throwing-batch",[D.Add (ka,a)])])))
val _ = check "TheoryBatch propagates foreign installation exception"
  (foreign (fn () => set [D.Fragment (badMaker (Foreign 73)),
     D.TheoryBatch ("throwing-batch",[D.Add (ka,a)])]))
val _ = check "LocalDelta propagates foreign installation exception"
  (foreign (fn () => set [D.Fragment (badMaker (Foreign 73)),
                          D.LocalDelta (D.Add (ka,a))]))
val _ = check "Fragment propagates foreign installation exception"
  (foreign (fn () => set [D.Fragment (badMaker (Foreign 73)),
                          D.Fragment frag]))
val _ = check "TypeInfo propagates installation UNCHANGED"
  (unchanged (fn () => set [D.Fragment (badMaker Conv.UNCHANGED),
                            D.TypeInfo boolCustom]))
val updates = ref ([] : int list)
fun update n ss = (updates := !updates @ [n]; ss)
val _ = set [D.Update (update 1),D.LocalDelta (D.Add (ka,a)),
             D.Update (update 2)]
val _ = check "Update closures run once in recipe order" (!updates=[1,2])
val _ = check "Update explicitly propagates HOL_ERR"
  (case error (fn () => set [D.Update (fn _ => raise boom)]) of
     SOME {origin_structure,origin_function,message} =>
       origin_structure="provider-test" andalso origin_function="maker"
       andalso message="sentinel"
   | NONE => false)
val _ = check "Update explicitly propagates foreign exception"
  (foreign (fn () => set [D.Update (fn _ => raise Foreign 73)]))
val _ = check "build Update UNCHANGED is not map's no-op convention"
  (unchanged (fn () => set [D.Update (fn _ => raise Conv.UNCHANGED)]))
val seedCalls = ref 0
val _ = D.build {seed=fn () => (seedCalls := !seedCalls+1;
                              pureSimpsExt.pure_ss),steps=[]}
val _ = check "build evaluates seed exactly once" (!seedCalls=1)
val _ = check "build propagates seed HOL_ERR"
  (Option.isSome (error (fn () => D.build
     {seed=fn () => raise boom,steps=[]})))
val _ = check "build propagates seed foreign exception"
  (foreign (fn () => D.build
     {seed=fn () => raise Foreign 73,steps=[]}))

(* Projection is shallow, even for installed maker-generated bounded sources.
   A shared seed intentionally shares live and exhausted controls. *)
val makerCalls = ref 0
val counting = S.SSFRAG {name=SOME "counting-maker",
  filter=SOME (fn rw => (makerCalls := !makerCalls+1; [rw])),
  rewrs=[],convs=[],congs=[],ac=[],dprocs=[]}
val boundedFrag = S.named_rewrites "quota" [BoundedRewrites.Ntimes a 2]
val quota = build [D.Fragment counting,D.Fragment boundedFrag]
val quotaSS = D.value quota
val callsAtBuild = !makerCalls
val _ = check "fixture maker actually runs during explicit preparation"
  (callsAtBuild > 0)
val reuse = D.build {seed=fn () => quotaSS,steps=[]}
val _ = proof "shared seed first live allowance" (D.value reuse) input a
val _ = proof "shared seed second live allowance" quotaSS input a
val exhausted = D.build {seed=fn () => quotaSS,steps=[]}
val _ = proof "build does not reset an exhausted shared seed"
  (D.value exhausted) input (REFL input)
val _ = check "seed reuse retains native source identity"
  (identical (quotaSS,D.value reuse) andalso
   identical (quotaSS,D.value exhausted))
val _ = List.app (fn _ =>
  (ignore (D.value quota); ignore (D.get_of (D.install quota saved));
   ignore (S.traversedata_for_ss quotaSS);
   ignore (S.xtraversedata_for_ss quotaSS);
   ignore (S.traverseconfig_for_ss quotaSS);
   ignore (S.rewrite_sources quotaSS []);
   ignore (S.rewrite_source_handles quotaSS))) [1,2,3]
val _ = check "all provider and traversal projections never rerun maker"
  (!makerCalls=callsAtBuild)
val _ = proof "projections never refresh exhausted controls"
  quotaSS input (REFL input)
val freshQuota = build [D.Fragment counting,D.Fragment boundedFrag]
val _ = check "fresh build installs independent bounded sources"
  (not (identical (quotaSS,D.value freshQuota)))
val _ = proof "fresh construction gets fresh allowance"
  (D.value freshQuota) input a

(* Provider map is explicit; only UNCHANGED is absorbed. *)
val pa = build [D.LocalDelta (D.Add (ka,a))]
val pb = D.map (fn ss => S.-* (ss,["provider_a"])) pa
val _ = proof "map transforms returned provider" (D.value pb) input
  (REFL input)
val _ = proof "map leaves original provider intact" (D.value pa) input a
val nochange = D.map (fn _ => raise Conv.UNCHANGED) quota
val _ = check "map UNCHANGED retains sources and controls"
  (identical (D.value nochange,quotaSS))
val _ = proof "map UNCHANGED retains spent quota" (D.value nochange)
  input (REFL input)
val _ = check "map propagates HOL_ERR"
  (Option.isSome (error (fn () => D.map (fn _ => raise boom) pa)))
val _ = check "map propagates foreign exception"
  (foreign (fn () => D.map (fn _ => raise Foreign 73) pa))

(* Context operations are opt-in. A snapshot carries provider and installed
   source identities together; it is not a deferred recipe. *)
val absent = saved
val _ = check "get_of absent does not manufacture a provider"
  (case D.get_of absent of NONE => true | _ => false)
val callback = ref false
fun missing origin f = check ("absent provider precise " ^ origin ^ " error")
  (case error f of
     SOME {origin_structure,origin_function,message} =>
       origin_structure="trackedSimpDefaults" andalso
       origin_function=origin andalso
       message=("Unprepared tracked default provider; " ^
                "explicitly build and install one")
   | NONE => false)
val _ = missing "map_of" (fn () => D.map_of
  (fn ss => (callback := true; ss)) absent)
val _ = Context.restore absent
val _ = missing "with_updates" (fn () => D.with_updates
  (fn ss => (callback := true; ss)) (fn () => callback := true) ())
val _ = check "absent operations never call update or body" (not (!callback))
val ca = D.install pa absent
val cb = D.install pb ca
fun at c = D.value (valOf (D.get_of c))
val _ = proof "install returns context containing prepared provider"
  (at ca) input a
val _ = check "install is pure with respect to ambient and old snapshots"
  (not (Option.isSome (D.get_of (Context.snapshot ()))) andalso
   not (Option.isSome (D.get_of absent)))
val _ = proof "second install replaces only returned context" (at cb)
  input (REFL input)
val _ = proof "first snapshot survives replacement" (at ca) input a
val mapped = D.map_of (fn ss => S.-* (ss,["provider_a"])) ca
val _ = proof "map_of updates explicit context" (at mapped) input
  (REFL input)
val _ = proof "map_of does not alter input snapshot" (at ca) input a
val _ = check "map_of UNCHANGED retains source identity"
  (identical (at ca,at (D.map_of (fn _ => raise Conv.UNCHANGED) ca)))
val _ = check "map_of propagates HOL_ERR"
  (Option.isSome (error (fn () => D.map_of (fn _ => raise boom) ca)))
val _ = check "map_of propagates foreign exception"
  (foreign (fn () => D.map_of (fn _ => raise Foreign 73) ca))
val _ = Context.restore ca
fun current () = at (Context.snapshot ())
fun drop ss = S.-* (ss,["provider_a"])
val windowSnapshot = ref (NONE : Context.t option)
val result = D.with_updates drop (fn n =>
  (proof "window exposes temporary provider" (current ()) input (REFL input);
   windowSnapshot := SOME (Context.snapshot ()); n+1)) 41
val _ = check "with_updates returns body result" (result=42)
val _ = proof "successful window rewinds provider" (current ()) input a
val _ = proof "snapshot taken in window keeps temporary provider"
  (at (valOf (!windowSnapshot))) input (REFL input)
val _ = check "HOL_ERR from window body is preserved"
  (Option.isSome (error (fn () => D.with_updates drop
     (fn () => raise boom) ())))
val _ = proof "HOL_ERR window rewinds provider" (current ()) input a
val _ = check "foreign exception from window body is preserved"
  (foreign (fn () => D.with_updates drop
     (fn () => raise Foreign 73) ()))
val _ = proof "foreign exception window rewinds provider" (current ()) input a
val _ = check "window body UNCHANGED propagates"
  (unchanged (fn () => D.with_updates drop
    (fn () => raise Conv.UNCHANGED) ()))
val _ = proof "UNCHANGED body still rewinds provider" (current ()) input a
val _ = check "window update HOL_ERR never enters body"
  (Option.isSome (error (fn () => D.with_updates (fn _ => raise boom)
     (fn () => callback := true) ())) andalso not (!callback))
val _ = check "window update foreign exception never enters body"
  (foreign (fn () => D.with_updates (fn _ => raise Foreign 73)
     (fn () => callback := true) ()) andalso not (!callback))
val _ = proof "failed update leaves installed provider" (current ()) input a
val _ = D.with_updates (fn _ => raise Conv.UNCHANGED)
  (fn () => proof "window UNCHANGED executes body with original provider"
    (current ()) input a) ()
val _ = D.with_updates drop (fn () =>
  (D.with_updates (fn _ => D.value pa)
     (fn () => proof "nested window sees inner provider"
       (current ()) input a) ();
   proof "nested window restores outer provider"
     (current ()) input (REFL input))) ()
val _ = proof "nested windows restore original provider" (current ()) input a
(* Slot windows restore only their own slot, not unrelated Context writes. *)
val other = Context.Data.new
  {name="provider-test.other",empty=0,pp=Int.toString}
val _ = D.with_updates drop (fn () => Context.Data.write other 9) ()
val _ = check "window does not rewind unrelated Context slots"
  (Context.Data.get other (Context.snapshot ())=9)
val _ = Context.restore (D.install quota (Context.snapshot ()))
val spentSnapshot = Context.snapshot ()
val _ = D.with_updates (fn ss => ss) (fn () =>
  proof "window shares exhausted installed controls" (current ()) input
    (REFL input)) ()
val _ = Context.restore ca
val _ = Context.restore spentSnapshot
val _ = check "Context restore keeps provider source identities"
  (identical (current (),quotaSS))
val _ = proof "Context restore does not reconstruct exhausted provider"
  (current ()) input (REFL input)

(* Slot rollback restores the binding, not the mutable allowances inside it.
   Capturing a context before spending must not turn it into a quota reset. *)
val windowQuota = build [D.Fragment
  (S.rewrites [BoundedRewrites.Ntimes a 3])]
val _ = Context.restore (D.install windowQuota (Context.snapshot ()))
val liveSnapshot = Context.snapshot ()
val _ = D.with_updates (fn ss => ss) (fn () =>
  proof "successful window spends shared live allowance"
    (current ()) input a) ()
val _ = check "HOL_ERR window spends allowance before propagating"
  (Option.isSome (error (fn () => D.with_updates (fn ss => ss)
    (fn () => (proof "HOL_ERR body sees remaining allowance"
      (current ()) input a; raise boom)) ())))
val _ = check "foreign window spends allowance before propagating"
  (foreign (fn () => D.with_updates (fn ss => ss)
    (fn () => (proof "foreign body sees remaining allowance"
      (current ()) input a; raise Foreign 73)) ()))
val _ = proof "all window exits retain consumed controls"
  (current ()) input (REFL input)
val _ = Context.restore liveSnapshot
val _ = check "live snapshot restore retains exact source identities"
  (identical (current (),D.value windowQuota))
val _ = proof "pre-spend snapshot restore does not reset allowance"
  (current ()) input (REFL input)

val _ = Context.with_context ca (fn () =>
  (proof "pinned context exposes its own installed provider"
     (current ()) input a;
   Context.restore (D.map_of drop (Context.snapshot ()));
   proof "pinned map changes only pinned provider"
     (current ()) input (REFL input);
   D.with_updates (fn _ => D.value pa)
     (fn () => proof "window operates inside pinned context"
       (current ()) input a) ();
   proof "window restores pinned provider"
     (current ()) input (REFL input))) ()
val _ = proof "pin release keeps ambient provider and exhausted allowance"
  (current ()) input (REFL input)
val _ = check "pin release preserves ambient source identity"
  (identical (current (),D.value windowQuota))

(* Ordinary SRW has neither been mirrored nor changed by any provider API.
   Conversely a local ordinary update must not appear in this provider. *)
val _ = check "provider APIs leave ordinary SRW fragment list unchanged"
  (map O.frag_name (O.ssfrags_of (BasicProvers.srw_ss ())) = ordinaryNames)
val _ = List.app (fn tm => check
  "provider APIs leave ordinary SRW complete proofs unchanged"
  (same (orun ordinaryBefore tm,orun (BasicProvers.srw_ss ()) tm)))
  (input :: examples)
val _ = check "ordinary SRW never acquired provider-only rule"
  (same (orun (BasicProvers.srw_ss ()) input,orun ordinaryBefore input))
val _ = BasicProvers.with_simpset_updates
  (fn ss => O.++ (ss,O.rewrites [c]))
  (fn () =>
    (proof "ordinary SRW window is not automatically mirrored"
       (current ()) (lhs (concl c)) (REFL (lhs (concl c)));
     proof "initial_seed does not import ordinary SRW window updates"
       (D.initial_seed ()) (lhs (concl c)) (REFL (lhs (concl c))))) ()
val _ = check "provider retrieval remains inert after all Context operations"
  (!makerCalls=callsAtBuild+1)

(* Executable static boundaries: existing ordinary compiled objects cannot
   enter any recipe input, even as an ordinary update closure. *)
fun rejected name = let
  val rejected = (PolyML.use ("negative/" ^ name ^ ".ML"); false)
    handle Fail msg =>
      if String.isSubstring "Static Errors" msg then true
      else raise Fail ("nonstatic failure: " ^ msg)
in check ("static rejection: " ^ name) rejected end
val _ = List.app rejected ["ordinary-seed","ordinary-fragment",
                           "ordinary-update"]
val _ = Context.restore saved
val _ = print ("TRACKED_DEFAULTS_COMPLETE checks=" ^
               Int.toString (!checks) ^ "\n")
val _ = OS.Process.exit OS.Process.success
