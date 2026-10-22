(* Supplemental legacy-only routes, loaded by the compatibility Paired driver.
   No extension APIs, instrumentation, or weakened theorem checks. *)
open HolKernel boolSyntax Drule simpLib Paired
val _ = new_theory "fragment_routes"
fun sameTh (a,b) =
  aconv (concl a) (concl b) andalso HOLset.equal (hypset a,hypset b)
fun sameThs (xs,ys) = ListPair.allEq sameTh (xs,ys)
fun rule tm = CONJUNCT1 (SPEC tm boolTheory.AND_CLAUSES)
val p = mk_var ("route_p",bool)
val q = mk_var ("route_q",bool)
val r1 = rule p
val r2 = ADD_ASSUM (mk_var ("route_h",bool)) (rule q)
val acPair = (boolTheory.CONJ_ASSOC,boolTheory.CONJ_SYM)
fun frag name filter ac rs ds cs = SSFRAG
  {name=name,filter=filter,ac=ac,rewrs=rs,dprocs=ds,convs=cs,congs=[]}
fun proof label ss rw = let
  val tm = lhs (concl rw)
  val th = Conv.QCONV (SIMP_CONV ss []) tm
  val equal = sameTh (th,rw)
  fun describe name theorem =
    print (name ^ " conclusion: " ^
           String.toString (Parse.term_to_string (concl theorem)) ^
           "\n" ^ name ^ " hypotheses: [" ^
           String.concatWith ", "
             (map (String.toString o Parse.term_to_string) (hyp theorem)) ^
           "]\n")
  val _ = if equal then () else
    (print ("Proof mismatch: " ^ label ^ "\n");
     describe "actual" th; describe "expected" rw)
in Paired.check label equal end
fun unchanged label ss tm =
  Paired.check label
    (sameTh (Conv.QCONV (SIMP_CONV ss []) tm,REFL tm))

(* Reducers remain opaque: their names must print without running collectors
   or apply functions, including anonymous and repeated named reducers. *)
exception Opaque
val opaqueCalls = ref 0
fun opaque name = Traverse.REDUCER
  {name=name,initial=Opaque,
   addcontext=fn _ => (opaqueCalls := !opaqueCalls + 1; raise Opaque),
   apply=fn _ => fn _ => (opaqueCalls := !opaqueCalls + 1; raise Opaque)}
val key = lhs (concl r1)
fun inert _ _ _ = raise Conv.UNCHANGED
val keyed : convdata =
  {name="route_keyed",key=SOME ([p],key),trace=2,conv=inert}
val unkeyed : convdata =
  {name="route_unkeyed",key=NONE,trace=2,conv=inert}
val raw = frag (SOME "route_named") NONE [acPair]
  [(SOME {Thy="bool",Name="route_rule"},r1),(NONE,r2)]
  [opaque (SOME "route_dp"),opaque NONE,opaque (SOME "route_dp")]
  [keyed,unkeyed]
val updated = ssf_upd_rewrs List.rev raw
val merged = merge_ss [updated,name_ss "route_tail" (rewrites [r1]),updated]
val anonymous = frag NONE NONE []
  [(SOME {Thy="",Name="route_local"},r2),(NONE,r1)]
  [opaque NONE] [keyed]
fun rendering label f = List.app (fn width =>
  Paired.observe ("pp." ^ label ^ "." ^ Int.toString width)
    (String.toString (PP.pp_to_string width pp_ssfrag f))) [40,80]
val _ = rendering "raw" raw
val _ = rendering "updated" updated
val _ = rendering "merged" merged
val _ = rendering "anonymous" anonymous
val _ = Paired.check "printing is opaque and persistent"
  (!opaqueCalls = 0 andalso sameThs (frag_rewrites raw,[r1,r2]) andalso
   sameThs (frag_rewrites updated,[r2,r1]) andalso
   sameThs (frag_rewrites merged,[r2,r1,r1,r2,r1]) andalso
   frag_name merged = SOME "route_named, route_tail, route_named" andalso
   frag_name anonymous = NONE)
val _ = proof "updated proof and hypotheses"
  (empty_ss ++ ssf_upd_rewrs (fn _ => [(NONE,r2)]) (rewrites [r1])) r2
val _ = proof "merged proof and hypotheses"
  (empty_ss ++ merge_ss [rewrites [],rewrites [r2],rewrites []]) r2

(* History is newest-first, retains duplicate named AND anonymous fragments.
   Names alone use Lib.mk_set's last-occurrence ordering, not sorted names. *)
val a1 = named_rewrites "route_A" [r1]
val a2 = named_rewrites "route_A" [r2]
val b = named_rewrites "route_B" []
val anon = rewrites [r1]
val history = mk_simpset [a1,anon,b,anon,a2]
val expectedHistory = [a2,anon,b,anon,a1]
fun sameFrag (a,b) = frag_name a = frag_name b andalso
  sameThs (frag_rewrites a,frag_rewrites b)
fun historyIs ss fs = ListPair.allEq sameFrag (ssfrags_of ss,fs)
fun historyText ss = String.concatWith ","
  (map (fn f => case frag_name f of NONE => "<anon>" | SOME n => n)
       (ssfrags_of ss))
val _ = Paired.observe "history.fragments" (historyText history)
val _ = Paired.observe "history.names"
  (String.concatWith "," (ssfrag_names_of history))
val _ = Paired.check "history retains duplicates and name order"
  (historyIs history expectedHistory andalso
   ssfrag_names_of history = ["route_B","route_A"])
val deleted = history -* ["route_no_such_rule"]
val _ = Paired.check "deletion event is not a fragment"
  (historyIs deleted expectedHistory andalso
   ssfrag_names_of deleted = ["route_B","route_A"])

(* Installation event logs use the ORIGINAL public filter mechanism. A
   fragment's filter affects subsequent installations, not its own rewrites.
   Collectors see the original theorem list, not AC or maker expansions. *)
exception Collector
exception LaterMaker
exception ThrowingMaker
val events = ref ([] : string list)
val contexts = ref ([] : thm list list)
fun record s = events := !events @ [s]
fun clear () = (events := []; contexts := [])
val (ac1,ac2,ac3) = Drule.MK_AC_LCOMM acPair
fun label th =
  if sameTh (th,r1) then "r1"
  else if sameTh (th,r2) then "r2"
  else if sameTh (th,ac1) then "ac1"
  else if sameTh (th,ac2) then "ac2"
  else if sameTh (th,ac3) then "ac3"
  else raise Fail "unexpected maker input (including hypotheses)"
fun maker (rw as (th,_)) = (record ("make:" ^ label th); [rw])
val collector = Traverse.REDUCER
  {name=SOME "route_collector",initial=Collector,
   addcontext=fn (ct,ths) =>
     (record "collect"; contexts := !contexts @ [ths]; ct),
   apply=fn _ => fn _ => raise Conv.UNCHANGED}
fun base filter = empty_ss ++ frag NONE (SOME filter) [] [] [collector] []
fun watch (2,Trace.LZ_TEXT text) =
      if String.isPrefix "New rewrite: " (text ()) then record "convert"
      else ()
  | watch _ = ()
fun watching f = let
  val name = "TASK15 routes compilation schedule"
  val _ = Listener.add_listener Trace.trace_hook (name,watch)
in Portable.finally
  (fn () => ignore (Listener.remove_listener Trace.trace_hook name)) f () end
fun logCheck name expected ctxt =
  (Paired.observe ("events." ^ name) (String.concatWith "," (!events));
   Paired.check name (!events = expected andalso
     ListPair.allEq sameThs (!contexts,ctxt)))
val duplicate = merge_ss [rewrites [r1,r2],rewrites [r1,r2]]
val installing = base maker
val _ = clear ()
val installed = watching (fn () => installing ++ duplicate)
val four = ["make:r1","make:r2","make:r1","make:r2"] @
           List.tabulate (4,K "convert") @ ["collect"]
val _ = logCheck "duplicate merge" four [[r1,r2,r1,r2]]
val _ = Paired.check "merged installation retains original fragment"
  (historyIs installed [duplicate,frag NONE (SOME maker) [] [] [collector] []])
val _ = clear ()
val twice = watching (fn () => installed ++ duplicate)
val _ = logCheck "duplicate installation" four [[r1,r2,r1,r2]]
val _ = Paired.check "duplicate installations remain in history"
  (length (ssfrags_of twice) = 3 andalso
   ListPair.allEq sameFrag (List.take (ssfrags_of twice,2),
                           [duplicate,duplicate]))
val _ = clear ()
val acInstalled = watching (fn () => installing ++
  frag NONE NONE [acPair] [(NONE,r1),(NONE,r2)] [] [])
val _ = logCheck "AC then ordinary"
  (["make:ac1","make:ac2","make:ac3","make:r1","make:r2"] @
   List.tabulate (5,K "convert") @ ["collect"]) [[r1,r2]]

(* The filter is installed AFTER compiling its own payload. *)
val _ = clear ()
val own = watching (fn () => empty_ss ++
  frag NONE (SOME maker) [] [(NONE,r2)] [] [])
val _ = logCheck "filter affects later only" ["convert"] []
val _ = proof "own filter payload proof and hypotheses" own r2

(* A later throwing maker must prevent ALL conversions and collectors. *)
val nth = ref 0
fun late (rw as (th,_)) =
  (nth := !nth + 1; record ("make:" ^ label th);
   if !nth = 5 then raise LaterMaker else [rw])
val lateBase = base late
val _ = clear ()
val lateResult = Exn.capture (fn () => watching (fn () => lateBase ++
  frag NONE NONE [acPair] [(NONE,r1),(NONE,r2)] [] [])) ()
val _ = logCheck "later throwing maker"
  ["make:ac1","make:ac2","make:ac3","make:r1","make:r2"] []
val _ = Paired.check "later maker exception identity"
  (case lateResult of Exn.Exn LaterMaker => true | _ => false)

(* All ordinary tags decode before AC compilation or ANY maker. The AC case
   is checked with both an effectful maker and a maker that would throw. *)
val malformed = ADD_ASSUM
  (mk_comb (boolSyntax.bounded_tm,mk_var ("not_a_number",bool))) r2
fun throws rw = (record "throwing-maker"; raise ThrowingMaker)
(* An invalid AC pair has a public HOL_MESG effect. First demonstrate that
   the observer fires; then malformed tags must suppress even that effect. *)
fun acMessages f =
  Portable.with_flag (Feedback.emit_MESG,true)
    (fn () => Portable.with_flag
      (Feedback.MESG_outstream,fn text =>
        if String.isSubstring "unable to AC-normalize input" text then
          record "AC-normalize"
        else raise Fail "unexpected message in AC ordering probe") f ()) ()
val invalidAC = [(r1,r1)]
val _ = clear ()
val acSensitivity = acMessages (fn () => watching (fn () => installing ++
  frag NONE NONE invalidAC [(NONE,r1)] [] []))
val _ = logCheck "AC message sensitivity"
  ["AC-normalize","make:r1","convert","collect"] [[r1]]
fun malformedCase name ac filter = let
  val ss = base filter
  val _ = clear ()
  val result = Exn.capture (fn () => acMessages (fn () => watching
    (fn () => ss ++ frag NONE NONE ac
      [(NONE,r1),(NONE,malformed)] [] []))) ()
  val _ = logCheck name [] []
in Paired.check (name ^ " exception")
     (case result of Exn.Exn Option => true | _ => false) end
val _ = malformedCase "malformed ordinary effect" [] maker
val _ = malformedCase "malformed ordinary throw" [] throws
val _ = malformedCase "malformed AC effect" [acPair] maker
val _ = malformedCase "malformed AC throw" [acPair] throws
val _ = malformedCase "malformed before AC message effect" invalidAC maker
val _ = malformedCase "malformed before AC message throw" invalidAC throws

(* Excluded ++ must not decode, call throwing makers/collectors, install a
   filter, or append history. force_add clears that name for subsequent ++. *)
val excluded0 = exclude_ssfrags ["route_skip"] empty_ss
val excluded = excluded0 ++ frag NONE (SOME throws) [] [] [collector] []
val skipped = frag (SOME "route_skip") (SOME throws) [acPair]
  [(NONE,malformed)] [opaque (SOME "skipped")] []
val _ = clear ()
val skipResult = Exn.capture
  (fn () => watching (fn () => excluded ++ skipped)) ()
val _ = logCheck "excluded throwing maker" [] []
val _ = Paired.check "excluded no history or exception"
  (case skipResult of Exn.Res ss =>
     historyIs ss (ssfrags_of excluded) andalso null (ssfrag_names_of ss)
   | _ => false)
val safeExcluded = excluded0 ++ frag NONE (SOME maker) [] [] [collector] []
val safe = named_rewrites "route_skip" [r2]
val _ = clear ()
val stillExcluded = watching (fn () => safeExcluded ++ safe)
val _ = logCheck "excluded collector" [] []
val _ = unchanged "excluded proof" stillExcluded (lhs (concl r2))
val throwingCollector = Traverse.REDUCER
  {name=SOME "throwing_collector",initial=Collector,
   addcontext=fn _ => (record "throwing-collector"; raise Collector),
   apply=fn _ => fn _ => raise Conv.UNCHANGED}
val collectorExcluded = excluded0 ++ dproc_ss throwingCollector
val _ = clear ()
val collectorSkip = Exn.capture
  (fn () => watching (fn () => collectorExcluded ++ safe)) ()
val _ = logCheck "excluded throwing collector" [] []
val _ = Paired.check "excluded collector history and exception"
  (case collectorSkip of Exn.Res ss =>
     historyIs ss (ssfrags_of collectorExcluded) andalso
     null (ssfrag_names_of ss)
   | _ => false)
val _ = clear ()
val forced = watching (fn () => force_add safeExcluded safe)
val _ = logCheck "force add" ["make:r2","convert","collect"] [[r2]]
val _ = Paired.check "force add history"
  (historyIs forced (safe :: ssfrags_of safeExcluded) andalso
   ssfrag_names_of forced = ["route_skip"])
(* The collector raises UNCHANGED on application. Legacy traversal propagates
   that even after a rewrite, so QCONV returns precisely this closed reflexive
   theorem, NOT r2. Keep both the full conclusion and exact empty hypotheses. *)
val collectorProof = REFL (lhs (concl r2))
val _ = proof "force add proof and hypotheses" forced collectorProof
val _ = clear ()
val afterForce = watching (fn () => forced ++ safe)
val _ = logCheck "force clears exclusion"
  ["make:r2","convert","collect"] [[r2]]
val _ = Paired.check "force subsequent duplicate history"
  (historyIs afterForce (safe :: safe :: ssfrags_of safeExcluded))
val _ = proof "force subsequent proof and hypotheses"
  afterForce collectorProof

(* Also test actual rewriting via force_add without the UNCHANGED collector:
   here the expected theorem has exactly the original nonempty hypotheses. *)
val forcedRewriter = force_add excluded0 safe
val _ = proof "force add without collector proof and hypotheses"
  forcedRewriter r2
val _ = proof "force subsequent without collector proof and hypotheses"
  (forcedRewriter ++ safe) r2
val _ = Paired.observe "complete" "TASK15-fragment-routes-v1"
