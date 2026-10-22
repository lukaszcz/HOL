(* TASK17 supplemental ordinary replay contracts. All proof checks include
   conclusions and complete hypothesis sets, not only rewritten endpoints. *)
open HolKernel Parse boolLib simpLib Paired
val _ = new_theory "task17_replay"
fun same (a,b) = aconv (concl a) (concl b) andalso
  HOLset.equal (hypset a,hypset b)
fun constant n = (new_constant (n,bool); mk_const (n,bool))
val p = constant "task17_p"
val q = constant "task17_q"
val a = ASSUME (mk_eq (p,T))
val b = ASSUME (mk_eq (q,T))
fun proof label ss tm expected = Paired.check label
  (same (Conv.QCONV (SIMP_CONV ss []) tm,expected))
val dummy = named_rewrites "task17_drop" []
fun replay ss = remove_ssfrags ["task17_drop"] ss
fun frag name filter rs ds = SSFRAG {name=name,filter=filter,rewrs=rs,
  dprocs=ds,convs=[],ac=[],congs=[]}
fun names ss = map frag_name (ssfrags_of ss)
fun unchanged f = (f (); false) handle Conv.UNCHANGED => true

(* Empty deletion is inert; missing NONEMPTY deletion must be recorded even
   in an empty net. A later theory change makes that observable as an error. *)
val saved = Context.snapshot ()
fun theoryChecks () = let
  val _ = Theory.link_parents ("task17_ephemeral","selftest") []
  val empty = empty_ss ++ dummy
  val literal = empty && [Excl "task17_ephemeral.missing"]
  val direct = remove_simps ["task17_ephemeral.missing"] empty
  val emptyDeletion = empty -* []
  val present = Context.snapshot ()
  val _ = Context.restore saved
  val _ = new_theory "task17_changed"
  fun error ss = case Exn.capture replay ss of
      Exn.Exn (HOL_ERR e) => Feedback.top_function_of e = "-*" andalso
        Feedback.message_of e = "bad theory name: task17_ephemeral"
    | _ => false
  val _ = Paired.check "unmatched Excl reparsed in new theory" (error literal)
  val _ = Paired.check "unmatched remove_simps reparsed in new theory"
    (error direct)
  val _ = Paired.check "empty list has no deletion history"
    (names (replay emptyDeletion) = [])
  val _ = Context.restore present
  val _ = Paired.check "unmatched history valid after theory restoration"
    (names (replay direct) = [] andalso
     names (exclude_ssfrags [] literal) = [NONE,SOME "Cong and/or AC",
                                           SOME "task17_drop"])
in () end
val _ = Portable.finally (fn () => Context.restore saved) theoryChecks ()

(* Replay must rerun makers in historical order and prime the surviving
   collectors at their original stages, including ADDWEAKENER and deletes. *)
val events = ref ([] : string list)
fun record s = events := !events @ [s]
fun label th = if same (th,a) then "a" else if same (th,b) then "b"
               else raise Fail "unexpected collector theorem"
fun maker id (rw as (th,_)) = (record (id ^ ":" ^ label th); [rw])
exception C
fun reducer n = Traverse.REDUCER {name=SOME n,initial=C,
  addcontext=fn (ct,ths) =>
    (record (n ^ ":" ^ String.concatWith "," (map label ths)); ct),
  apply=fn _ => NO_CONV}
val setup = frag (SOME "setup") (SOME (maker "m1")) [] [reducer "d1"]
val switch = frag (SOME "switch") (SOME (maker "m2")) [] []
val fa = frag (SOME "A") NONE [(NONE,a)] []
val fb = frag (SOME "B") NONE [(NONE,b)] []
val s0 = empty_ss ++ setup ++ fa
val s1 = add_weakener ([],[],reducer "weak") s0
val source = (((s1 -* ["d1","missing"]) ++ switch) ++ fb) ++ dummy
val _ = events := []
val rebuilt = replay source
val _ = Paired.observe "replay.events" (String.concatWith ";" (!events))
val _ = Paired.check "replay callback order and exact counts"
  (!events = ["m1:a","d1:a","weak:","m1:b","m2:b","weak:b"])
val _ = Paired.check "replay preserves dproc deletion and weakener"
  (map (#name o Traverse.dest_reducer)
    (#dprocs (traversedata_for_ss rebuilt)) = [SOME "weak"])
val _ = proof "replayed first proof" rebuilt p a
val _ = proof "replayed second proof" rebuilt q b
val _ = events := []
val _ = Paired.check "missing fragment removal raises UNCHANGED"
  (unchanged (fn () => ignore (remove_ssfrags ["not_installed"] source)))
val _ = Paired.check "UNCHANGED removal invokes no callbacks" (null (!events))
val _ = exclude_ssfrags [] source
val _ = Paired.check "empty exclude still replays"
  (!events = ["m1:a","d1:a","weak:","m1:b","m2:b","weak:b","weak:"])

(* Excluded state and traversal limits survive every replay route. Empty-name
   exclusion removes existing anonymous frags, not future anonymous additions;
   force_add does not reinterpret this baseline distinction. *)
val blocked = exclude_ssfrags ["A",""] (limit 0 (empty_ss ++ dummy ++ fa))
val _ = Paired.check "exclude removes all matching history"
  (names blocked = [SOME "task17_drop"])
val forced = force_add blocked fa
val _ = proof "force preserves zero limit" forced p (REFL p)
val forcedReplay = replay forced
val _ = Paired.check "remove preserves limit"
  (#limit (traversedata_for_ss forcedReplay) = SOME 0)
val _ = proof "unlimit after forced replay" (unlimit forcedReplay) p a
val _ = Paired.check "force clears only named prohibition"
  (names (forcedReplay ++ fa ++ rewrites [b]) = [NONE,SOME "A",SOME "A"])
val _ = Paired.check "anonymous force remains anonymous addition"
  (names (force_add blocked (rewrites [b])) = NONE :: names blocked)
val reexcluded = exclude_ssfrags ["A"] forcedReplay
val _ = Paired.check "exclude preserves limits and anonymous prohibition"
  (#limit (traversedata_for_ss reexcluded) = SOME 0 andalso
   names (reexcluded ++ fa ++ rewrites [b]) = [NONE])
val _ = Paired.check "empty remove raises UNCHANGED"
  (unchanged (fn () => ignore (remove_ssfrags [] forcedReplay)))

(* Ordinary replay resets declared quotas, unlike extension control-preserving
   replay. Missing deletions retain survivors' actual live controls until then. *)
fun bounded k = empty_ss ++ dummy ++ named_rewrites "bounded" [Ntimes a k]
val quota = bounded 2
val _ = proof "bounded first use" quota p a
val survivor = quota -* ["missing"]
val _ = proof "deletion shares remaining quota" survivor p a
val _ = proof "original quota exhausted" quota p (REFL p)
val reset = replay survivor
val _ = proof "replay resets declared quota first" reset p a
val _ = proof "replay resets declared quota second" reset p a
val _ = proof "replay allowance exhausted" reset p (REFL p)
val _ = proof "old allowance stays exhausted" survivor p (REFL p)
val resetByExclude = exclude_ssfrags ["not_present"] survivor
val _ = proof "exclude resets declared bound" resetByExclude p a
val _ = proof "exclude declared second use" resetByExclude p a
val _ = proof "exclude declared exhaustion" resetByExclude p (REFL p)
val _ = proof "zero declared bound remains zero" (replay (bounded 0)) p (REFL p)

(* Markers reach the same literal net/dproc deletion via conversions and reused
   tactics. Returned tactic validations must reconstruct the original theorem. *)
val literalName = "task17_namespace::rule"
val installed = empty_ss ++ rewrites_with_names
  [({Thy="bool",Name=literalName},a)]
val goalProof = EQ_MP (SYM a) TRUTH
fun tactics () = let
  fun one (tag,excluded) = let
    val th = Conv.QCONV (SIMP_CONV installed [Excl tag]) p
    val _ = Paired.check ("conversion " ^ tag)
      (same (th,if excluded then REFL p else a))
    val tac = SIMP_TAC installed [Excl tag]
    fun use suffix = let
      val (goals,validate) = testutils.runtac tac ([concl a],p)
      fun solve (asl,w) = if aconv w T then TRUTH
                         else if aconv w p then goalProof
                         else raise Fail "unexpected tactic subgoal"
      val result = validate (map solve goals)
    in Paired.check ("tactic " ^ tag ^ " " ^ suffix)
      (same (result,goalProof) andalso
       (if excluded then length goals = 1 else null goals)) end
  in use "first"; use "reused" end
in List.app one [("task17_namespace::",false),(literalName,true),
                 ("bool." ^ literalName,true),("missing",false)] end
val _ = tactics ()
val _ = Paired.observe "complete" "TASK17-exclusions-replay-v1"
