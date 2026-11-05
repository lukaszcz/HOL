(* Public legacy APIs only. Each workload owns a retained result, an exact
   proof checker and (where relevant) untimed batch callback assertions.
   This is harness code, not production instrumentation. *)
structure MatrixSupport =
struct
  open HolKernel boolSyntax boolLib simpLib
  val sizes = [0,1,10,100,1000,10000]
  val cases =
    ["frag_create", "frag_named", "frag_named_rules", "frag_record",
     "frag_update", "frag_duplicate", "frag_merge", "frag_named_merge",
     "frag_ac", "frag_ac_merge", "frag_typebase", "frag_type_lookup",
     "compile_batch", "compile_single", "compile_empty", "compile_excluded",
     "compile_conditional", "compile_bounded", "compile_ac", "compile_maker",
     "compile_user", "compile_collector", "compile_construct_conv",
     "compile_reuse", "compile_complete", "compile_supplied",
     "exclude_empty", "exclude_missing", "exclude_matching", "exclude_batch",
     "exclude_qualified", "exclude_partial", "exclude_literal_namespace",
     "exclude_literal_exact", "exclude_dproc", "exclude_mixed",
     "exclude_marker", "exclude_marker_reuse",
     "exclude_tactic_construct", "exclude_tactic_reuse",
     "exclude_tactic_complete", "exclude_replay",
     "history_remove", "history_force", "history_excluded", "history_bounded",
     "history_limit", "history_collectors", "history_makers",
     "history_theory_change",
     "storage_graph"]
  fun required b = if b then () else raise Fail "matrix workload invariant"
  fun same (a,b) = aconv (concl a) (concl b) andalso
                  HOLset.equal (hypset a,hypset b)
  fun proof expected actual = required (same (expected,actual))
  fun sameList (a,b) = ListPair.allEq same (a,b)
  fun names ss = map frag_name (ssfrags_of ss)
  fun dpnames ss = map (#name o Traverse.dest_reducer)
                        (#dprocs (traversedata_for_ss ss))
  (* Isolate the net for semantic checks of inert collector dprocs. An inert
     dproc returning UNCHANGED can otherwise mask the ordinary net result. *)
  fun netconv ss = let
    val {rewriters,travrules,relation,limit,...} = traversedata_for_ss ss
  in Conv.QCONV (Conv.TRY_CONV (Traverse.TRAVERSE
       {rewriters=rewriters,travrules=travrules,relation=relation,
        limit=limit,dprocs=[]} [])) end
  (* Hooks of the structural evidence of the allocation fixture
     (MatrixAllocation.sml) and the operator smoke. The constructors of a
     workload set them, when the workload is built and never inside a timed
     closure; the work phase reads them once, untimed, after the operations.
       fingerprint  text of the retained result, for a digest
       useResult    a client's use of the retained result, which the work
                    phase counts (no use: nothing to count)
       localCalls   maker calls a workload counts itself, not in makerCalls
       ruleList     the n installed rules (a reference to the list the
                    workload builds anyway, so setup allocates no copy) *)
  val missingFingerprint = fn () => raise Fail "workload without fingerprint"
  val fingerprint : (unit -> string) ref = ref missingFingerprint
  val noUse = fn () => ()
  val useResult : (unit -> unit) ref = ref noUse
  val noCalls = fn () => 0
  val localCalls : (unit -> int) ref = ref noCalls
  val ruleList = ref ([] : thm list)
  fun retaining text use = (fingerprint := text; useResult := use)
  fun printable s = String.translate (fn c =>
    if Char.isPrint c andalso c <> #"\\" then str c else Char.toString c) s
  fun termText tm = Lib.with_flag (Globals.show_types,true)
    (fn () => printable (Parse.term_to_string tm)) ()
  fun thmText th = String.concatWith "," (map termText (hyp th)) ^ " |- " ^
                   termText (concl th)
  fun goalText (asl,w) =
    String.concatWith "," (map termText asl) ^ " ?- " ^ termText w
  (* FNV-1a, 64 bits, in hex: a compact stand-in for a long text. *)
  fun hashText s = let
    val prime = Word64.fromInt 1099511628211
    fun step (c,h) = Word64.* (Word64.xorb (h,Word64.fromInt (Char.ord c)),
                               prime)
  in Word64.fmt StringCvt.HEX
       (CharVector.foldl step (Word64.fromLargeInt 14695981039346656037) s)
  end
  fun rangesText is = let
    fun add (i,[]) = [(i,i)]
      | add (i,(lo,hi)::rest) =
          if i = hi + 1 then (lo,i) :: rest else (i,i) :: (lo,hi) :: rest
    fun one (lo,hi) = Int.toString lo ^
                      (if lo = hi then "" else "-" ^ Int.toString hi)
  in String.concatWith "," (map one (List.rev (List.foldl add [] is))) end
  fun optText NONE = "-"
    | optText (SOME s) = "+" ^ s
  (* The net conversion of ss on the left side of each installed rule, in
     order: what a client does with a simpset. f sees the index and result. *)
  fun lookups ss f = let
    val conv = netconv ss
    fun one (rw,i) = (f (i,conv (lhs (concl rw))); i + 1)
  in ignore (List.foldl one 0 (!ruleList)) end
  (* The dprocs of a simpset are not in the net, and the traversal tries
     them only when the net leaves a term alone, and stops at the first
     that does not fail (the fixture's raise UNCHANGED, which ends the
     search), so a conversion would apply one of them. A use of a simpset
     therefore also applies each of its dprocs directly, with the public
     Traverse.dest_reducer and the context it holds, to a few of the left
     sides: the first (the rule the deletion cases delete, which the net no
     longer answers), the middle and the last. The fixture's dprocs raise
     UNCHANGED and so leave no trace event and no inference; what is
     counted is their own counter (dprocCalls, below): the number of dprocs
     the result still holds times the number of sampled terms. *)
  fun useDprocs ss = let
    val {dprocs,relation,...} = traversedata_for_ss ss
    val n = length (!ruleList)
    val sample = if n = 0 then [] else Lib.mk_set [0,n div 2,n-1]
    fun fail _ _ = raise Feedback.mk_HOL_ERR "MatrixSupport" "useDprocs" "no"
    fun apply tm d = let
      val {apply,initial,...} = Traverse.dest_reducer d
    in ignore (apply {solver=fail,conv=fail,context=initial,stack=[],
                      relation=(relation,REFL)} tm)
         handle _ => () end
  in List.app (fn i => let val tm = lhs (concl (List.nth (!ruleList,i)))
                       in List.app (apply tm) dprocs end) sample end
  fun useSS ss = (lookups ss ignore; useDprocs ss)
  (* Names, dprocs, the set of installed rules whose left side the net
     leaves alone (run-length encoded) and a hash of the other results. *)
  fun ssText ss = let
    val untouched = ref ([] : int list)
    val others = ref ([] : string list)
    fun note (i,th) =
      if aconv (lhs (concl th)) (rhs (concl th))
      then untouched := i :: !untouched
      else others := thmText th :: !others
    val _ = lookups ss note
  in "names=" ^ String.concatWith "," (map optText (names ss)) ^
     ";dprocs=" ^ String.concatWith "," (map optText (dpnames ss)) ^
     ";refl=" ^ rangesText (List.rev (!untouched)) ^
     ";other=" ^ hashText (String.concatWith ";" (List.rev (!others))) end
  type workload = {run:unit -> unit, verify:unit -> unit,
                   beforeBatch:unit -> unit, afterBatch:int -> unit}
  fun basic run verify : workload =
    {run=run,verify=verify,beforeBatch=fn () => (),afterBatch=fn _ => ()}
  (* Public simplifier conversions use UNCHANGED for identity results. The
     proof checker always needs an explicit reflexivity theorem instead. *)
  fun SIMP_CONV ss ths = Conv.QCONV (simpLib.SIMP_CONV ss ths)
  val rawStorage = ref (fn () => ())
  (* The theory-graph change of history_theory_change. In a `hol run` process
     (Globals.interactive is false) new_theory exports the current theory:
     it writes *Theory files below the working directory and its words
     depend on the clock and the process id. A harness that counts words
     replaces it (MatrixAllocation.sml): the reparse the case verifies comes
     from the Context.restore that drops the linked theory, not from the
     new one. *)
  val theoryChange = ref (fn name => ignore (new_theory name))
  val makerCalls = ref 0
  val collectorCalls = ref 0
  val dprocCalls = ref 0
  fun maker rw = (makerCalls := !makerCalls + 1; [rw])
  exception CollectorContext
  (* One shared closure for every fixture dproc: a per-reducer closure over
     dprocCalls would add words to setup for each of the n dprocs. *)
  fun dprocApply _ _ = (dprocCalls := !dprocCalls + 1; raise Conv.UNCHANGED)
  fun reducer name = Traverse.REDUCER
    {name=SOME name,initial=CollectorContext,
     addcontext=fn (ct,_) => (collectorCalls := !collectorCalls + 1; ct),
     apply=dprocApply}
  fun setup filter dprocs = SSFRAG
    {name=SOME "matrix_setup",filter=filter,dprocs=dprocs,
     rewrs=[],convs=[],ac=[],congs=[]}
  fun callbacks makers collectors ({run,verify,...}:workload) : workload = let
    val oldM = ref 0
    val oldC = ref 0
  in {run=run,verify=verify,
      beforeBatch=fn () => (oldM := !makerCalls; oldC := !collectorCalls),
      afterBatch=fn count =>
        required (!makerCalls - !oldM = count * makers andalso
                  !collectorCalls - !oldC = count * collectors)} end
  (* Structural evidence: an untimed phase after the operations. It runs
     the operation twice, then the use of its retained result, each with the
     simplifier's trace listener, which Trace.trace calls whatever the trace
     level, and the kernel's inference counter, and reports the callback
     counts with them. The listener counts by exact level and action
     constructor, and a TEXT also by its message (a plain string; an LZ_TEXT
     is never forced and has no message in the key). The fingerprint of the
     retained result closes the list. Nothing here runs in a timed
     process. *)
  val traceActions =
    ["IGNORE", "LZ_TEXT", "MORE_CONTEXT", "OPENING", "PRODUCE", "REDUCE",
     "REWRITING", "SIDECOND_ATTEMPT", "SIDECOND_NOT_SOLVED",
     "SIDECOND_SOLVED", "TEXT"]
  fun actionIndex a = case a of
      Trace.IGNORE _ => 0 | Trace.LZ_TEXT _ => 1 | Trace.MORE_CONTEXT _ => 2
    | Trace.OPENING _ => 3 | Trace.PRODUCE _ => 4 | Trace.REDUCE _ => 5
    | Trace.REWRITING _ => 6 | Trace.SIDECOND_ATTEMPT _ => 7
    | Trace.SIDECOND_NOT_SOLVED _ => 8 | Trace.SIDECOND_SOLVED _ => 9
    | Trace.TEXT _ => 10
  val textIndex = 10
  (* A message in a key: printable ASCII outside the separators as is, any
     other byte as %XX. *)
  fun escapeText s = String.translate (fn c =>
    if Char.isAlphaNum c orelse Char.contains " _.()'/+*-<>[]!?:" c
    then str c
    else "%" ^ StringCvt.padLeft #"0" 2 (Int.fmt StringCvt.HEX (Char.ord c)))
    s
  fun levelText l = if l < 0 then "-" ^ Int.toString (~l) else Int.toString l
  fun keyCompare ((l1,a1,m1),(l2,a2,m2)) =
    case Int.compare (l1,l2) of
      EQUAL => (case Int.compare (a1,a2) of
                  EQUAL => String.compare (m1,m2) | r => r)
    | r => r
  fun keyText (l,a,m) = levelText l ^ "." ^ List.nth (traceActions,a) ^
                        (if a = textIndex then ":" ^ m else "")
  fun countsText named = String.concatWith "," (List.mapPartial
    (fn (k,n) => if n = 0 then NONE else SOME (k ^ "=" ^ Int.toString n))
    named)
  fun kernelCounts () = let val c = Count.thm_count () in
    [("ABS",#ABS c),("ALPHA",#ALPHA c),("AP_TERM",#AP_TERM c),
     ("AP_THM",#AP_THM c),("ASSUME",#ASSUME c),("BETA_CONV",#BETA_CONV c),
     ("CCONTR",#CCONTR c),("CHOOSE",#CHOOSE c),("COMPUTE",#COMPUTE c),
     ("CONJ",#CONJ c),("CONJUNCT1",#CONJUNCT1 c),
     ("CONJUNCT2",#CONJUNCT2 c),("DISCH",#DISCH c),("DISJ1",#DISJ1 c),
     ("DISJ2",#DISJ2 c),("DISJ_CASES",#DISJ_CASES c),
     ("EQ_IMP_RULE",#EQ_IMP_RULE c),("EQ_MP",#EQ_MP c),
     ("EXISTS",#EXISTS c),("GEN",#GEN c),("GEN_ABS",#GEN_ABS c),
     ("INST",#INST c),("INST_TYPE",#INST_TYPE c),("MK_COMB",#MK_COMB c),
     ("MP",#MP c),("NOT_ELIM",#NOT_ELIM c),("NOT_INTRO",#NOT_INTRO c),
     ("REFL",#REFL c),("SPEC",#SPEC c),("SUBST",#SUBST c),("SYM",#SYM c),
     ("TRANS",#TRANS c),("axiom",#axiom c),("definition",#definition c),
     ("from_disk",#from_disk c),("oracle",#oracle c),("total",#total c)] end
  (* One action between a reset and a read of every counter, as
     trace=L.ACTION[:message]=n,...;kernel=RULE=n,...;maker=n;collector=n;
     dproc=n *)
  fun counted (action : unit -> unit) = let
    val table = ref (Binarymap.mkDict keyCompare)
    fun listen (level,a) = let
      val key = (level,actionIndex a,
                 case a of Trace.TEXT s => escapeText s | _ => "")
      val n = case Binarymap.peek (!table,key) of NONE => 0 | SOME n => n
    in table := Binarymap.insert (!table,key,n + 1) end
    val maker0 = !makerCalls + (!localCalls) ()
    val collector0 = !collectorCalls
    val dproc0 = !dprocCalls
    fun body () =
      (Count.reset_thm_count ();
       Count.counting_thms true;
       Listener.add_listener Trace.trace_hook ("matrix_work",listen);
       action ())
    fun cleanup () =
      (ignore (Listener.remove_listener Trace.trace_hook "matrix_work");
       Count.counting_thms false)
    val _ = Portable.finally cleanup body ()
    val traced = map (fn (k,n) => (keyText k,n)) (Binarymap.listItems
                                                    (!table))
  in "trace=" ^ countsText traced ^ ";kernel=" ^ countsText (kernelCounts ()) ^
     ";maker=" ^ Int.toString (!makerCalls + (!localCalls) () - maker0) ^
     ";collector=" ^ Int.toString (!collectorCalls - collector0) ^
     ";dproc=" ^ Int.toString (!dprocCalls - dproc0) end
  fun measureOnce ({run,beforeBatch,afterBatch,...}:workload) =
    counted (fn () => (beforeBatch (); run (); afterBatch 1))
  (* The records of the work phase: two counted runs, the counted use of the
     retained result of the second (convert the left side of each rule with
     the net of a simpset; apply a retained conversion; apply a retained
     tactic; no use of a bare theorem, whose record is then the empty set of
     counts), then the fingerprint of the retained result. *)
  fun workPhase (w:workload) = let
    val first = measureOnce w
    val second = measureOnce w
    (* The digest first: a use can consume what it describes (the bounds
       of a bounded rewrite), so it describes the result as retained. *)
    val digest = (!fingerprint) ()
    val use = counted (!useResult)
  in [("work.first",first),("work.second",second),("work.use",use),
      ("result.digest",digest)]
  end
  fun constant name = (new_constant (name,bool); mk_const (name,bool))
  fun rule i = ASSUME (mk_eq
    (constant ("matrix_c" ^ Int.toString i),T))
  fun rname i = "matrix_r" ^ Int.toString i
  fun nsname i = "matrix_ns::r" ^ Int.toString i
  fun dpname i = "matrix_dp" ^ Int.toString i
  fun namedRules namer rs = rewrites_with_names
    (ListPair.zip (List.tabulate (length rs,fn i =>
      {Thy="bool",Name=namer i}),rs))
  (* The fingerprint of a fragment: name, rules (a hash of their printed
     form) and what `extra` makes of it; its use is a simpset with it. *)
  fun fragText extra f = let
    val actual = frag_rewrites f
  in optText (frag_name f) ^ ";" ^ Int.toString (length actual) ^ ";" ^
     hashText (String.concatWith ";" (map thmText actual)) ^ ";" ^ extra f
  end
  fun fragworkWith extra build expected name checkExtra = let
    val slot = ref (build ())
    val _ = retaining (fn () => fragText extra (!slot))
                      (fn () => useSS (empty_ss ++ !slot))
    fun verify () =
      (required (frag_name (!slot) = name andalso
                 sameList (frag_rewrites (!slot),expected));
       checkExtra (!slot))
  in basic (fn () => slot := build ()) verify end
  val fragwork = fragworkWith (fn _ => "")
  fun sswork build verifyResult = let
    val slot = ref (build ())
    val _ = retaining (fn () => ssText (!slot)) (fn () => useSS (!slot))
  in basic (fn () => slot := build ()) (fn () => verifyResult (!slot)) end
  fun thwork build expected = let
    val slot = ref (build ())
    val _ = retaining (fn () => thmText (!slot)) noUse
  in basic (fn () => slot := build ()) (fn () => proof expected (!slot)) end
  fun convwork build check terms = let
    val slot = ref (build ())
    val _ = retaining (fn () => String.concatWith ";"
                         (map (fn tm => thmText ((!slot) tm)) (terms ())))
                      (fn () => List.app (fn tm => ignore ((!slot) tm))
                                         (terms ()))
  in basic (fn () => slot := build ())
       (fn () => (check (!slot); check (!slot))) end

  fun workload label n = let
    val _ = required (Lib.mem label cases andalso Lib.mem n sizes)
    (* Constants have distinct net keys, not n variants of one variable rule.
       All installed rules have an exact, intentionally nonempty hypothesis. *)
    val rs = List.tabulate (n,rule)
    val _ = (ruleList := rs; fingerprint := missingFingerprint;
             useResult := noUse; localCalls := noCalls)
    val miss = constant "matrix_miss"
    val target = if null rs then miss else lhs (concl (hd rs))
    val expected = if null rs then REFL target else hd rs
    val frag = rewrites rs
    val data = name_ss "matrix_data" (namedRules rname rs)
    val drop = named_rewrites "matrix_drop" []
    val indices = if n = 0 then [] else Lib.mk_set [0,n div 2,n-1]
    fun checks removed cv =
      (List.app (fn i => let
         val rw = List.nth (rs,i)
         val tm = lhs (concl rw)
       in proof (if removed i then REFL tm else rw) (cv tm) end) indices;
       proof (REFL miss) (cv miss))
    fun no _ = false
    fun checkSS removed ss = checks removed (netconv ss)
    fun checkFrag f = checkSS no (empty_ss ++ f)
    fun normal build = sswork build (checkSS no)
    fun checkHistory want removed ss =
      (required (names ss = want); checkSS removed ss)
    fun installed () = empty_ss ++ data
    val first = fn i => i = 0
    val acPair = (boolTheory.CONJ_ASSOC,boolTheory.CONJ_SYM)
    val acs = List.tabulate (n,fn _ => acPair)
    val x = mk_var ("matrix_x",bool)
    val y = mk_var ("matrix_y",bool)
    val xy = mk_conj (x,y)
    val yx = mk_conj (y,x)
    val (acInput,acExpected) =
      if Cond_rewr.ac_term_ord (xy,yx) = GREATER then
        (xy,SPECL [x,y] boolTheory.CONJ_SYM)
      else (yx,SPECL [y,x] boolTheory.CONJ_SYM)
    fun checkAC ss = proof
      (if n = 0 then REFL acInput else acExpected)
      (SIMP_CONV ss [] acInput)
    fun acfrag build = fragworkWith (fn f => thmText
      (SIMP_CONV (empty_ss ++ f) [] acInput)) build [] NONE
      (fn f => (checkAC (empty_ss ++ f); checkAC (empty_ss ++ f)))
    fun typefrag lookup = let
      val info = valOf (TypeBase.fetch bool)
      val ti = TypeBasePure.put_simpls {rewrs=rs,convs=[]} info
      (* The hook runs after TypeBase's standard simplification augmentation.
         Mutation/setup is outside timing in this private fresh process. *)
      val _ = if not lookup then () else
        (TypeBase.register_update_fn (fn item =>
           if TypeBasePure.ty_name_of item = TypeBasePure.ty_name_of info
           then TypeBasePure.put_simpls {rewrs=rs,convs=[]} item else item);
         TypeBase.write [ti])
      val build = if lookup then fn () => type_ssfrag bool
                  else fn () => tyi_to_ssdata ti
    in fragwork build (List.rev rs) (SOME "Datatype min$bool") checkFrag end
    fun compilation () =
      case label of
        "compile_batch" => sswork (fn () => empty_ss ++ frag)
          (checkHistory [NONE] no)
      | "compile_single" => let
          val singles = map (fn th => rewrites [th]) rs
        in sswork (fn () => List.foldl (fn (f,ss) => ss ++ f)
                             empty_ss singles)
             (checkHistory (List.tabulate (n,fn _ => NONE)) no) end
      | "compile_empty" => let val source = installed () in
          sswork (fn () => source ++ empty_ssfrag)
            (checkHistory [NONE,SOME "matrix_data"] no) end
      | "compile_excluded" => let
          val blocked = exclude_ssfrags ["matrix_data"] empty_ss
        in sswork (fn () => blocked ++ data)
             (fn ss => (checkHistory [] (fn _ => true) ss;
                        checkSS no (force_add ss data))) end
      | "compile_conditional" => let
          val condition = miss
          val conditionProof = ASSUME condition
          val rules = map (DISCH condition) rs
          val conditional = rewrites rules
          fun expectedFor rw = CONJUNCT2 (CONJ conditionProof rw)
          fun verify ss =
            (checks (fn _ => true) (SIMP_CONV ss []);
             List.app (fn i => let val rw = List.nth (rs,i) in
               proof (expectedFor rw)
                 (SIMP_CONV ss [conditionProof] (lhs (concl rw))) end) indices)
        in sswork (fn () => pureSimps.pure_ss ++ conditional) verify end
      | "compile_bounded" => let
          val bounded = rewrites (map (fn th => Ntimes th 1) rs)
          fun verify ss =
            (proof expected (SIMP_CONV ss [] target);
             proof (REFL target) (SIMP_CONV ss [] target))
        in sswork (fn () => empty_ss ++ bounded) verify end
      | "compile_ac" => sswork (fn () => empty_ss ++ ac_ss acs) checkAC
      | "compile_maker" => let
          val source = empty_ss ++ setup (SOME maker) []
        in callbacks n 0 (normal (fn () => source ++ frag)) end
      | "compile_collector" => let
          val source = empty_ss ++ setup NONE [reducer "matrix_collector"]
        in callbacks 0 1 (sswork (fn () => source ++ frag)
             (fn ss => (required (dpnames ss = [SOME "matrix_collector"]);
                        checkSS no ss))) end
      | "compile_user" => let
          fun cd (i,rw) : convdata =
            {name="matrix_user" ^ Int.toString i,
             key=SOME ([],lhs (concl rw)),trace=2,
             conv=fn _ => fn _ => fn tm =>
               if aconv tm (lhs (concl rw)) then rw
               else raise Conv.UNCHANGED}
          val convs = map cd (ListPair.zip (List.tabulate (n,I),rs))
          val f = SSFRAG {name=NONE,convs=convs,rewrs=[],ac=[],
                          filter=NONE,dprocs=[],congs=[]}
        in normal (fn () => empty_ss ++ f) end
      | "compile_construct_conv" => let
          val source = installed ()
        in convwork (fn () => SIMP_CONV source []) (checks no)
             (fn () => miss :: map (fn i => lhs (concl (List.nth (rs,i))))
                                   indices)
        end
      | "compile_reuse" => let val cv = SIMP_CONV (installed ()) [] in
          thwork (fn () => cv target) expected end
      | "compile_complete" => thwork
          (fn () => SIMP_CONV (empty_ss ++ rewrites rs) [] target) expected
      | "compile_supplied" => thwork
          (fn () => SIMP_CONV empty_ss rs target) expected
      | _ => raise Fail "unknown compilation case"
    fun exclusions () = let
      val source = installed ()
      val batch = Lib.mk_set [0,n div 2,Int.max (0,n-1)]
      fun delete from pats removed = sswork (fn () => from -* pats)
        (fn ss => (required (names ss = names from andalso
                            dpnames ss = dpnames from);
                   checkSS removed ss; checkSS no from))
      fun markerTactic stage = let
        fun make () = SIMP_TAC source [Excl (rname 0)]
        val slot = ref (make ())
        val expected = ASSUME target
        val result = ref expected
        val residual = ref ([] : Abbrev.goal list)
        fun apply () = let
          val (gs,actualvf) = testutils.runtac (!slot) ([],target)
        in residual := gs; result := actualvf [ASSUME target] end
        fun check () =
          (required (case !residual of [(asl,w)] =>
             null asl andalso aconv w target | _ => false);
           proof expected (!result))
        fun run () = case stage of
            "construct" => slot := make ()
          | "reuse" => apply ()
          | "complete" => (slot := make (); apply (); check ())
          | _ => raise Fail "unknown marker tactic stage"
        fun verify () =
          (if stage = "construct" then apply () else (); check ())
        val _ = apply ()
        val _ = retaining (fn () => String.concatWith ";"
                  (map goalText (!residual) @ [thmText (!result)]))
                  (fn () => if stage = "construct" then apply () else ())
      in basic run verify end
      fun dproc mixed = let
        val ds = List.tabulate (n,fn i => reducer (dpname i))
        (* The dprocs and a maker come first and the data after them, so
           that a rebuild of the history would prime the dprocs (++ passes
           the rewrites of each later fragment to Traverse.addctxt) and,
           where data follows (mixed), run the maker: the zero counts below
           then show the deletion replays nothing, not that there was
           nothing to replay. With no data only the collectors are primed. *)
        val f = setup (SOME maker) ds
        val from = empty_ss ++ f ++ (if mixed then data else empty_ssfrag)
        val pats = [dpname 0] @ (if mixed then [rname 0] else [])
        val wantDP = List.drop (map (SOME o dpname)
                                (List.tabulate (n,I)),Int.min (1,n))
        fun verify ss =
          (required (dpnames ss = wantDP andalso
                     length (dpnames from) = n andalso names ss = names from);
           checkSS (if mixed then first else fn _ => true) ss;
           checkSS (if mixed then no else fn _ => true) from)
        (* Deleting replays nothing: -* filters the net and the dprocs, and
           neither a maker nor a collector runs. *)
      in callbacks 0 0 (sswork (fn () => from -* pats) verify) end
    in case label of
        "exclude_empty" => delete source [] no
      | "exclude_missing" => delete source ["matrix_missing"] no
      | "exclude_matching" => delete source [rname 0] first
      | "exclude_batch" => delete source
          (map rname batch @ ["matrix_missing"]) (fn i => Lib.mem i batch)
      | "exclude_qualified" => delete source ["bool." ^ rname 0] first
      | "exclude_partial" => let
          fun split (rw as (th,tag)) =
            if n >= 2 andalso same (th,hd rs) then
              [rw,(List.nth (rs,1),tag)] else [rw]
          val partialRs = if n < 2 then rs else hd rs :: List.drop (rs,2)
          val partial = empty_ss ++ setup (SOME split) [] ++
                        namedRules rname partialRs
        in delete partial [rname 0 ^ ".1"] first end
      | "exclude_literal_namespace" =>
          delete (empty_ss ++ namedRules nsname rs) ["matrix_ns::"] no
      | "exclude_literal_exact" =>
          delete (empty_ss ++ namedRules nsname rs) [nsname 0] first
      | "exclude_dproc" => dproc false
      | "exclude_mixed" => dproc true
      | "exclude_marker" => thwork
          (fn () => SIMP_CONV source [Excl (rname 0)] target) (REFL target)
      | "exclude_marker_reuse" => let
          val cv = SIMP_CONV source [Excl (rname 0)]
        in thwork (fn () => cv target) (REFL target) end
      | "exclude_tactic_construct" => markerTactic "construct"
      | "exclude_tactic_reuse" => markerTactic "reuse"
      | "exclude_tactic_complete" => markerTactic "complete"
      | "exclude_replay" => let
          val from = (source -* [rname 0,"matrix_missing"]) ++ drop
        in sswork (fn () => remove_ssfrags ["matrix_drop"] from)
             (fn ss => (checkHistory [SOME "matrix_data"] first ss;
                        checkSS first from; checkSS no source)) end
      | _ => raise Fail "unknown exclusion case"
    end
    fun history () = let
      val source = installed () ++ drop
      fun replay ss = remove_ssfrags ["matrix_drop"] ss
    in case label of
        "history_remove" => sswork
          (fn () => remove_ssfrags ["matrix_data"] source)
          (fn ss => (checkHistory [SOME "matrix_drop"] (fn _ => true) ss;
                     checkSS no source))
      | "history_force" => let
          val blocked = exclude_ssfrags ["matrix_data"] source
        in sswork (fn () => force_add blocked data)
             (fn ss => (checkHistory
                          [SOME "matrix_data",SOME "matrix_drop"] no ss;
                        checkSS (fn _ => true) blocked;
                        required (names (ss ++ data) =
                                  SOME "matrix_data" :: names ss))) end
      | "history_excluded" => sswork
          (fn () => exclude_ssfrags ["matrix_data"] source)
          (fn ss => (checkHistory [SOME "matrix_drop"] (fn _ => true) ss;
                     checkHistory [SOME "matrix_drop"] (fn _ => true)
                       ((replay ss) ++ drop ++ data);
                     checkSS no (force_add ss data)))
      | "history_bounded" => let
          val from = empty_ss ++ drop ++
                     named_rewrites "matrix_bounded"
                       (map (fn th => Ntimes th 1) rs)
          val _ = proof expected (SIMP_CONV from [] target)
          val _ = proof (REFL target) (SIMP_CONV from [] target)
        in sswork (fn () => replay from)
             (fn ss => (proof expected (SIMP_CONV ss [] target);
                        proof (REFL target) (SIMP_CONV ss [] target);
                        proof (REFL target) (SIMP_CONV from [] target);
                        required (names ss = [SOME "matrix_bounded"]))) end
      | "history_limit" => let val from = limit 0 source in
          sswork (fn () => replay from)
            (fn ss => (required (#limit (traversedata_for_ss ss) = SOME 0);
                       checkSS (fn _ => true) ss;
                       checkSS no (unlimit ss);
                       checkSS (fn _ => true) from)) end
      | "history_collectors" => let
          val from = ((empty_ss ++ setup (SOME maker)
                         [reducer "matrix_collector"] ++ data)
                        -* ["matrix_missing"]) ++ drop
        in callbacks n 1 (sswork (fn () => replay from)
             (fn ss => (checkHistory
                [SOME "matrix_data",SOME "matrix_setup"] no ss;
                required (dpnames ss = [SOME "matrix_collector"]);
                checkSS no from))) end
      | "history_makers" => let
          val calls1 = ref 0
          val calls2 = ref 0
          fun firstMaker rw = (calls1 := !calls1 + 1; [rw])
          fun laterMaker rw = (calls2 := !calls2 + 1; [rw])
          val changed = name_ss "matrix_changed_maker"
                          (setup (SOME laterMaker) [])
          val late = name_ss "matrix_late" (namedRules rname rs)
          val from = empty_ss ++ setup (SOME firstMaker) [] ++ data ++
                     changed ++ late ++ drop
          val want = [SOME "matrix_late",SOME "matrix_changed_maker",
                      SOME "matrix_data",SOME "matrix_setup"]
          val {run,verify,...} = sswork (fn () => replay from)
            (fn ss => (checkHistory want no ss;
                       checkHistory (SOME "matrix_drop" :: want) no from))
          val old1 = ref 0
          val old2 = ref 0
          val _ = localCalls := (fn () => !calls1 + !calls2)
        in {run=run,verify=verify,
            beforeBatch=fn () => (old1 := !calls1; old2 := !calls2),
            afterBatch=fn count =>
              required (!calls1 - !old1 = count * 2 * n andalso
                        !calls2 - !old2 = count * n andalso
                        (!calls1 - !old1) + (!calls2 - !old2) =
                          count * 3 * n)} end
      | "history_theory_change" => let
          val saved = Context.snapshot ()
          val _ = Theory.link_parents ("matrix_ephemeral","matrix") []
          val from = source -* ["matrix_ephemeral.missing"]
          val present = Context.snapshot ()
          val _ = Context.restore saved
          val _ = (!theoryChange) "matrix_changed"
          val changed = Context.snapshot ()
          val slot = ref (Exn.capture replay from)
          fun verify () = let
            val _ = required (case !slot of
                Exn.Exn (HOL_ERR e) =>
                  Feedback.top_function_of e = "-*" andalso
                  Feedback.message_of e = "bad theory name: matrix_ephemeral"
              | _ => false)
            fun restored () =
              (Context.restore present;
               checkHistory [SOME "matrix_data"] no (replay from))
          in
            Portable.finally (fn () => Context.restore changed) restored ()
          end
          val _ = retaining (fn () => case !slot of
              Exn.Exn (HOL_ERR e) =>
                "error:" ^ printable (Feedback.top_function_of e) ^ ":" ^
                printable (Feedback.message_of e)
            | Exn.Exn _ => "exception"
            | Exn.Res ss => ssText ss)
            (fn () => case !slot of Exn.Res ss => useSS ss | _ => ())
        in basic (fn () => slot := Exn.capture replay from) verify end
      | _ => raise Fail "unknown history case"
    end
    fun storage () = let
      val slot = ref (SOME (empty_ss ++ frag))
      fun current () = valOf (!slot)
      fun raw () = let
        val _ = PolyML.fullGC ()
        val baseWords = PolyML.objSize empty_ss
        val fragWords = PolyML.objSize frag
        val ssWords = PolyML.objSize (current ())
        (* Equal-arity roots, with shared base and fragment removed. *)
        val anchor = PolyML.objSize (empty_ss,frag,empty_ss)
        val union = PolyML.objSize (empty_ss,frag,current ())
        val fa = PolyML.objSize (empty_ss,rs,empty_ss)
        val fu = PolyML.objSize (empty_ss,rs,frag)
        val _ = required (union >= anchor andalso fu >= fa)
        val _ = slot := NONE
        val _ = PolyML.fullGC ()
        val released = PolyML.objSize
          (empty_ss,frag,case !slot of NONE => empty_ss | SOME ss => ss)
        val _ = required (released = anchor)
        val fields = [n,baseWords,fragWords,ssWords,anchor,union,union-anchor,
                      fa,fu,fu-fa,released]
      in print ("@@MATRIX_STORAGE\tstorage_graph\t" ^
                String.concatWith "," (map Int.toString fields) ^ "\n");
         TextIO.flushOut TextIO.stdOut end
      val _ = rawStorage := raw
      val _ = retaining (fn () => ssText (current ()))
                        (fn () => useSS (current ()))
    in basic (fn () => slot := SOME (empty_ss ++ frag))
             (fn () => checkSS no (current ())) end
  in
    if String.isPrefix "frag_" label then
      (case label of
         "frag_create" => fragwork (fn () => rewrites rs) rs NONE checkFrag
       | "frag_named" => fragwork (fn () => named_rewrites "matrix_data" rs)
           rs (SOME "matrix_data") checkFrag
       | "frag_named_rules" => fragwork (fn () => namedRules rname rs)
           rs NONE checkFrag
       | "frag_record" => fragwork (fn () => SSFRAG
           {name=NONE,rewrs=map (fn th => (NONE,th)) rs,convs=[],ac=[],
            filter=NONE,dprocs=[],congs=[]}) rs NONE checkFrag
       | "frag_update" => fragwork
           (fn () => ssf_upd_rewrs List.rev data) (List.rev rs)
           (SOME "matrix_data") checkFrag
       | "frag_duplicate" => fragwork (fn () => merge_ss [frag,frag])
           (rs @ rs) NONE checkFrag
       | "frag_merge" => fragwork (fn () => merge_ss [frag,empty_ssfrag])
           rs NONE checkFrag
       | "frag_named_merge" => fragwork
           (fn () => named_merge_ss "matrix_merged" [data,data])
           (rs @ rs) (SOME "matrix_merged") checkFrag
       | "frag_ac" => acfrag (fn () => ac_ss acs)
       | "frag_ac_merge" => let val f = ac_ss acs in
           acfrag (fn () => merge_ss [f,f]) end
       | "frag_typebase" => typefrag false
       | "frag_type_lookup" => typefrag true
       | _ => raise Fail "unknown fragment case")
    else if String.isPrefix "compile_" label then compilation ()
    else if String.isPrefix "exclude_" label then exclusions ()
    else if String.isPrefix "history_" label then history ()
    else if label = "storage_graph" then storage ()
    else raise Fail "unknown matrix case"
  end
end
