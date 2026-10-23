(* Untimed TASK28 runtime instrumentation. Load in both private selections.
   beforeBatch precedes start*Timer; afterBatch follows ALL check*Timer calls
   and precedes workload verification (which can itself collect).
   sizeHeap/free fields are GC-updated heap observations, NOT allocation
   totals. Allocation-area capacity/free space is also NOT allocated bytes.
   VmHWM is the process lifetime maximum: startup, loading, verification and
   other batches all contribute. Its delta is NOT an exact temporary peak.
   Reading /proc and statistics is not atomic and allocates outside timing. *)
structure RuntimeMetrics = struct
  type snapshot =
    {gcFullGCs:int, gcPartialGCs:int, gcSharePasses:int,
     sizeHeap:LargeInt.int, sizeHeapFreeLastGC:LargeInt.int,
     sizeHeapFreeLastFullGC:LargeInt.int, sizeAllocation:LargeInt.int,
     sizeAllocationFree:LargeInt.int, sizeStacks:LargeInt.int,
     sizeCode:LargeInt.int, rssBytes:LargeInt.int option,
     hwmBytes:LargeInt.int option}

  fun procStatus () = let
    val input = TextIO.openIn "/proc/self/status"
    fun lines acc = case TextIO.inputLine input of
        NONE => acc | SOME line => lines (line :: acc)
    val contents = (lines [] handle e => (TextIO.closeIn input; raise e))
    val _ = TextIO.closeIn input
    fun field key = let
      val matches = List.mapPartial (fn line =>
        case String.tokens Char.isSpace line of
          [name,value,"kB"] => if name = key then SOME value else NONE
        | _ => NONE) contents
    in case matches of
         [value] => if String.size value > 0 andalso
                      CharVector.all Char.isDigit value then
           Option.map (fn n => n * 1024) (LargeInt.fromString value)
           else NONE
       | _ => NONE
    end
  in case (field "VmRSS:",field "VmHWM:") of
       (SOME rss,SOME hwm) => (SOME rss,SOME hwm)
     | _ => (NONE,NONE)
  end handle IO.Io _ => (NONE,NONE) | OS.SysErr _ => (NONE,NONE)

  (* Keep the allocating /proc read on the OUTSIDE of the GC-counter
     interval. A few record/timer operations still separate counter reads
     from timer boundaries; these are batch-boundary counters, not a claim
     of cycle-exact attribution. Never force a GC inside a snapshot. *)
  fun capture statsFirst : snapshot = let
    val (s,(rss,hwm)) = if statsFirst then let
        val stats = PolyML.Statistics.getLocalStats ()
      in (stats,procStatus ()) end
      else let val rss = procStatus ()
      in (PolyML.Statistics.getLocalStats (),rss) end
  in {gcFullGCs = #gcFullGCs s, gcPartialGCs = #gcPartialGCs s,
      gcSharePasses = #gcSharePasses s, sizeHeap = #sizeHeap s,
      sizeHeapFreeLastGC = #sizeHeapFreeLastGC s,
      sizeHeapFreeLastFullGC = #sizeHeapFreeLastFullGC s,
      sizeAllocation = #sizeAllocation s,
      sizeAllocationFree = #sizeAllocationFree s,
      sizeStacks = #sizeStacks s, sizeCode = #sizeCode s,
      rssBytes=rss,hwmBytes=hwm} end
  fun beforeBatch () = capture false

  (* All string values below are fixed literals or validated stage names. *)
  fun quoted s = "\"" ^ s ^ "\""
  fun object fields = "{" ^ String.concatWith ","
    (map (fn (k,v) => quoted k ^ ":" ^ v) fields) ^ "}"
  fun optional NONE = "null" | optional (SOME n) = LargeInt.toString n
  fun json (s:snapshot) = object
    [("gcFullGCs",Int.toString (#gcFullGCs s)),
     ("gcPartialGCs",Int.toString (#gcPartialGCs s)),
     ("gcSharePasses",Int.toString (#gcSharePasses s)),
     ("sizeHeap",LargeInt.toString (#sizeHeap s)),
     ("sizeHeapFreeLastGC",LargeInt.toString (#sizeHeapFreeLastGC s)),
     ("sizeHeapFreeLastFullGC",
       LargeInt.toString (#sizeHeapFreeLastFullGC s)),
     ("sizeAllocation",LargeInt.toString (#sizeAllocation s)),
     ("sizeAllocationFree",LargeInt.toString (#sizeAllocationFree s)),
     ("sizeStacks",LargeInt.toString (#sizeStacks s)),
     ("sizeCode",LargeInt.toString (#sizeCode s)),
     ("rssBytes",optional (#rssBytes s)),
     ("hwmBytes",optional (#hwmBytes s))]
  fun emit prefix data =
    (print (prefix ^ "\t" ^ data ^ "\n"); TextIO.flushOut TextIO.stdOut)
  fun afterBatch (stage,iterations,prior:snapshot) = let
    val after = capture true
    val _ = if (stage = "calibration" orelse stage = "sample") andalso
               iterations > 0 then () else raise Fail "invalid runtime batch"
  in emit "@@MATRIX_RUNTIME" (object
       [("schema","1"),("stage",quoted stage),
        ("iterations",Int.toString iterations),
        ("before",json prior),("after",json after)]) end

  (* Actual weak collection, not reachable-word subtraction. The weak referent
     is a fresh simpset REF captured by a known ordinary conversion wrapper.
     Weak.weak only accepts references, not opaque simpsets. This proves
     release of the controlled wrapper root, not every internal net,
     historical graph, arbitrary client closure or global/shared base object.
     No closure introspection, address casts or unsafe operations are used. *)
  fun release () = let
    open HolKernel boolLib simpLib
    fun prepare () = let
      val a = mk_var ("runtime_release_a",bool)
      val b = mk_var ("runtime_release_b",bool)
      val rule = ASSUME (mk_eq (a,b))
      val root = ref (pureSimps.pure_ss ++ rewrites [rule])
      val weak = Weak.weak (SOME root)
      val holder = ref (SOME (fn tm => SIMP_CONV (!root) [] tm))
    in (weak,holder,a,rule) end
    fun exercise (holder,a,rule) = case !holder of
        NONE => raise Fail "release probe lost retained closure"
      | SOME cv => let val th = cv a in
          if aconv (concl th) (concl rule) andalso
             HOLset.equal (hypset th,hypset rule) then ()
          else raise Fail "release probe proof mismatch"
        end
    (* Return from the retention phase before collecting: dead ML stack
       temporaries from exercising a conversion can otherwise keep it live. *)
    (* The recursive boundary prevents Poly/ML inlining the retained
       conversion's stack frame into the subsequent collection phase. *)
    fun retainedPhase depth = if depth > 0 then retainedPhase (depth-1)
    else let
      val (weak,holder,a,rule) = prepare ()
      val start = PolyML.Statistics.getLocalStats ()
      val _ = PolyML.fullGC ()
      val retained = Option.isSome (!weak)
      val _ = exercise (holder,a,rule)
      val _ = if retained then ()
              else raise Fail "weak retention control failed"
      val _ = holder := NONE
    in (weak,retained,#gcFullGCs start) end
    val (weak,retained,start) = retainedPhase 1
    val _ = List.app (fn _ => PolyML.fullGC ()) [1,2,3]
    val collected = not (Option.isSome (!weak))
    val finish = PolyML.Statistics.getLocalStats ()
    val fullGCs = #gcFullGCs finish - start
    val status = if collected then "pass" else "blocked"
    val reason = if collected then "" else
      "weak referent survived three explicit full collections"
    val _ = emit "@@MATRIX_RELEASE" (object
      [("schema","1"),("scope",quoted "controlled-simpset-ref-closure"),
       ("retained",Bool.toString retained),
       ("collected",Bool.toString collected),
       ("fullGCs",Int.toString fullGCs),("releaseCollections","3"),
       ("status",quoted status),("blockedReason",quoted reason)])
  in {retained=retained,collected=collected,fullGCs=fullGCs,
      status=status,blockedReason=reason} end
end
