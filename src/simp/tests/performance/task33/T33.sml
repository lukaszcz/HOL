(* TASK33 probe support (harness only): one JSON record per stdout line,
   "@@T33<TAB>{...}".  Develop APIs only.  No simplifier dependency, so
   it loads on every heap.  Control switches come from the environment.
   Not used by the timing probes (T33Load, T33Trivial), whose compile cost
   is inside the measured process. *)
structure T33 =
struct
  open HolKernel

  fun js s = "\"" ^ String.translate
    (fn #"\"" => "\\\"" | #"\\" => "\\\\"
      | c => if Char.ord c < 32 then " " else str c) s ^ "\""
  fun jl f xs = "[" ^ String.concatWith "," (map f xs) ^ "]"
  fun jo fields = "{" ^ String.concatWith ","
    (map (fn (k, v) => js k ^ ":" ^ v) fields) ^ "}"
  fun neg s = String.map (fn #"~" => #"-" | c => c) s
  fun ji (n : int) = neg (Int.toString n)
  fun jn (n : LargeInt.int) = neg (LargeInt.toString n)
  fun jb b = if b then "true" else "false"
  fun jopt f NONE = "null" | jopt f (SOME x) = f x

  fun env name = OS.Process.getEnv name
  fun need name = case env name of
      SOME s => s
    | NONE => raise Fail ("T33: missing " ^ name)
  fun switch name = case env name of
      NONE => false | SOME "0" => false | SOME "1" => true
    | SOME s => raise Fail ("T33: bad " ^ name ^ "=" ^ s)
  val graph_extra = switch "T33_GRAPH_EXTRA"
  val leak = switch "T33_LEAK"
  val hook = switch "T33_HOOK"

  fun need_int name lo = case Int.fromString (need name) of
      SOME n => if n >= lo then n else raise Fail ("T33: bad " ^ name)
    | NONE => raise Fail ("T33: bad " ^ name)

  val probe = ref ""
  val kind = ref ""
  (* quietly f: f's records are not printed (a warm-up run). *)
  val quiet = ref false
  fun quietly f = let
    val _ = quiet := true
    val r = f () handle e => (quiet := false; raise e)
  in quiet := false; r end
  fun emit record fields =
    if !quiet then () else
    (print ("@@T33\t" ^ jo (("record", js record) :: ("probe", js (!probe))
       :: ("kind", js (!kind)) :: fields) ^ "\n");
     TextIO.flushOut TextIO.stdOut)

  fun install_hook () =
    if hook then Theory.register_hook ("t33.hook", fn _ => ()) else ()
  val switches_json = jo [("graph_extra", jb graph_extra),
                          ("leak", jb leak), ("hook", jb hook)]

  (* The header: probe, process kind, heap root, switches, parameters. *)
  fun start (p, k, params) =
    (probe := p; kind := k; install_hook ();
     emit "probe" [("holdir", js Systeml.HOLDIR),
                   ("switches", switches_json), ("params", jo params)])
  fun finish () = emit "done" []

  fun check label ok value =
    (emit "check" [("check", js label), ("ok", jb ok),
                   ("value", js value)];
     if ok then () else raise Fail ("T33 check failed: " ^ label))
  fun share () = #gcSharePasses (PolyML.Statistics.getLocalStats ())
  fun same (a, b) = aconv (concl a) (concl b) andalso
    HOLset.equal (hypset a, hypset b)

  (* A tactic run on a goal in the present context (no current theory). *)
  fun solve tac goal = let val (gl, vf) = tac goal (Context.snapshot ())
    in if null gl then vf [] else raise Fail "T33: tactic left goals" end

  (* Live words after three full GCs: (size_heap - free_full - alloc) / 8.
     free_full is the free space of the local spaces when the last full GC
     ended; that GC deletes every space it emptied (memmgr.cpp
     RemoveEmptyLocals), and the allocation spaces present afterwards were
     created later, so they are counted in size_heap and alloc but not in
     free_full: the formula then does not depend on how many allocation
     segments there are.  A space that kept data through the GC would be
     counted in free_full as well, and the formula would be low by its free
     words.  Such a space is not a whole 1 MB segment (memmgr.cpp:136), so
     a reading is comparable only when alloc is a whole number of segments,
     and is retried a few times and otherwise emitted with comparable = false
     (the validator refuses such a process as not comparable: a redraw, not
     a failure of the probe).  alloc_free = alloc says nothing about this:
     after a GC both counters are incremented with the same free value
     (gc.cpp:295), and it differs only when the 1 s periodic update
     (statistics.cpp:646) ran in between.  The record keeps alloc and
     gc_share, so that readings can be checked to be comparable. *)
  val segment = 1048576 : LargeInt.int
  fun live phase = let
    fun settle tries = let
      val _ = List.app (fn _ => PolyML.fullGC ()) [1, 2, 3]
      val s = PolyML.Statistics.getLocalStats ()
      val fresh = #sizeAllocationFree s = #sizeAllocation s andalso
                  LargeInt.mod (#sizeAllocation s, segment) = 0
    in
      if fresh orelse tries <= 0 then (s, fresh) else settle (tries - 1)
    end
    val (s, fresh) = settle 8
    val words = (#sizeHeap s - #sizeHeapFreeLastFullGC s -
                 #sizeAllocation s) div 8
  in
    emit "live" [("phase", js phase), ("size_heap", jn (#sizeHeap s)),
                 ("free_full", jn (#sizeHeapFreeLastFullGC s)),
                 ("alloc", jn (#sizeAllocation s)),
                 ("alloc_free", jn (#sizeAllocationFree s)),
                 ("gc_share", ji (#gcSharePasses s)),
                 ("comparable", jb fresh),
                 ("words", jn words)];
    words
  end

  (* A closure that keeps x reachable (a store is not optimised away). *)
  fun hold x = let val r = ref x in fn () => r := !r end
  (* T33_LEAK: every discarded object is kept in a global list. *)
  val sink : (unit -> unit) list ref = ref []
  fun retain u = if leak then sink := u :: !sink else ()
  fun rname i = "t33_r" ^ Int.toString i

  (* R1: after one warm cycle, m build/use/discard cycles; then m objects
     held alive.  Each reading is after three full GCs. *)
  fun release m (name, make) = let
    fun cycle i = let val u = make i in retain u; u () end
    fun go i = if i > m then () else (cycle i; go (i + 1))
    val _ = cycle 0
    val first = live (name ^ ".before")
    val _ = go 1
    val after = live (name ^ ".after")
    val us = List.tabulate (m, fn i => make (m + 1 + i))
    val _ = List.app (fn u => u ()) us
    val held = live (name ^ ".held")
    val _ = ignore (length us)
  in
    emit "release" [("release", js name), ("m", ji m),
                    ("before", jn first), ("after", jn after),
                    ("held", jn held)]
  end

  (* L1/L3/S2: loaded map, registries, global names, structure sizes.
     sizes: absolute objSize of each structure and signature (reported
     only: it counts the code and global state reachable from them).
     anchored: D is the declared structures (ThmAttribute and Cond_rewr,
     structure and signature) and Context.snapshot ().  rows: for every
     structure X outside D, the exclusive part objSize ((D, X)) -
     objSize ((D, D)).  total: the closure total U = objSize ((D, [X1,
     ..., Xn])) over all of them (a list, so n cons cells of 3 words are
     constant).  k repeats in one image, repeat_ok when they agree; total
     and repeat_ok are null when D is not loaded (not applicable). *)
  val sized = ["ThmAttribute", "Cond_rewr", "simpLib", "Traverse",
               "Travrules", "Opening", "boolSimps", "pureSimps"]
  val declared = ["ThmAttribute", "Cond_rewr"]
  val repeats = 3
  fun anchored () = let
    val ns = PolyML.globalNameSpace
    val others = List.filter (fn n => not (List.exists (fn d => d = n)
                                             declared)) sized
    fun both n = (#lookupStruct ns n, #lookupSig ns n)
    val d = case (both "ThmAttribute", both "Cond_rewr") of
        ((SOME a, SOME b), (SOME c, SOME e)) =>
          SOME ((a, b, c, e), Context.snapshot ())
      | _ => NONE
    val found = map (#lookupStruct ns) others
    fun once dv = let
      val dd = PolyML.objSize (dv, dv)
      fun one NONE = NONE
        | one (SOME v) = SOME (PolyML.objSize (dv, v) - dd)
      val total = if List.all Option.isSome found
                  then SOME (PolyML.objSize (dv, map valOf found))
                  else NONE
    in (dd, total, map one found) end
    val reps = case d of
        NONE => []
      | SOME dv => List.tabulate (repeats, fn _ => once dv)
    fun col i = map (fn (_, _, xs) => List.nth (xs, i)) reps
    fun vals i = if null reps orelse List.exists (not o Option.isSome)
                                       (col i) then NONE
                 else SOME (map valOf (col i))
    fun constant xs = case xs of
        [] => true | x :: r => List.all (fn y => y = x) r
    val rows = List.tabulate (length others,
                              fn i => (List.nth (others, i), vals i))
    val totals = map #2 reps
    val ok = not (null reps) andalso constant (map #1 reps) andalso
             constant totals andalso
             List.all (fn (_, v) => case v of NONE => true
                                            | SOME xs => constant xs) rows
  in
    jo [("d", jl js declared),
        ("d_vals", if null reps then "null" else jl ji (map #1 reps)),
        ("total", if null reps orelse List.exists (not o Option.isSome)
                                         totals
                  then "null" else jl ji (map valOf totals)),
        ("rows", jl (fn (n, v) => jo [("name", js n),
                                      ("vals", jopt (jl ji) v)]) rows),
        ("repeat_ok", if null reps then "null" else jb ok)]
  end

  fun registry () = let
    val ns = PolyML.globalNameSpace
    val words = live "registry"
    fun names f = Lib.sort (fn a => fn b => a <= b) (map #1 (f ()))
    fun size lookup name = case lookup name of
        SOME v => SOME (PolyML.objSize v) | NONE => NONE
    fun sizes name = jo [("name", js name),
      ("struct", jopt ji (size (#lookupStruct ns) name)),
      ("sig", jopt ji (size (#lookupSig ns) name))]
    fun strs xs = jl js xs
  in
    emit "registry"
      [("loaded", strs (Meta.loaded ())),
       ("files", jl (fn (f, d) => jl js [f, d])
                    (Binarymap.listItems (Meta.fileDirMap ()))),
       ("listeners", strs (map #1 (Listener.listeners Theory.delta_hook))),
       ("attributes", strs (ThmAttribute.all_attributes ())),
       ("set_types", strs (ThmSetData.all_set_types ())),
       ("structures", strs (names (#allStruct ns))),
       ("signatures", strs (names (#allSig ns))),
       ("functors", strs (names (#allFunct ns))),
       ("sizes", jl sizes sized),
       ("anchored", anchored ())]
  end
end
