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

  (* Live words: the garbage collector's own marked live total.  The
     probe runs under `--debug gc --logfile $T33_GCLOG` (the driver sets
     both), and every full GC writes a header, a total and a closing line

       GC: Full GC, <n> words required <k> spaces
       GC: Mark: Total live data <N> words
       GC: Completed successfully

     (Poly/ML 5.9.2; PolyML.fullGC says "0 words required", a full GC
     the run time sets off itself says "<n> words required" with n > 0;
     a retried mark writes a second total after a "GC: Count error"
     line; a minor GC writes only a closing line).  A full GC is the
     lines from a header to the next closing line.  A reading takes the
     log size (log_start) immediately before its own three full GCs, and
     after them and getLocalStats reads the log from log_start: its
     words are the last total inside the THIRD full GC there, and
     log_end is the offset just past that GC's closing line.  Anything
     the run time logs between log_start and the first own GC, or after
     the third own GC (a full GC set off by reading the log, whose total
     would include the read buffers), is not the reading's: the third
     full GC is not the last one.  A reading with fewer than three
     complete full GCs, or no total in the third, fails loudly.  The
     line formats, the slice and the checks are the driver's replay
     again in task33_records.py (LOG_TOTAL, FULL_GC_HEAD, CLOSING,
     OWN_FULL_GCS, check_gc_log): every record's words must be the last
     total of the third full GC of its slice, and a slice with a full
     GC that is not an own one with exactly one total (a foreign GC, a
     retried mark) is a redraw.

     This is not the heap extent (size_heap - free_full - alloc) / 8, which
     earlier probes reported: the extent is live data plus holes.  The copy
     phase places immutable objects by the first object it copies, so
     immutable data can be left in a mutable space and moved out by a later
     full GC, leaving a counted hole (the ~509-word jump of the no-op
     kind), and new objects fill old holes, so the extent grows by less
     than the live data (the held deficits); see
     .agent-files/evidence/task33/noop-offset-diagnosis.md.  The extent,
     size_heap, free_full and alloc_free stay in the record, reported
     only.  alloc and gc_share are also recorded, and they do decide
     comparability: the share-pass rule of task33_records.py (equal alloc,
     gc_share not shrinking, design 8.9) judges whether two readings can
     be compared. *)
  val gclog_env = "T33_GCLOG"  (* task33_records.GCLOG_ENV *)
  val own_gcs = 3  (* task33_records.OWN_FULL_GCS *)
  val log_marker = "GC: Mark: Total live data "
  val log_unit = " words"
  val log_head = "GC: Full GC, "
  val log_closing = ["GC: Completed successfully",
                     "GC: Completed with insufficient space"]
  val log_stop = ref 0  (* the end of the previous reading *)
  fun log_fail path = Fail ("T33: cannot read GC log " ^ path)
  fun log_size path =
    Position.toInt (Posix.FileSys.ST.size (Posix.FileSys.stat path))
    handle OS.SysErr _ => raise log_fail path
  (* The bytes of the file from `from` on. *)
  fun log_from path from = let
    val fd = Posix.FileSys.openf (path, Posix.FileSys.O_RDONLY,
                                  Posix.FileSys.O.flags [])
            handle OS.SysErr _ => raise log_fail path
    fun loop acc = let val v = Posix.IO.readVec (fd, 65536) in
      if Word8Vector.length v = 0 then rev acc
      else loop (Byte.bytesToString v :: acc) end
    val parts = (Posix.IO.lseek (fd, Position.fromInt from,
                                 Posix.IO.SEEK_SET);
                 loop [])
      handle e => (Posix.IO.close fd;
                   raise (case e of OS.SysErr _ => log_fail path
                                  | _ => e))
    val _ = Posix.IO.close fd
  in String.concat parts end
  fun log_total line =
    if String.isPrefix log_marker line then
      let val rest = String.extract (line, size log_marker, NONE)
          val n = size rest - size log_unit
      in
        if n > 0 andalso String.extract (rest, n, NONE) = log_unit then
          (case LargeInt.fromString (String.substring (rest, 0, n)) of
               SOME w => if CharVector.all Char.isDigit
                              (String.substring (rest, 0, n))
                         then SOME w else NONE
             | NONE => NONE)
        else NONE
      end
    else NONE
  (* The last total inside the own_gcs-th full GC of text (a full GC
     runs from a header line to the next closing line; complete lines
     only) and the offset in text just past that GC's closing line. *)
  fun nth_gc text = let
    val n = size text
    fun line_end i = if i >= n then NONE
      else if String.sub (text, i) = #"\n" then SOME i
      else line_end (i + 1)
    (* closed: the full GCs closed so far; open_: NONE outside a full
       GC, else the last total seen in it *)
    fun scan pos closed open_ = case line_end pos of
        NONE => NONE
      | SOME e => let
          val line = String.substring (text, pos, e - pos)
          val next = e + 1
        in
          if String.isPrefix log_head line then scan next closed (SOME NONE)
          else case open_ of
              NONE => scan next closed NONE
            | SOME last =>
                (case log_total line of
                     SOME w => scan next closed (SOME (SOME w))
                   | NONE =>
                       if not (List.exists (fn c => c = line) log_closing)
                       then scan next closed open_
                       else if closed + 1 < own_gcs
                       then scan next (closed + 1) NONE
                       else (case last of SOME w => SOME (w, next)
                                        | NONE => NONE))
        end
  in scan 0 0 NONE end
  fun live phase = let
    val path = need gclog_env
    val start = log_size path
    val _ = if start >= !log_stop then ()
            else raise Fail ("T33: the GC log " ^ path ^ " shrank")
    val _ = List.app (fn _ => PolyML.fullGC ())
                     (List.tabulate (own_gcs, fn i => i))
    val s = PolyML.Statistics.getLocalStats ()
    val (words, stop) = case nth_gc (log_from path start) of
        SOME (w, off) => (w, start + off)
      | NONE => raise Fail ("T33: fewer than " ^ Int.toString own_gcs ^
                            " complete full GCs with a total in the GC log " ^
                            path ^ " for " ^ phase)
    val extent = (#sizeHeap s - #sizeHeapFreeLastFullGC s -
                  #sizeAllocation s) div 8
  in
    log_stop := stop;
    emit "live" [("phase", js phase), ("size_heap", jn (#sizeHeap s)),
                 ("free_full", jn (#sizeHeapFreeLastFullGC s)),
                 ("alloc", jn (#sizeAllocation s)),
                 ("alloc_free", jn (#sizeAllocationFree s)),
                 ("gc_share", ji (#gcSharePasses s)),
                 ("extent", jn extent), ("log_start", ji start),
                 ("log_end", ji stop), ("words", jn words)];
    words
  end

  (* A closure that keeps x reachable (a store is not optimised away). *)
  fun hold x = let val r = ref x in fn () => r := !r end
  (* T33_LEAK: every discarded object is kept in a global list, except
     those of the floor kind: the no-op kind is the harness's noise floor,
     not code under test, and must not leak.  The name is mirrored by
     task33_records.FLOOR_KIND (a test compares them). *)
  val floor_kind = "noop"
  val sink : (unit -> unit) list ref = ref []
  fun retain u = if leak then sink := u :: !sink else ()
  fun rname i = "t33_r" ^ Int.toString i

  (* R1: after one warm cycle, m build/use/discard cycles; then m objects
     held alive.  Each reading is after three full GCs. *)
  fun release m (name, make) = let
    fun cycle i = let
      val u = make i
    in (if name = floor_kind then () else retain u); u () end
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
