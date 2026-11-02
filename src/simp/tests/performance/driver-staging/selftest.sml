(* Compile/execute the ACTUAL calibration/sample suffixes declaration by
 * declaration, as the ordinary loader does. Synthetic measured durations test
 * scheduling only; they are NEVER performance or allocation observations.
 * The compiler-entry serial must not change from first calibration to last
 * sample. Reverting to a top-level calibrated count is an executed negative
 * control. No instruction printing or unsafe runtime inspection is needed.
 *)
open testutils

structure DriverStaging =
struct
  exception CompilerDuringMeasurement
  exception ShortCalibration
  val serial = ref 0
  val first = ref (NONE : int option)
  val stages = ref ([] : (string * int) list)
  val fixed = ref (NONE : int option)
  val warmup = ref false
  val sink = ref 0
  val observations = ref ([] : (string * string list) list)
  val checks = ref 0
  fun required b = if b then () else raise ShortCalibration
  fun emit key fields = observations := (key,fields) :: !observations
  fun measured stage n = let
    val _ = case !first of
        NONE => first := SOME (!serial)
      | SOME s => if s = !serial then ()
                  else raise CompilerDuringMeasurement
    val _ = stages := (stage,n) :: !stages
    val _ = sink := !sink + n
  in (if n >= 2 then 0.25 else 0.01, [Int.toString n]) end
  fun reset count =
    (first := NONE; stages := []; fixed := count; warmup := false; sink := 0;
     observations := []; checks := 0)
end

fun check label yes = (tprint label; if yes then OK () else die label)
fun contents path = let
  val stream = TextIO.openIn path
in Portable.finally (fn () => TextIO.closeIn stream)
     TextIO.inputAll stream end
fun split marker text = let
  val (a,b) = Substring.position marker (Substring.full text)
  val _ = if Substring.isEmpty b then raise Fail ("missing " ^ marker) else ()
  val rest = Substring.triml (size marker) b
  val _ = if String.isSubstring marker (Substring.string rest)
          then raise Fail ("duplicate " ^ marker) else ()
in (Substring.string a,Substring.string rest) end
fun suffix text = let
  val (_,tail) = split "fun calibrate count =" text
  val (driver,_) = split "val _ = emit \"sink\"" tail
in "fun calibrate count =" ^ driver end
fun reverted driver = let
  val (a,b) = split "fun experiment () = let\n" driver
  val (body,tail) = split
    "in List.app sample (List.tabulate (samples,I)) end\n" b
  val (_,rest) = split "val _ = experiment ()" tail
in a ^ body ^ "val _ = List.app sample (List.tabulate (samples,I))\n" ^ rest
end
val prefix =
  "open DriverStaging\n" ^
  "val iterations = !fixed\nval fixedIterations = !fixed\n" ^
  "val warmup = !warmup\n" ^
  "val label = \"staging\"\nval selected = label\n" ^
  "val seconds = 0.2\nval samples = 3\nfun I x = x\n" ^
  "structure Paired = struct fun check label yes = " ^
  "(required yes; checks := !checks + 1) end\n"
fun execute source = let
  val {read,eof,...} = HOLSource.stringToReader
    {quietOpen=false,print=print} (prefix ^ source)
  fun loop () = if eof () then () else let
    val _ = DriverStaging.serial := !DriverStaging.serial + 1
    val messages = ref ([] : string list)
    val code = PolyML.compiler
      (read,
       [PolyML.Compiler.CPOutStream (fn s => messages := s :: !messages)])
      handle e => (List.app print (rev (!messages)); raise e)
    val _ = code ()
  in loop () end
in loop () end
fun expected n = let
  fun history k = ("calibration",k) ::
    (if k = n then [] else history (k*2))
in history 1 @ List.tabulate (3,fn _ => ("sample",n)) end
fun expectedWarmup n =
  ("calibration",n) :: List.tabulate (3,fn _ => ("sample",n))
fun run warm name driver count n = let
  val _ = DriverStaging.reset count
  val _ = DriverStaging.warmup := warm
  val _ = execute driver
  val actual = rev (!DriverStaging.stages)
  val total = List.foldl (fn ((_,k),a) => a+k) 0 actual
  val observations = rev (!DriverStaging.observations)
  val calibration = List.filter (fn (stage,_) => stage = "calibration") actual
  val expectedObservations = map (fn (_,k) =>
    ((if warm then "warmup.staging" else "calibration.staging"),
     [Int.toString k,Int.toString k])) calibration @
    List.tabulate (3,fn i =>
      ("batch.staging",map Int.toString [i,n,n]))
in
  check (name ^ " uninterrupted compiler serial")
    (Option.isSome (!DriverStaging.first));
  check (name ^ " complete calibration/sample schedule")
    (actual = (if warm then expectedWarmup n else expected n));
  check (name ^ " consumption and all result checks")
    (!DriverStaging.sink = total andalso !DriverStaging.checks = 3);
  check (name ^ " observation ordering/counts/indices")
    (observations = expectedObservations)
end
fun controls name driver = let
  val _ = run false (name ^ " adaptive") driver NONE 2
  val _ = List.app (fn n => run false (name ^ " fixed " ^ Int.toString n)
    driver (SOME n) n) [2,4,16]
  val _ = DriverStaging.reset (SOME 1)
  val short = (execute driver; false)
    handle DriverStaging.ShortCalibration => true
  val _ = check (name ^ " short calibration rejects before samples")
    (short andalso rev (!DriverStaging.stages) = [("calibration",1)] andalso
     !DriverStaging.checks = 0)
  val _ = DriverStaging.reset (SOME 4)
  val gap = (execute (reverted driver); false)
    handle DriverStaging.CompilerDuringMeasurement => true
in check (name ^ " actual top-level-count regression rejects")
  (gap andalso rev (!DriverStaging.stages) =
   [("calibration",1),("calibration",2),("calibration",4)] andalso
   !DriverStaging.checks = 0)
end
(* The warmup schedule: one recorded batch of N, any N, then the samples. *)
fun warmControls name driver = let
  val _ = List.app (fn n => run true (name ^ " warmup " ^ Int.toString n)
    driver (SOME n) n) [3,16]
  val _ = DriverStaging.reset (SOME 1)
  val _ = DriverStaging.warmup := true
  val short = (execute driver; false)
    handle DriverStaging.ShortCalibration => true
  val _ = check (name ^ " short warm-up rejects before samples")
    (short andalso rev (!DriverStaging.stages) = [("calibration",1)] andalso
     !DriverStaging.checks = 0)
  val _ = DriverStaging.reset (SOME 4)
  val _ = DriverStaging.warmup := true
  val gap = (execute (reverted driver); false)
    handle DriverStaging.CompilerDuringMeasurement => true
in check (name ^ " warm-up top-level-count regression rejects")
  (gap andalso rev (!DriverStaging.stages) = [("calibration",4)] andalso
   !DriverStaging.checks = 0)
end
val root = case OS.Process.getEnv "TASK29_STAGING_ROOT" of
    SOME path => path
  | NONE => raise Fail "set TASK29_STAGING_ROOT to the configured HOL root"
val _ = List.app (fn name => let
    val driver = suffix (contents
      (OS.Path.concat (root,"src/simp/tests/performance/" ^ name)))
  in (controls name driver; warmControls name driver) end)
  ["MatrixPerformance.sml","ClientPerformance.sml"]
val _ = print "@@TASK29_DRIVER_STAGING\tcomplete\t56\n"
