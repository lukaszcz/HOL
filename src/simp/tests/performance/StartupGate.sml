(* TASK31 ordinary-startup allocation client, run as `hol run StartupGate.sml`
   on the private patched runtime (see startup_gate.py). One process measures
   one kind (GATE_KIND):
     hol-startup    hol.state: the absolute counter at the first user code
     hol-first-use  hol.state: first and second SIMP_CONV / SIMP_TAC
     load-simpLib   hol.state0: a fresh `load "simpLib"` and `load
                    "pureSimps"`, then the same calls
     load-congLib   hol.state0: a fresh `load "congLib"`
     files-simpLib  hol.state0: `load "simpLib"` with a bracket around every
                    source file the loader uses (attribution, not a gate)
   The first lines are the whole prologue before the `startup` record: the
   foreign setup and one snapshot, so that startup is the words of the
   process load up to the first user code (plus compiling these lines).
   Later brackets are the TASK29B ones: the counter is read from C storage
   after the bracket has ended, and no decoding, output or label work
   happens inside. Everything is printed at the very end, outside every
   bracket. *)
val library = Foreign.loadLibrary
  (valOf (OS.Process.getEnv "TASK29_ALLOC_SHIM"))
fun symbol name = Foreign.getSymbol library name
val startCall = Foreign.buildCall0
  (symbol "task29_alloc_start", (), Foreign.cVoid)
val endCall = Foreign.buildCall0
  (symbol "task29_alloc_end", (), Foreign.cVoid)
val getCall = Foreign.buildCall1
  (symbol "task29_alloc_get", Foreign.cInt, Foreign.cUint64Large)
val _ = (startCall (); endCall ())
val startupWords = List.tabulate (8, getCall)

val kind = valOf (OS.Process.getEnv "GATE_KIND")
val runtimePath = Foreign.buildCall0
  (symbol "task29_alloc_runtime", (), Foreign.cString)
val abiCheck = Foreign.buildCall0
  (symbol "task29_alloc_abi_check", (), Foreign.cInt)
val getPath = Foreign.buildCall1
  (symbol "task29_alloc_path_get", Foreign.cInt, Foreign.cUint64Large)
val identity = runtimePath ()
val abi = abiCheck ()
val _ = if abi = 15 then () else raise Fail "allocator ABI check"

val log = ref ([] : (string * LargeInt.int list * LargeInt.int list) list)
fun bracket name work = let
  val _ = startCall ()
  val _ = work ()
  val _ = endCall ()
  val s = List.tabulate (8, getCall)
  val e = List.tabulate (8, fn i => getCall (8 + i))
in log := (name, s, e) :: !log end

val _ = log := [("startup", startupWords, startupWords)]
val _ = bracket "empty" (fn () => ())

(* Terms and the goal are built outside every bracket. *)
val gp = Term.mk_var ("gate_p", Type.bool)
val gtm = boolSyntax.mk_conj (boolSyntax.T, gp)
val gtt = boolSyntax.mk_conj (boolSyntax.T, boolSyntax.T)
val grules = [boolTheory.AND_CLAUSES]
val result = ref (NONE : Thm.thm option)
val proved = ref (NONE : Thm.thm option)
val convRef = ref (fn () => ())
val tacRef = ref (fn () => ())
(* StartupGateUse.sml sets both once simpLib is there to be compiled
   against; its compilation happens between brackets. *)
fun prepare () = Meta.qquse (valOf (OS.Process.getEnv "GATE_USE"))

fun use1 () = (bracket "SIMP_CONV_1" (!convRef);
               bracket "SIMP_TAC_1" (!tacRef))
fun use2 () = (bracket "SIMP_CONV_2" (!convRef);
               bracket "SIMP_TAC_2" (!tacRef))

(* The loader step of Meta.load with every `use` bracketed. *)
fun tracedUse path = bracket path (fn () => Meta.qquse path)
val _ = if kind = "hol-startup" then ()
  else if kind = "load-congLib" then
    bracket "load_congLib" (fn () => Meta.load "congLib")
  else if kind = "load-simpLib" then
    (bracket "load_simpLib" (fn () => Meta.load "simpLib");
     bracket "load_pureSimps" (fn () => Meta.load "pureSimps");
     prepare (); use1 (); use2 ())
  else if kind = "files-simpLib" then Meta.loadPlan tracedUse "simpLib"
  else if kind = "hol-first-use" then (prepare (); use1 (); use2 ())
  else raise Fail ("unknown GATE_KIND " ^ kind)

(* Everything below is outside every bracket. *)
fun fields xs = String.concatWith "," (map LargeInt.toString xs)
fun emit event name payload =
  print (String.concatWith "\t" ["@@GATE", kind, event, name, payload] ^ "\n")
val _ = List.app (fn (name, s, e) => emit "alloc" name
                     (fields s ^ ";" ^ fields e)) (List.rev (!log))
val _ = emit "holdir" "path" Systeml.HOLDIR
val _ = emit "foreign" "path"
  (LargeInt.toString (getPath (32 + 3 + 27)) ^ "," ^
   LargeInt.toString (getPath (32 + 31)))
fun valid goal th = Term.aconv (Thm.concl th) goal andalso null (Thm.hyp th)
val _ = (case (!result, !proved) of
    (SOME th, SOME th2) =>
      emit "result" "ok"
        (if valid (boolSyntax.mk_eq (gtm, gp)) th andalso valid gtt th2
         then "true" else "false")
  | (NONE, NONE) => emit "result" "none" "-"
  | _ => emit "result" "unexpected" "-")
val loaded = Meta.loaded ()
val _ = emit "loaded" "count" (Int.toString (length loaded))
val _ = emit "loaded" "modules" (String.concatWith "," loaded)
val records = map #1 (Binarymap.listItems (Meta.fileDirMap ()))
val _ = emit "files" "count" (Int.toString (length records))
val _ = emit "files" "names" (String.concatWith "," records)
val structs = map #1 (#allStruct PolyML.globalNameSpace ())
val _ = emit "structures" "count" (Int.toString (length structs))
val _ = emit "structures" "names" (String.concatWith "," structs)
val maps = TextIO.openIn "/proc/self/maps"
fun emitMaps () = case TextIO.inputLine maps of
    NONE => ()
  | SOME line => (print ("@@TASK29_ALLOC_MAP_V1\t" ^ line); emitMaps ())
val _ = print ("@@TASK29_ALLOC_RUNTIME_V1\t" ^ identity ^ "\n")
val _ = emitMaps ()
val _ = TextIO.closeIn maps
val _ = print "@@GATE\tend\n"
