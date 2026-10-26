(* Hybrid native/bytecode control, loaded by a Holmake/testutils launcher.
 * No full HOL rebuild. The driver supplies sealed source/body/host/shim
 * paths and verifies the actual mapped runtime. This file does NOT establish
 * source/image lineage or full allocator completeness.
 *
 * Pinned polyml-5.9.2-2 recipe: RootInterpreted.ML selects GCode=ByteCode;
 * mlsource/BuildAll.sml creates Make.makeGEnv, Initialise.initGlobalEnv with
 * intIsArbitraryPrecision=false, then MLCompiler.useIntoEnv BuildBasis.sml.
 * We follow that recipe but never start rootFunction/the interactive shell.
 * The compiler itself is bootstrapped by the existing native compiler; its
 * generated basis and workload use the bytecode backend in a FRESH gEnv.
 * The dynamically loaded NATIVE host precompiles declaration-entry closures
 * and brackets only their execution/ignored result, never compilation or
 * declaration installation. Interpreted SML never invokes Foreign wrappers.
 * No RunCall casts, compiler-mode guesses or counter writes.
 *)
fun required name =
  case OS.Process.getEnv name of
      SOME p => if OS.Path.isAbsolute p then p
                else raise Fail (name ^ " must be absolute")
    | NONE => raise Fail ("set " ^ name)
val sourcePath = required "TASK29_ALLOC_SOURCE"
val bodyPath = required "TASK29_ALLOC_BODY"
val hostPath = required "TASK29_ALLOC_HOST"
val branchPath = required "TASK29_ALLOC_BRANCH_HOST"
val _ = required "TASK29_ALLOC_SHIM"
val oldDirectory = OS.FileSys.getDir ()
(* Capture the HOST compiler before loading the compiler sources. Names Make,
 * Initialise and MLCompiler become available only dynamically after use.
 *)
val hostCompiler = PolyML.compiler
val hostUse = PolyML.use
fun smlString s = "\"" ^ String.toString s ^ "\""
val recipe =
  "val Task29InterpreterTable : Make.gEnv = Make.makeGEnv (); " ^
  "val () = Initialise.initGlobalEnv " ^
  "{globalTable=Task29InterpreterTable, intIsArbitraryPrecision=false}; " ^
  "val () = MLCompiler.useIntoEnv Task29InterpreterTable [] " ^
  "\"mlsource/BuildBasis.sml\"; " ^
  "val () = MLCompiler.useIntoEnv Task29InterpreterTable [] " ^
  smlString (OS.Path.mkRelative {path=bodyPath, relativeTo=sourcePath}) ^ ";"
fun executeText text = let
  val input = TextIO.openString text
  fun loop () = if TextIO.endOfStream input then ()
    else (hostCompiler (fn () => TextIO.input1 input, []) (); loop ())
in
  (loop () before TextIO.closeIn input)
  handle ex => (TextIO.closeIn input; raise ex)
end
val _ =
  ((OS.FileSys.chDir sourcePath;
    (* ConcIsaLib narrows Thread to Thread.Thread. Restore its saved full
     * PolyThread alias for the pinned compiler's Thread.Thread/Mutex uses.
     * Also bypass HOL's source-transforming QUse for Root's nested uses.
     * This is a dedicated launcher process, not an interactive HOL session.
     *)
    executeText ("structure Thread = PolyThread; " ^
                 "structure Word8 = PolyWord8; val use = PolyML.use;");
    hostUse "RootInterpreted.ML";
    executeText recipe;
    (* Native loader: host sees the dynamically created compiler and table.
     * Do not compile this file into Task29InterpreterTable.
     *)
    hostUse hostPath;
    hostUse branchPath;
    OS.FileSys.chDir oldDirectory)
   handle ex => (OS.FileSys.chDir oldDirectory; raise ex))
val _ = testutils.tprint
  "interpreted basis/workload completed without exception"
val _ = testutils.OK ()
