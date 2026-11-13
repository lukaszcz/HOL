(* Scenario "shadowed-load" of the fresh-load suite, kept in its own launcher
   so the sealed selftest.sml is unchanged.  Before any extension module is
   loaded, each basis name that HOL libraries re-export for toplevel `open`
   is rebound with an incompatible type; every added module must still load.
   Deliberately no static dependency on the simplifier. *)
open HolKernel testutils

val _ = boolTheory.TRUTH

fun obs key value = print ("OBS " ^ key ^ "=" ^
  String.translate (fn #"\n" => "\\n" | c => str c) value ^ "\n")
fun check label ok =
  (tprint label; if ok then OK () else die label)
fun env s =
  case OS.Process.getEnv s of
      SOME v => v
    | NONE => raise Fail ("missing environment variable " ^ s)
val scenario = env "SIMP_COMPAT_SCENARIO"
val _ = obs "scenario" scenario
val _ = check "scenario is shadowed-load" (scenario = "shadowed-load")
val _ = check "fail-fast test mode" (!diemode = ProcessExit)

fun observed stage f =
  let
    val old = !Feedback.WARNING_outstream
    val warnings = ref ([] : string list)
    val _ = Feedback.WARNING_outstream :=
      (fn s => (warnings := s :: !warnings; old s))
    val result = (SOME (f ()) handle e =>
      (obs (stage ^ ".exception")
         (General.exnName e ^ ": " ^ Feedback.exn_to_string e); NONE))
    val _ = Feedback.WARNING_outstream := old
    val _ = if Option.isSome result then obs (stage ^ ".exception") "none"
            else ()
    val _ = obs (stage ^ ".warnings") (Int.toString (length (!warnings)))
  in
    (Option.isSome result, null (!warnings))
  end
fun require_result label (succeeded,silent) =
  (check (label ^ " succeeds") succeeded;
   check (label ^ " without warnings") silent)

(* Basis names that HOL libraries designed for toplevel `open` re-export:
   patriciaLib.size, hurdUtils.concat and liteLib.foldr (found from the
   *Lib/*Utils signatures that re-export a basis toplevel value).  `load`
   compiles modules absent from the heap in the user's toplevel, so such
   modules must not use these names unqualified.  The static check
   tests/compatibility/interfaces/test_shadowed.py keeps its own copy of this
   list and compares it with this one. *)
val shadowed = ["size", "concat", "foldr"]

fun compile_string src =
  let
    val pos = ref 0
    fun next () =
      if !pos < String.size src
      then SOME (String.sub (src, !pos)) before pos := !pos + 1
      else NONE
  in
    PolyML.compiler
      (next, [PolyML.Compiler.CPNameSpace PolyML.globalNameSpace]) ()
  end
fun compiles src = (compile_string src; true) handle _ => false

(* The extension modules: every added source of this directory, found with
   the same name rules as the static check (extension, split*, SplitData and
   simpMarker* modules; not theory scripts). *)
fun is_extension f =
  let
    val {base,ext} = OS.Path.splitBaseExt f
    fun has sub = Substring.size (#2 (Substring.position sub
                                        (Substring.full base))) > 0
    fun prefix p = String.isPrefix p base
  in
    ext = SOME "sml" andalso base <> "selftest" andalso
    not (String.isSuffix "Script" base) andalso
    (has "Ext" orelse prefix "split" orelse base = "SplitData" orelse
     prefix "simpMarker")
  end
fun extension_modules dir =
  let
    val d = OS.FileSys.openDir dir
    fun loop acc =
      case OS.FileSys.readDir d of
          NONE => acc
        | SOME f => loop (if is_extension f then #base (OS.Path.splitBaseExt f)
                                                :: acc else acc)
    val names = loop [] before OS.FileSys.closeDir d
  in Listsort.sort String.compare names end

fun shadowed_load () =
  let
    val dir = OS.Path.dir (env "SIMP_COMPAT_PATH")
    val modules = extension_modules dir
    val _ = check "extension modules found" (length modules >= 12)
    val _ = List.app (fn n => obs "shadowed.module" n) modules
    (* Develop sources outside the added set (HolSat) use these names
       unqualified; load them first so only the added modules are tested. *)
    val _ = List.app Meta.load ["tautLib", "combinTheory", "refuteLib"]
    val _ = check "shadowing compiles" (List.all (fn n =>
      compiles ("val " ^ n ^ " = ();")) shadowed)
    val _ = check "shadowing is incompatible with the basis" (not
      (compiles ("val _ = size \"x\"; val _ = concat [];" ^
                 " val _ = foldr op+ 0 [];")))
  in
    List.app (fn m =>
      require_result ("shadowed-toplevel load of " ^ m)
        (observed ("load." ^ m) (fn () => Meta.load (OS.Path.concat (dir, m)))))
      modules
  end

val _ = shadowed_load ()
val _ = obs "result" "pass"
val _ = OS.Process.exit OS.Process.success
