(* Pure interpreted SML, compiled ONLY in the fresh RootInterpreted table.
 * No Foreign calls: the native interpreter_path_host.sml owns every C
 * endpoint. Dynamic count, size, action and escaping root are shared by
 * precompiled entry declarations. Preparation, outcome inspection and result
 * printing are never inside a measured interval.
 *
 * An exception raised by the bytecode interpreter cannot propagate into the
 * native frames above it (a pre-existing hybrid-mode limit), so a real
 * exhaustion Interrupt is caught here, inside the interpreted code.
 *)
structure Task29Path =
struct
val sentinel = Array.array (0, 0w0 : word)
val count = ref 0
val size = ref 0
val root = ref sentinel
val outcome = ref 0
fun noop () = ()
fun loop () = let
  fun go i = if i = 0 then ()
             else (root := Array.array (!size, 0wx25); go (i - 1))
in go (!count) end
val action = ref noop
fun clear () = (action := noop; root := sentinel; outcome := 0)
fun prepare k s = (count := k; size := s; root := sentinel; outcome := 0;
                   action := loop)
fun work () = (outcome := 0; (!action) (); outcome := 1)
val enabled = [Thread.Thread.EnableBroadcastInterrupt true,
               Thread.Thread.InterruptState Thread.Thread.InterruptAsynchOnce]
val synchronous = [Thread.Thread.EnableBroadcastInterrupt true,
                   Thread.Thread.InterruptState Thread.Thread.InterruptSynch]
val saved = ref (Thread.Thread.getAttributes ())
fun attempt () =
  ((saved := Thread.Thread.getAttributes ();
    outcome := 0;
    (Thread.Thread.setAttributes enabled; (!action) (); outcome := 1)
     handle Thread.Thread.Interrupt =>
       (Thread.Thread.setAttributes synchronous; outcome := 2));
   Thread.Thread.setAttributes (!saved))
(* outcome: 0 not run, 1 returned, 2 interrupted by a real exhaustion. *)
fun report label = let
  val a = !root
  val intact = Array.all (fn w => w = 0wx25) a
in
  print ("@@TASK29_PATH_RESULT_V1\t" ^ label ^ "\t" ^
         Int.toString (!outcome) ^ "\t" ^ Int.toString (Array.length a) ^
         "\t" ^ (if intact then "1" else "0") ^ "\n");
  TextIO.flushOut TextIO.stdOut
end
end;
