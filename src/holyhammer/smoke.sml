(* ========================================================================= *)
(* FILE          : smoke.sml                                                 *)
(* DESCRIPTION   : End-to-end smoke driver for HolyHammer                    *)
(* ========================================================================= *)

fun fresh_output () =
  let
    val path = OS.FileSys.tmpName ()
    val _ = OS.FileSys.remove path handle OS.SysErr _ => ()
  in
    path
  end

fun show_result (entry : hhEval.journal_entry) =
  print (#goal_id entry ^ " [" ^ #prover entry ^ "]: " ^ #szs entry ^
    (case #recon_ok entry of
         SOME true => ", reconstructed\n"
       | SOME false => ", reconstruction failed\n"
       | NONE => ", not reconstructed\n"))

fun main () =
  let
    val expdir = fresh_output ()
    val entries = hhEval.run_smoke {expdir = expdir, timeout = 30}
    val _ = app show_result entries
    val _ = print ("HolyHammer smoke passed " ^
      Int.toString (length entries) ^ "/" ^
      Int.toString (length hhEval.smoke_goals) ^ " goals\n")
  in
    OS.Process.success
  end

val status =
  main ()
  handle Interrupt => raise Interrupt
       | error =>
           (TextIO.output (TextIO.stdErr,
              "HolyHammer smoke failed: " ^ General.exnMessage error ^ "\n");
            OS.Process.failure)

val _ = OS.Process.exit status
