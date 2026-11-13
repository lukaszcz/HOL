(* ===================================================================== *)
(* FILE          : hhReconstruct.sml                                     *)
(* DESCRIPTION   : Reconstruct a proof from the lemmas given by an ATP   *)
(*                 and optionally minimize them.                         *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

structure hhReconstruct :> hhReconstruct =
struct

open HolKernel Dep Tag boolLib aiLib smlExecute smlTimeout smlRedirect
  mlThmData psMinimize

val ERR = mk_HOL_ERR "hhReconstruct"

(* --------------------------------------------------------------------------
   Settings
   -------------------------------------------------------------------------- *)

val reconstruct_flag = ref true
val minimization_timeout = ref 1.0
val reconstruction_timeout = ref 1.0

(*----------------------------------------------------------------------------
   Minimization and pretty-printing
 -----------------------------------------------------------------------------*)

val TC_OFF = trace ("show_typecheck_errors", 0)
(* the trace setting, the timeout and the handler all have to span the
   context application, which is when the tactic does its work *)
fun timeout_tactic t tac g =
  let val ctxt = Context.snapshot() in
    SOME (fst (timeout t (TC_OFF (Lib.C tac ctxt)) g))
  end
  handle Interrupt => raise Interrupt | _ => NONE

type settings =
  {minimize : bool, preplay_timeout : real, minimize_timeout : real}

fun hh_reconstruct_with ({minimize, preplay_timeout, minimize_timeout}
                         : settings) lemmas g =
  if not (!reconstruct_flag)
  then (print_endline (mk_metis_call lemmas);
        raise ERR "hh_minimize" "reconstruction off")
  else
    let
      val stac = mk_metis_call lemmas
      val newstac =
        if minimize then psMinimize.minimize_stac minimize_timeout stac g []
        else stac
      val tac = tactic_of_sml 1.0 newstac
    in
      case timeout_tactic preplay_timeout tac g of
        SOME _ => (newstac,tac)
      | NONE   => raise ERR "hh_reconstruct" "reconstruction failed"
    end

fun hh_reconstruct lemmas =
  hh_reconstruct_with
    {minimize = true, preplay_timeout = !reconstruction_timeout,
     minimize_timeout = !minimization_timeout} lemmas

end
