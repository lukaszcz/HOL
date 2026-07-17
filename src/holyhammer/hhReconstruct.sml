(* ===================================================================== *)
(* FILE          : hhReconstruct.sml                                     *)
(* DESCRIPTION   : Reconstruct a proof from the lemmas given by an ATP   *)
(*                 and minimize them.                                    *)
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

val (TC_OFF : tactic -> tactic) = trace ("show_typecheck_errors", 0)
fun timeout_tactic t tac g =
  SOME (fst (timeout t (TC_OFF tac) g))
  handle Interrupt => raise Interrupt | _ => NONE

fun hh_reconstruct lemmas g =
  if not (!reconstruct_flag)
  then (print_endline (mk_metis_call lemmas);
        raise ERR "hh_minimize" "reconstruction off")
  else
    let
      val stac = mk_metis_call lemmas
      val t1 = !minimization_timeout
      val t2 = !reconstruction_timeout
      val newstac = psMinimize.minimize_stac t1 stac g []
      val tac = tactic_of_sml 1.0 newstac
    in
      case timeout_tactic t2 tac g of
        SOME _ => (newstac,tac)
      | NONE   => raise ERR "hh_reconstruct" "reconstruction failed"
    end

end
