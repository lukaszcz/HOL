(* Executed through the isolated Holmake launcher, against either source pin.
   Staging observations are expected-red evidence, not compatibility passes. *)
open HolKernel boolLib simpLib testutils
val _ = new_theory "pairedstaging"
val atom = mk_var ("staging_atom", bool)
val calls = ref 0
fun printer gs be sys (pp : term_pp_types.ppstream_funs) gravs depth tm =
  if aconv atom tm then
    (calls := !calls + 1; #add_string pp "staging_atom")
  else raise term_pp_types.UserPP_Failed
val _ = Parse.temp_add_user_printer ("paired-stage", atom, printer)
val cfg = {strip=false, elimvars=false, droptrues=false, oldestfirst=true}
val tac = global_simp_tac cfg empty_ss [ReqD (ASSUME atom)]
val _ = Paired.observe "construction.printers" (Int.toString (!calls))
val goal : Abbrev.goal = ([], mk_var ("staging_unmatched", bool))
fun execute () =
  let
    val outcome = (ignore (runtac (VALID tac) goal); "returned")
      handle HOL_ERR err => Feedback.top_function_of err
  in
    Paired.check "requirement failure" (outcome = "REQUIRE_DECREASE_TAC")
  end
val _ = execute ()
val _ = Paired.observe "first.printers" (Int.toString (!calls))
val _ = execute ()
val _ = Paired.observe "second.printers" (Int.toString (!calls))
exception PrinterFailure
val throw = ref false
val andterm = concl boolTheory.AND_CLAUSES
fun throwing_printer gs be sys (pp : term_pp_types.ppstream_funs) gravs depth tm =
  if aconv andterm tm then
    if !throw then raise PrinterFailure else #add_string pp "AND_CLAUSES"
  else raise term_pp_types.UserPP_Failed
val _ = Parse.temp_add_user_printer
  ("paired-throw", andterm, throwing_printer)
val tac2 = global_simp_tac cfg boolSimps.bool_ss [ReqD boolTheory.AND_CLAUSES]
val _ = throw := true
val outcome =
  (let val (gs, _) = runtac (VALID tac2) ([], mk_conj (atom, T))
   in "goals=" ^ Int.toString (length gs) end)
  handle PrinterFailure => "PrinterFailure"
val _ = Paired.observe "saved.outcome" outcome
val th = SIMP_CONV boolSimps.bool_ss [] (mk_conj (atom, T))
val _ = Paired.check "ordinary simplification"
  (aconv (concl th) (mk_eq (mk_conj (atom, T), atom)) andalso null (hyp th))
