open HolKernel boolLib simpLib testutils
val _ = new_theory "reviewstaging"
val atom = mk_var ("staging_atom",bool)
val calls = ref 0
fun printer gs be sys (pp : term_pp_types.ppstream_funs) gravs depth tm =
  if aconv atom tm then (calls := !calls + 1; #add_string pp "staging_atom")
  else raise term_pp_types.UserPP_Failed
val _ = Parse.temp_add_user_printer ("review-stage",atom,printer)
val cfg = {strip=false,elimvars=false,droptrues=false,oldestfirst=true}
val requested = ReqD (ASSUME atom)
val meter = Count.mk_meter ()
val tac = global_simp_tac cfg empty_ss [requested]
val _ = print ("STAGE construction printers=" ^ Int.toString (!calls) ^
               " primitives=" ^ Int.toString (#prims (Count.read meter)) ^ "\n")
val goal : Abbrev.goal = ([],mk_var("staging_unmatched",bool))
fun execute () = (ignore (runtac tac goal); "returned")
                 handle HOL_ERR _ => "HOL_ERR" | _ => "other"
val result1 = execute ()
val _ = print ("STAGE first printers=" ^ Int.toString (!calls) ^ " " ^ result1 ^ "\n")
val result2 = execute ()
val _ = print ("STAGE second printers=" ^ Int.toString (!calls) ^ " " ^ result2 ^ "\n")
exception PrinterFailure
val throw = ref false
val andterm = concl boolTheory.AND_CLAUSES
fun throwing_printer gs be sys (pp : term_pp_types.ppstream_funs) gravs depth tm =
  if aconv andterm tm then
    if !throw then raise PrinterFailure else #add_string pp "AND_CLAUSES"
  else raise term_pp_types.UserPP_Failed
val _ = Parse.temp_add_user_printer ("review-throw",andterm,throwing_printer)
val tac2 = global_simp_tac cfg boolSimps.bool_ss [ReqD boolTheory.AND_CLAUSES]
val _ = throw := true
val outcome =
  (let val (gs,_) = runtac (VALID tac2) ([],mk_conj(atom,T))
   in "goals=" ^ Int.toString(length gs) end)
  handle PrinterFailure => "PrinterFailure" | HOL_ERR _ => "HOL_ERR" | _ => "other"
val _ = print ("OUTCOME " ^ outcome ^ "\n")
val _ = OS.Process.exit OS.Process.success
