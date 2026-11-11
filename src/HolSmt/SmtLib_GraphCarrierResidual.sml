(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphCarrierResidual :> SmtLib_GraphCarrierResidual =
struct
  structure Q = SmtLib_GraphQueryAnalysis
  structure S = SmtLib_GraphCarrierScratch
  structure M = SmtLib_CarrierHoPartMatch
  structure R = SmtLib_CarrierPureRewrite

  fun theorem_reduces_exact_application (context:Q.outbound_context) =
    let
      val scratch = S.create context
      val operations : S.term R.operations =
        {syntax= #operations scratch,of_template= #of_template scratch,
         variable_name= #variable_name scratch,
         variant= #variant scratch,
         part_match=M.part_match scratch}
    in fn theorem => fn current =>
      let val input = (#of_query scratch) current
      in R.reduces operations theorem input end
    end

end
