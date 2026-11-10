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

  fun make (context:Q.outbound_context) {syntax_error,metadata_error} =
    let
      val _ = ignore ((#key context) (#goal context))
      val reduce = theorem_reduces_exact_application context
      fun is_comb current = case (#view context) current of
          Q.ApplicationView _ => true | _ => false
      fun dest_comb current = case (#view context) current of
          Q.ApplicationView pair => pair
        | _ => raise syntax_error "dest_comb" "application expected"
      fun constant_leaf current = case (#view context) current of
          Q.ConstantView atom => SOME atom | _ => NONE
      fun same_const current expected = case constant_leaf current of
          SOME atom => Term.same_const atom expected | NONE => false
      val operations : Q.carrier SmtLib.outbound_carrier_residual_operations =
        {is_comb=is_comb,dest_comb=dest_comb,type_of= #type_of context,
         strip_comb= #strip_comb context,same_const=same_const,
         constant_leaf=constant_leaf,free_vars= #free_variables context,
         theorem_reduces_exact_application=reduce,
         metadata_error=metadata_error}
    in SmtLib.outbound_carrier_residual operations end
end
