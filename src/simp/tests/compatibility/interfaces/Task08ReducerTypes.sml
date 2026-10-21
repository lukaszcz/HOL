(* Design prototype, not an installed TraverseExt implementation. *)
signature Task08ReducerTypes =
sig
  include Abbrev
  type context = exn
  type reducer_config_data =
    {name : string option, initial : context,
     addcontext : context * thm list -> context,
     apply : {solver : term list -> term -> thm,
              conv : term list -> term -> thm, context : context,
              stack : term list, cond_depth : int option,
              term_ord : term * term -> order,
              relation : term * (term -> thm)} -> conv}
  type reducer_context_data =
    {name : string option, initial : context,
     addcontext : context * thm list -> context,
     apply : {solver : term list -> term -> thm,
              conv : term list -> term -> thm, context : context,
              stack : term list, cond_depth : int,
              term_ord : term * term -> order,
              relation : term * (term -> thm)} -> conv}
  datatype reducer = LIFTED of Traverse.reducer
                   | CONTEXT_REDUCER of reducer_context_data
                   | CONFIG_REDUCER of reducer_config_data
  val lift : Traverse.reducer -> reducer
  val reducer_config_data : reducer -> reducer_config_data
  val reducer_data : reducer -> reducer_context_data
  val addctxt : thm list -> reducer -> reducer
end
