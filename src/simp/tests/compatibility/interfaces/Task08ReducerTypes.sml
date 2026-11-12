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
  type reducer
  val lift : Traverse.reducer -> reducer
  val CONTEXT_REDUCER : reducer_context_data -> reducer
  val CONFIG_REDUCER : reducer_config_data -> reducer
  val reducer_config_data : reducer -> reducer_config_data
  val reducer_data : reducer -> reducer_context_data
  val addctxt : thm list -> reducer -> reducer
end
