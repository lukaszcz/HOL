(* Executable boundary only: no traversal/engine placeholders. *)
structure Task08Reducers :> Task08ReducerTypes =
struct
  open Abbrev
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
  val lift = LIFTED
  fun reducer_config_data (CONFIG_REDUCER r) = r
    | reducer_config_data (LIFTED r) =
      let val {name,initial,addcontext,apply} = Traverse.dest_reducer r
      in
        {name=name, initial=initial, addcontext=addcontext,
         apply=fn {solver,conv,context,stack,relation,...} =>
           apply {solver=solver,conv=conv,context=context,stack=stack,
                  relation=relation}}
      end
    | reducer_config_data
        (CONTEXT_REDUCER {name,initial,addcontext,apply}) =
      {name=name, initial=initial, addcontext=addcontext,
       apply=fn {solver,conv,context,stack,relation,cond_depth,term_ord} =>
         apply {solver=solver,conv=conv,context=context,stack=stack,
                relation=relation,term_ord=term_ord,
                cond_depth=case cond_depth of NONE => !Cond_rewr.stack_limit
                                           | SOME n => n}}
  fun reducer_data r =
    let val {name,initial,addcontext,apply} = reducer_config_data r
    in
      {name=name, initial=initial, addcontext=addcontext,
       apply=fn {solver,conv,context,stack,relation,cond_depth,term_ord} =>
         apply {solver=solver,conv=conv,context=context,stack=stack,
                relation=relation,term_ord=term_ord,
                cond_depth=SOME cond_depth}}
    end
  fun addctxt ths (LIFTED r) = LIFTED (Traverse.addctxt ths r)
    | addctxt ths (CONTEXT_REDUCER {name,initial,addcontext,apply}) =
      CONTEXT_REDUCER {name=name,initial=addcontext (initial,ths),
                       addcontext=addcontext,apply=apply}
    | addctxt ths (CONFIG_REDUCER {name,initial,addcontext,apply}) =
      CONFIG_REDUCER {name=name,initial=addcontext (initial,ths),
                      addcontext=addcontext,apply=apply}
end
