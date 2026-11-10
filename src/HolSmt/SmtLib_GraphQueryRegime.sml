(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphQueryRegime :> SmtLib_GraphQueryRegime =
struct
  structure Q = SmtLib_GraphQueryAnalysis
  structure T = SmtLib_GraphTranslation
  structure D = SmtLib_GraphCarrierDatatype
  type result = {regime:SmtLib.regime,reason:string,visits:int}
  fun compare_key ((ls,ln),(rs,rn)) =
    case Int.compare (ls,rs) of
      EQUAL => Int.compare (ln,rn) | result => result
  fun compare_memo ((lk,le),(rk,re)) =
    case compare_key (lk,rk) of
      EQUAL => List.collate compare_key (le,re) | result => result
  fun select (context:Q.outbound_context)
      {operations,request} : result =
    let
      val operations : Q.carrier
          SmtLib.outbound_term_translation_operations = operations
      val builtin = T.outbound_builtin_operations context
      val errors = {syntax_error= #syntax_error builtin,
        is_mismatch= #is_syntax_error builtin}
      val datatype_hooks = D.make context errors
      val answers = ref (Redblackmap.mkDict compare_memo)
      val visits = ref 0
      fun guard current = ignore ((#key context) current)
      val _ = guard (#goal context)
      fun memoize inherited current compute =
        let val index = ((#key context) current,
              List.map (#key context) inherited)
            fun valid () = (guard current;List.app guard inherited)
        in case Redblackmap.peek (!answers,index) of
            SOME result => (valid ();result)
          | NONE =>
              let val _ = (#step context) () val _ = visits := !visits+1
                  val result = compute () val _ = valid ()
                  val _ = answers := Redblackmap.insert (!answers,index,result)
              in result end
        end
      fun is_abstraction current = case (#view context) current of
          Q.AbstractionView _ => true | _ => false
      fun constant_name current = case (#view context) current of
          Q.ConstantView atom =>
            let val {Thy,Name,...} = Term.dest_thy_const atom in (Thy,Name) end
        | _ => raise (#syntax_error builtin) "regime_constant_name"
            "constant leaf expected"
      fun datatype_case current = Option.map
        (fn {scrutinee,clauses} =>
          {scrutinee=scrutinee,clauses=List.map (fn (variables,body) =>
            (fn () => (List.app guard variables;variables),body)) clauses})
        ((#case_view datatype_hooks) current)
      val algebra : Q.carrier SmtLib.outbound_regime_operations =
        {syntax=operations,is_abstraction=is_abstraction,
         constant_name=constant_name,datatype_case=datatype_case,
         is_syntax_error= #is_syntax_error builtin,
         is_optional_error= #is_syntax_error builtin,memoize=memoize}
      val (regime,reason) = SmtLib.outbound_select_regime algebra request
        (#assumptions context,#goal context)
      val _ = guard (#goal context)
    in {regime=regime,reason=reason,visits= !visits} end
end
