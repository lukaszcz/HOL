structure SmtLib_CollectionApplicationAnalysis :>
  SmtLib_CollectionApplicationAnalysis =
struct
  type 'term operations =
    {same : 'term * 'term -> bool,
     type_of : 'term -> Type.hol_type,
     is_variable : 'term -> bool,
     is_constant : 'term -> bool,
     declared_const_arity : 'term -> int,
     strip_comb : 'term -> 'term * 'term list,
     dest_comb : 'term -> 'term * 'term,
     is_abstraction : 'term -> bool,
     dest_abs : 'term -> 'term * 'term,
     free_variables : 'term -> 'term list}

  fun member (operations : 'term operations) term terms =
    List.exists (fn saved => (#same operations) (term,saved)) terms

  fun ordinary_symbol_application (operations : 'term operations) function =
    let val (head,applied) = (#strip_comb operations) function
    in (#is_variable operations) head orelse
      ((#is_constant operations) head andalso
       List.length applied < (#declared_const_arity operations) head)
    end

  fun collection_parameter_index (operations : 'term operations)
      function argument variable =
    let
      val residual_type = (#type_of operations) function
      val argument_type = (#type_of operations) argument
      fun find index ty =
        if Type.compare (ty,residual_type) = EQUAL then
          case Lib.total Type.dom_rng ty of
            SOME (domain,_) =>
              if Type.compare (domain,argument_type) = EQUAL then SOME index
              else NONE
          | NONE => NONE
        else
          case Lib.total Type.dom_rng ty of
            SOME (_,range) => find (index + 1) range
          | NONE => NONE
    in find 0 ((#type_of operations) variable) end

  fun computed_pairs (operations : 'term operations) collection_terms term =
    case Lib.total (#dest_comb operations) term of
      SOME (function,argument) =>
        if member operations argument collection_terms andalso
           not (ordinary_symbol_application operations function) then
          List.mapPartial (fn variable =>
            Option.map (fn index => (variable,index,argument))
              (collection_parameter_index operations function argument
                variable)) ((#free_variables operations) function)
        else []
    | NONE => []

  fun computed_applications operations collection_terms subterms =
    if List.null collection_terms then []
    else List.concat
      (List.map (computed_pairs operations collection_terms) subterms)

  fun has_mixed_argument (operations : 'term operations)
      collection_terms subterms =
    let
      fun positions function [] _ = []
        | positions function (argument :: arguments) index =
            (function,index,argument) ::
            positions function arguments (index + 1)
      fun application_positions subterm =
        let val (function,arguments) = (#strip_comb operations) subterm
        in if (#is_variable operations) function orelse
            (#is_constant operations) function then
            positions function arguments 0
          else []
        end
      val applications =
        List.concat (List.map application_positions subterms)
    in
      List.exists (fn (function,index,argument) =>
        member operations argument collection_terms andalso
        List.exists (fn (other_function,other_index,other_argument) =>
          (#same operations) (function,other_function) andalso
          index = other_index andalso
          not (member operations other_argument collection_terms))
          applications) applications
    end

  fun has_bound_application_with_memo (operations : 'term operations)
      memoize collection_terms roots =
    let
      fun visit bound term =
        memoize bound term (fn () =>
          if (#is_abstraction operations) term then
            let val (variable,body) = (#dest_abs operations) term
            in visit (variable :: bound) body end
          else
            let
              val (function,arguments) = (#strip_comb operations) term
              val applies_bound =
                List.exists (fn variable =>
                  (#same operations) (function,variable)) bound
              val has_collection_argument =
                List.exists (fn argument =>
                  member operations argument collection_terms) arguments
              fun computed_applies_bound () =
                List.exists (fn (variable,_,_) =>
                  member operations variable bound)
                  (computed_pairs operations collection_terms term)
            in
              (applies_bound andalso has_collection_argument) orelse
              computed_applies_bound () orelse
              List.exists (visit bound) arguments
            end)
    in List.exists (visit []) roots end

  fun has_bound_application operations collection_terms roots =
    has_bound_application_with_memo operations
      (fn _ => fn _ => fn compute => compute ()) collection_terms roots
end
