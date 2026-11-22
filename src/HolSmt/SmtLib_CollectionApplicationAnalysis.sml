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

  fun computed_pairs_with (operations : 'term operations) is_marked term =
    case Lib.total (#dest_comb operations) term of
      SOME (function,argument) =>
        if is_marked argument andalso
           not (ordinary_symbol_application operations function) then
          List.mapPartial (fn variable =>
            Option.map (fn index => (variable,index,argument))
              (collection_parameter_index operations function argument
                variable)) ((#free_variables operations) function)
        else []
    | NONE => []

  fun computed_pairs operations collection_terms =
    computed_pairs_with operations
      (fn term => member operations term collection_terms)

  fun computed_applications_with operations is_marked subterms =
    List.concat (List.map (computed_pairs_with operations is_marked) subterms)

  fun computed_applications operations collection_terms subterms =
    if List.null collection_terms then []
    else computed_applications_with operations
      (fn term => member operations term collection_terms) subterms

  fun scan_mixed_argument (operations : 'term operations) observe subterms =
    let
      fun scan_arguments _ _ [] rest = scan_terms rest
        | scan_arguments record index (argument :: arguments) rest =
            record (index,argument) orelse
            scan_arguments record (index + 1) arguments rest
      and scan_terms [] = false
        | scan_terms (subterm :: rest) =
            case (#strip_comb operations) subterm of
              (_,[]) => scan_terms rest
            | (function,arguments) =>
                if (#is_variable operations) function orelse
                   (#is_constant operations) function then
                  scan_arguments (observe function) 0 arguments rest
                else scan_terms rest
    in
      scan_terms subterms
    end

  fun has_mixed_argument operations collection_terms subterms =
    if List.null collection_terms then false
    else
      let
        val positions = ref []
        fun observe function (index,argument) =
          let
            val marked = member operations argument collection_terms
            val saved = List.find (fn (other,other_index,_) =>
              index = other_index andalso (#same operations) (function,other))
              (!positions)
          in
            case saved of
              SOME (_,_,other_marked) => marked <> other_marked
            | NONE =>
                (positions := (function,index,marked) :: !positions; false)
          end
      in
        scan_mixed_argument operations observe subterms
      end

  fun has_mixed_argument_by operations compare key collection_terms subterms =
    if List.null collection_terms then false
    else
      let
        val marked = Redblackset.addList (Redblackset.empty compare,
          List.map key collection_terms)
        val positions = ref (Redblackmap.mkDict (Lib.pair_compare
          (compare,Int.compare)))
        fun observe function =
          let val function_key = key function in
            fn (index,argument) =>
              let
                val position = (function_key,index)
                val is_marked = Redblackset.member (marked,key argument)
              in
                case Redblackmap.peek (!positions,position) of
                  SOME saved => saved <> is_marked
                | NONE =>
                    (positions := Redblackmap.insert
                      (!positions,position,is_marked); false)
              end
          end
      in
        scan_mixed_argument operations observe subterms
      end

  fun scan_bound_application (operations : 'term operations)
      memoize is_marked roots =
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
              val has_collection_argument = List.exists is_marked arguments
              fun computed_applies_bound () =
                List.exists (fn (variable,_,_) =>
                  member operations variable bound)
                  (computed_pairs_with operations is_marked term)
            in
              (applies_bound andalso has_collection_argument) orelse
              computed_applies_bound () orelse
              List.exists (visit bound) arguments
            end)
    in List.exists (visit []) roots end

  fun has_bound_application_with_memo operations memoize collection_terms
      roots =
    not (List.null collection_terms) andalso
    scan_bound_application operations memoize
      (fn term => member operations term collection_terms) roots

  fun has_bound_application_with operations is_marked roots =
    scan_bound_application operations
      (fn _ => fn _ => fn compute => compute ()) is_marked roots

  fun has_bound_application operations collection_terms roots =
    not (List.null collection_terms) andalso
    has_bound_application_with operations
      (fn term => member operations term collection_terms) roots
end
