structure SmtLib_RawNumAnalysis :> SmtLib_RawNumAnalysis =
struct
  type 'term operations =
    {same : 'term * 'term -> bool,
     type_of : 'term -> Type.hol_type,
     is_abstraction : 'term -> bool,
     dest_abs : 'term -> 'term * 'term,
     is_combination : 'term -> bool,
     dest_comb : 'term -> 'term * 'term,
     strip_comb : 'term -> 'term * 'term list,
     is_integer_coercion : 'term -> bool,
     is_num_head : 'term -> bool,
     is_bag_card_head : 'term -> bool,
     number_type : Type.hol_type}

  type 'term memo = Type.hol_type option -> 'term -> 'term list ->
    (unit -> 'term list) -> 'term list

  fun collect_with_memo (operations : 'term operations) memoize
      bag_terms roots =
    let
      fun member term terms =
        List.exists (fn saved => (#same operations) (term,saved)) terms
      fun insert term terms =
        if member term terms then terms else term :: terms
      fun for_term term =
        let
          fun visit expected term acc =
            memoize expected term acc (fn () =>
            if (#is_abstraction operations) term then
              let
                val (_,body) = (#dest_abs operations) term
                val (_,range) = Type.dom_rng ((#type_of operations) term)
                val expected_body =
                  if member term bag_terms then NONE else SOME range
              in visit expected_body body acc end
            else if (#is_combination operations) term then
              let
                val (rator,rand) = (#dest_comb operations) term
                val domain =
                  Lib.fst (Type.dom_rng ((#type_of operations) rator))
                val expected_arg =
                  if (#is_integer_coercion operations) rator andalso
                     not (case (#strip_comb operations) rand of
                       (head, [_]) => (#is_num_head operations) head
                     | _ => false) then NONE else SOME domain
                val acc = visit NONE rator acc
                val acc = visit expected_arg rand acc
              in
                if ((#is_num_head operations) rator orelse
                    (#is_bag_card_head operations) rator orelse
                    (case (#strip_comb operations) term of
                       (bag,[_]) => member bag bag_terms
                     | _ => false)) andalso
                   Option.isSome expected andalso
                   Type.compare (Option.valOf expected,
                     #number_type operations) = EQUAL then
                  insert term acc
                else acc
              end
            else acc)
        in visit NONE term [] end
    in
      List.foldl (fn (term,acc) =>
        List.foldl (fn (number,terms) => insert number terms)
          acc (for_term term)) [] roots
    end

  fun collect operations bag_terms roots =
    collect_with_memo operations
      (fn _ => fn _ => fn _ => fn compute => compute ()) bag_terms roots
end
