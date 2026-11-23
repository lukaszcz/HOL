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

  fun collect_root (operations : 'term operations) memoize
      has_bags is_bag insert root =
    let
      fun is_unary_num_application term =
        (#is_combination operations) term andalso
        let val (head, _) = (#dest_comb operations) term
        in not ((#is_combination operations) head) andalso
           (#is_num_head operations) head
        end
      fun expects_number (SOME ty) =
            Type.compare (ty, #number_type operations) = EQUAL
        | expects_number NONE = false
      fun visit expected term acc =
        memoize expected term acc (fn () =>
        if (#is_abstraction operations) term then
          let
            val (_,body) = (#dest_abs operations) term
            val (_,range) = Type.dom_rng ((#type_of operations) term)
            val expected_body =
              if is_bag term then NONE else SOME range
          in visit expected_body body acc end
        else if (#is_combination operations) term then
          let
            val (rator,rand) = (#dest_comb operations) term
            val domain =
              Lib.fst (Type.dom_rng ((#type_of operations) rator))
            val expected_arg =
              if (#is_integer_coercion operations) rator andalso
                 not (is_unary_num_application rand)
              then NONE else SOME domain
            val acc = visit NONE rator acc
            val acc = visit expected_arg rand acc
          in
            if expects_number expected andalso
               ((#is_num_head operations) rator orelse
                (#is_bag_card_head operations) rator orelse
                (has_bags andalso
                 not ((#is_combination operations) rator) andalso
                 is_bag rator)) then
              insert term acc
            else acc
          end
        else acc)
    in visit NONE root [] end

  fun collect_with_merge_member (operations : 'term operations) memoize
      merge_member bag_terms roots =
    let
      fun member term terms =
        List.exists (fn saved => (#same operations) (term,saved)) terms
      fun insert term terms =
        if member term terms then terms else term :: terms
      val collect = collect_root operations memoize (not (null bag_terms))
        (fn term => member term bag_terms) insert
    in
      List.foldl (fn (root,terms) =>
        List.foldl (fn (number,acc) =>
          if merge_member number acc then acc else number :: acc) terms
          (collect root)) [] roots
    end

  fun collect_with_memo (operations : 'term operations) memoize =
    collect_with_merge_member operations memoize
      (fn term => List.exists (fn saved => (#same operations) (term,saved)))

  fun direct _ _ _ compute = compute ()

  fun collect operations bag_terms roots =
    collect_with_memo operations direct bag_terms roots

  fun collect_by operations compare bag_terms roots =
    let
      val empty = Redblackset.empty compare
      val bags = Redblackset.addList (empty,bag_terms)
      val seen = ref empty
      fun insert term terms =
        if Redblackset.member (!seen,term) then terms
        else (seen := Redblackset.add (!seen,term); term :: terms)
      val collect = collect_root operations direct (not (null bag_terms))
        (fn term => Redblackset.member (bags,term)) insert
    in
      (* Each root's new markers precede the earlier roots' markers in
         order of first occurrence within that root. *)
      List.foldl (fn (root,terms) => List.revAppend (collect root,terms))
        [] roots
    end
end
