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

  fun expects_number (operations : 'term operations) (SOME ty) =
        Type.compare (ty, #number_type operations) = EQUAL
    | expects_number _ NONE = false

  fun collect_root (operations : 'term operations) memoize branch_cache
      has_bags is_bag insert root =
    let
      fun compound term = (#is_combination operations) term orelse
        (#is_abstraction operations) term
      fun is_unary_num_application term =
        (#is_combination operations) term andalso
        let val (head, _) = (#dest_comb operations) term
        in not ((#is_combination operations) head) andalso
           (#is_num_head operations) head
        end
      fun visit expected term acc =
        memoize expected term acc (fn () =>
        if (#is_abstraction operations) term then
          let
            fun descend () =
              let
                val (_,body) = (#dest_abs operations) term
                val (_,range) = Type.dom_rng ((#type_of operations) term)
                val expected_body =
                  if is_bag term then NONE else SOME range
              in visit expected_body body acc end
          in case branch_cache of
              NONE => descend ()
            | SOME cache => cache expected term acc descend
          end
        else if (#is_combination operations) term then
          let
            val (rator,rand) = (#dest_comb operations) term
            fun descend () =
              let
                val domain =
                  Lib.fst (Type.dom_rng ((#type_of operations) rator))
                val expected_arg =
                  if (#is_integer_coercion operations) rator andalso
                     not (is_unary_num_application rand)
                  then NONE else SOME domain
                val acc = visit NONE rator acc
                val acc = visit expected_arg rand acc
              in
                if expects_number operations expected andalso
                   ((#is_num_head operations) rator orelse
                    (#is_bag_card_head operations) rator orelse
                    (has_bags andalso
                     not ((#is_combination operations) rator) andalso
                     is_bag rator)) then
                  insert term acc
                else acc
              end
          in
            case branch_cache of
              SOME cache =>
                (* Cache forks with compound operands. A unary spine cannot
                   repeatedly visit both sides of a shared subterm. *)
                if (#is_combination operations) rator andalso compound rand
                   andalso compound (#2 ((#dest_comb operations) rator)) then
                  cache expected term acc descend
                else descend ()
            | NONE => descend ()
          end
        else acc)
    in visit NONE root [] end

  fun collect_with_membership (operations : 'term operations) memoize
      {bag_member, number_member, merge_member} bag_terms roots =
    let
      fun insert term terms =
        if number_member term terms then terms else term :: terms
      val collect = collect_root operations memoize NONE (not (null bag_terms))
        (bag_member bag_terms) insert
    in
      List.foldl (fn (root,terms) =>
        List.foldl (fn (number,acc) =>
          if merge_member number acc then acc else number :: acc) terms
          (collect root)) [] roots
    end

  fun collect_with_merge_member (operations : 'term operations) memoize
      merge_member =
    let fun member term = List.exists
          (fn saved => (#same operations) (term,saved))
    in collect_with_membership operations memoize
      {bag_member=Lib.C member,number_member=member,merge_member=merge_member}
    end

  fun collect_with_memo (operations : 'term operations) memoize =
    collect_with_merge_member operations memoize
      (fn term => List.exists (fn saved => (#same operations) (term,saved)))

  fun direct _ _ _ compute = compute ()

  fun collect operations bag_terms roots =
    collect_with_memo operations direct bag_terms roots

  fun collect_by_using operations compare branch_cache bag_terms roots =
    let
      val empty = Redblackset.empty compare
      val bags = Redblackset.addList (empty,bag_terms)
      val seen = ref empty
      fun insert term terms =
        if Redblackset.member (!seen,term) then terms
        else (seen := Redblackset.add (!seen,term); term :: terms)
      val collect = collect_root operations direct branch_cache
        (not (null bag_terms))
        (fn term => Redblackset.member (bags,term)) insert
    in
      (* Each root's new markers precede the earlier roots' markers in
         order of first occurrence within that root. *)
      List.foldl (fn (root,terms) => List.revAppend (collect root,terms))
        [] roots
    end

  fun collect_by operations compare = collect_by_using operations compare NONE

  fun collect_terms (operations : Term.term operations) bag_terms roots =
    let
      val branches = Array.array (127, [])
      fun cached expected term incoming compute =
        let
          val index = SmtReplayImport.pointer_bucket 1
            (Array.length branches) term
          val numeric = expects_number operations expected
          fun matches (saved, context) = context = numeric andalso
            Portable.pointer_eq (saved, term)
        in
          if List.exists matches (Array.sub (branches, index)) then incoming
          else
            let
              val result = compute ()
              val entries = case Array.sub (branches, index) of
                  first :: second :: third :: _ => [first,second,third]
                | rest => rest
              (* A completed visit only adds markers to the query-wide set.
                 Keep collisions bounded even on identical-looking branches. *)
              val _ = Array.update (branches,index,(term,numeric)::entries)
            in result end
        end
    in collect_by_using operations Term.compare (SOME cached) bag_terms roots
    end
end
