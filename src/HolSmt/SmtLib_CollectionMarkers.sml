(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_CollectionMarkers :> SmtLib_CollectionMarkers =
struct
  datatype role = Membership | UnaryObservation | Insert | Delete
                | BinaryConstruction | UnaryConstruction | Inclusion
                | Empty | Equality | Other

  type 'term operations =
    {strip_comb : 'term -> 'term * 'term list,
     dest_abs : 'term -> 'term * 'term,
     dest_comb : 'term -> 'term * 'term,
     condition : 'term -> ('term * 'term * 'term) option,
     bindings : 'term -> ('term * 'term) list,
     add : 'term -> 'term list -> 'term list,
     member : 'term -> 'term list -> bool,
     is_collection_type : 'term -> bool,
     classify : 'term * 'term -> role}

  type 'term memo_hooks =
    {walk : 'term -> 'term list -> (unit -> 'term list) -> 'term list,
     mark : 'term -> 'term list -> (unit -> 'term list) -> 'term list}

  fun collect_with_memo_and_syntax_errors (operations : 'term operations)
      is_syntax_error
      ({walk=memo_walk,mark=memo_mark} : 'term memo_hooks)
      {propagate_bindings, visit_prefix} =
    let
      fun mark term terms =
        memo_mark term terms (fn () =>
          case (#condition operations) term of
            SOME (_, then_term, else_term) =>
              mark else_term (mark then_term ((#add operations) term terms))
          | NONE => (#add operations) term terms)
      (* Marks what the application [term] = [rator rands] introduces. *)
      fun mark_application term rator rands terms =
        case (#classify operations) (term, rator) of
          Membership =>
            (case rands of [_, collection] => mark collection terms
             | _ => terms)
        | UnaryObservation =>
            (case rands of [collection] => mark collection terms
             | _ => terms)
        | Insert =>
            (case rands of [_, collection] =>
               mark term (mark collection terms)
             | _ => terms)
        | Delete =>
            (case rands of [collection, _] =>
               mark term (mark collection terms)
             | _ => terms)
        | BinaryConstruction =>
            (case rands of [left, right] =>
               mark term (mark left (mark right terms))
             | _ => terms)
        | UnaryConstruction =>
            (case rands of [collection] =>
               mark term (mark collection terms)
             | _ => terms)
        | Inclusion =>
            (case rands of [left, right] => mark left (mark right terms)
             | _ => terms)
        | Empty => (#add operations) term terms
        | Equality =>
            (case rands of [left, right] =>
               if (#is_collection_type operations) left andalso
                  (#is_collection_type operations) right then
                 mark left (mark right terms)
               else terms
             | _ => terms)
        | Other => terms
      (* The application prefixes of [term], longest first, ending with its
         head. *)
      fun prefixes term =
        case (SOME ((#dest_comb operations) term)
              handle primary => if is_syntax_error primary then NONE
                else raise primary) of
          SOME (function, _) => function :: prefixes function
        | NONE => []
      fun walk term terms =
        memo_walk term terms (fn () => let
          val (rator, rands) = (#strip_comb operations) term
          val terms =
            (let val (_, body) = (#dest_abs operations) term
             in walk body terms end
             handle primary => if is_syntax_error primary then
               List.foldl (fn (arg, acc) => walk arg acc) terms rands
             else raise primary)
          val terms =
            if propagate_bindings then
              (let val bindings = (#bindings operations) term
               in List.foldl (fn ((variable, value), acc) =>
                 if (#member operations) variable acc then mark value acc
                 else acc) terms bindings end
               handle primary => if is_syntax_error primary then terms
                 else raise primary)
            else terms
          (* Walking each prefix would walk its arguments again, so that
             applications nested in their first argument took arity^depth
             walks.  Walk the head once and mark each partial application
             from its own arguments, which were walked above. *)
          val terms =
            if visit_prefix then
              (case List.rev (prefixes term) of
                 [] => terms
               | head :: partials =>
                   #2 (List.foldl (fn (partial, (count, acc)) =>
                     (count + 1, mark_application partial rator
                        (List.take (rands, count)) acc))
                     (1, walk head terms) partials))
            else terms
        in
          mark_application term rator rands terms
        end)
    in walk end

  fun legacy_syntax_error (Feedback.HOL_ERR _) = true
    | legacy_syntax_error _ = false

  fun collect_with_memo operations hooks policy =
    collect_with_memo_and_syntax_errors operations legacy_syntax_error
      hooks policy

  fun collect operations policy =
    collect_with_memo operations
      {walk=fn _ => fn _ => fn compute => compute (),
       mark=fn _ => fn _ => fn compute => compute ()} policy
end
