(* Expected-type analysis for HOL num terms at the outbound query boundary. *)
signature SmtLib_RawNumAnalysis =
sig
  (* Semantic head recognition remains in the caller's existing tables.
     Syntax callbacks must preserve their carrier's binding environment;
     graph callers use admitted typed views, not reconstructed raw terms. *)
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

  (* The second argument is the query's marked bag terms; the third is its
     ordered roots. Preserve per-root traversal/duplicate suppression and
     the subsequent outer merge order. NONE and SOME expected types have
     different meanings, including beneath coercions and bag abstractions.
     This direct traversal deliberately introduces no memo or new bound. *)
  val collect : 'term operations -> 'term list -> 'term list -> 'term list

  (* Each visit supplies its exact expected type (including NONE), current
     term, immutable incoming per-root list and synchronous computation.
     A graph caller keys successful full output lists on expected type,
     authentic scoped node, incoming list identity/version and fixed query
     bag-marker context. Never skip a node merely because it was visited,
     reuse output for another incoming state, cache an exception/in-progress
     result, or retain the computation. Caches belong to this analysis call.
     Per-root empty lists and the outer merge are unchanged. The ordinary
     collect entry uses direct hooks and retains its legacy traversal. *)
  val collect_with_memo : 'term operations -> 'term memo ->
    'term list -> 'term list -> 'term list
end
