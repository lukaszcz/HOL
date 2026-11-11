(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtLib_CollectionMarkers =
sig
  (* Classification is supplied by the existing theory registry. These
     roles describe argument positions, not operator names or proof rules. *)
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

  (* Set and Bag preserve different traversal policies. Set markers flow
     from let-local variables back to binding values. Bag markers also
     classify every application prefix with its own arguments and walk the
     head, as well as the flattened arguments. Without binding propagation
     this gives the markers, in order, of walking every prefix in full.
     Body/binding/prefix discovery retains the legacy HOL_ERR fallbacks.
     Each hook receives the current term, exact immutable incoming marker
     list and a synchronous computation. A graph caller keys separate walk
     and mark caches on the authentic scoped node, incoming list identity
     or version, and every relevant view context. Cache only a completed
     successful output list; never retain a thunk/exception or treat a
     node-only visited hit as no change. Incoming markers affect let-value
     propagation. Caches belong to one analysis call with fixed operations
     and policy; the helper retains neither caches nor caller context. *)
  val collect_with_memo : 'term operations -> 'term memo_hooks ->
    {propagate_bindings : bool, visit_prefix : bool} ->
    'term -> 'term list -> 'term list

  (* Graph callers distinguish ordinary destructor shape mismatches from
     ownership, admission and other failures. Only exceptions selected by
     this predicate enter the three legacy body/binding/prefix fallbacks;
     all other exceptions propagate unchanged. *)
  val collect_with_memo_and_syntax_errors : 'term operations ->
    (exn -> bool) -> 'term memo_hooks ->
    {propagate_bindings : bool, visit_prefix : bool} ->
    'term -> 'term list -> 'term list

  (* The legacy entry uses direct synchronous hooks, preserving its exact
     traversal, result ordering and HOL_ERR fallback behavior. The ordinary
     collect_with_memo entry also retains that same HOL_ERR policy. *)
  val collect : 'term operations ->
    {propagate_bindings : bool, visit_prefix : bool} ->
    'term -> 'term list -> 'term list
end
