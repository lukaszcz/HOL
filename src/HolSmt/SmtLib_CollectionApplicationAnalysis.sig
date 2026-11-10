(* Collection-argument analysis shared by term and graph query carriers. *)
signature SmtLib_CollectionApplicationAnalysis =
sig
  (* The caller preserves its existing equality, syntax and free-variable
     meaning. Graph clients supply typed constructor views and scoped FV
     metadata; they must not classify an unopened binder as a nonbinder.
     No operation returns a raw representative on behalf of this module. *)
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

  (* Results retain supplied inventory order, per-term FV order and duplicate
     triples. Parameter indices use exact HOL type equality, not type shape. *)
  val computed_pairs : 'term operations -> 'term list -> 'term ->
    ('term * int * 'term) list
  val computed_applications : 'term operations -> 'term list -> 'term list ->
    ('term * int * 'term) list
  val has_mixed_argument : 'term operations -> 'term list -> 'term list -> bool

  (* Walk ordered roots in their lexical binder context. This is deliberately
     not a context-free visited-node fold: one node can have distinct bound
     meanings in different frames. A graph caller's memo must account for
     the exact bound environment, not just cache the constructor views. *)
  val has_bound_application_with_memo : 'term operations ->
    ('term list -> 'term -> (unit -> bool) -> bool) ->
    'term list -> 'term list -> bool
  (* The memo hook receives the exact ordered bound stack and current node.
     It must evaluate a cache miss synchronously, cache only a returned bool,
     and never retain the computation or an exception. Cache keys must retain
     every graph/frame/environment distinction affecting the supplied views;
     caches belong to this one analysis call. A hit bypasses that node's
     complete scan. Recursive children and roots still short-circuit on true.
     The ordinary entry below deliberately uses no memoization. *)
  val has_bound_application : 'term operations -> 'term list -> 'term list ->
    bool
end
