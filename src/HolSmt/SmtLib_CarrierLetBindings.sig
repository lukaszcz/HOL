(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtLib_CarrierLetBindings =
sig
  type 'term pabs_operations =
    {dest_abs : 'term -> 'term * 'term,
     dest_uncurry : 'term -> 'term,
     mk_pair : 'term * 'term -> 'term,
     is_syntax_error : exn -> bool}

  (* Ordinary abstraction first, otherwise the genuine UNCURRY operand
     followed by two recursive paired abstractions, exactly as dest_pabs.
     dest_uncurry must check its head using the existing declaration table.
     mk_pair constructs the carrier's typed pattern DATA; it grants no
     graph/source authority and need not manufacture a public graph node.
     Only the supplied syntax-mismatch class triggers fallback or ends a
     strip. Unexpected graph, admission and Work errors propagate intact. *)
  val dest_pabs : 'term pabs_operations -> 'term -> 'term * 'term
  val strip_pabs : 'term pabs_operations -> 'term -> 'term list * 'term

  type 'term operations =
    {dest_abs : 'term -> 'term * 'term,
     dest_let : 'term -> 'term * 'term,
     dest_plet : 'term -> 'term * 'term * 'term,
     strip_pabs : 'term -> 'term list * 'term,
     list_mk_comb : 'term * 'term list -> 'term,
     is_let : 'term -> bool,
     is_syntax_error : exn -> bool,
     not_a_let : unit -> exn}

  (* The stock simple/paired/parallel-let fallback and function-binding
     fixup, with the carrier's own syntax and construction callbacks.
     Only exceptions accepted by is_syntax_error trigger fallback or final
     error normalization. A graph adapter must recognize its private syntax
     mismatch exception, never arbitrary guard, budget or native failures.
     The Term adapter can retain the stock HOL_ERR policy and callbacks.
     Unequal parallel binding/value counts produce not_a_let directly.
     This helper creates no source, theorem or graph authority. *)
  val dest_anylet : 'term operations -> 'term ->
    ('term * 'term) list * 'term
end
