(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtLib_GraphWordBuilders =
sig
  (* ID-aware implementation of the Fixed_Size_BitVectors @bbterm callback.
     Bits are least-significant first. Selector recovery observes only a
     bounded application spine against small expected numeral indices; word
     operands are compared by backend identity and inspected only for type.
     Backend observation/resource refusals are not parser retry signals. *)
  val bbterm : 'a SmtLib_GraphBackend.backend ->
    SmtReplayResourcePolicy.recipe_policy ->
    'a SmtLib_Parser.construction_parse_fn
end
