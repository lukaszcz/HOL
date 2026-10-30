(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayGroundDefinitions =
sig
  type plan
  (* Pure prospective lowering of the exact needed non-oriented portfolio.
     Explicit allocated endpoints retain the variable-definition route.
     Unknown operators stay ordinary Sources; no absence proof is inferred.
     Both original metrics and every planned evaluation operand/result are
     bounded before the first theorem-producing or caller type operation. *)
  val prepare : SmtReplayGraph.graph ->
    {scope : SmtReplayGraph.scope, allocated : SmtReplayGraph.node list,
     sources : SmtReplayGraph.node list, needed : SmtReplayGraph.node list,
     limit : int} -> plan
  (* Exact definition-only portfolio: preserve needed occurrence order and
     duplicates, intersect with retained original definition nodes, then
     exclude allocated-endpoint oriented definitions. A real parser/category
     producer is still required; callers cannot infer it from asserted terms. *)
  val prepare_recorded : SmtReplayGraph.graph ->
    {scope : SmtReplayGraph.scope, allocated : SmtReplayGraph.node list,
     sources : SmtReplayGraph.node list, needed : SmtReplayGraph.node list,
     definitions : SmtReplayGraph.node list, limit : int} -> plan
  (* Optional CHAR slice. Original cached raw/binder metrics precede
     character/numeral metadata callbacks; only in-range CHR, ORD and exact
     char equality/order are predicted. Public EVAL remains proof authority.
     The legacy prepare/prepare_recorded routes retain their old lowering. *)
  val prepare_recorded_characters : SmtReplayGraph.graph ->
    {scope : SmtReplayGraph.scope, allocated : SmtReplayGraph.node list,
     sources : SmtReplayGraph.node list, needed : SmtReplayGraph.node list,
     definitions : SmtReplayGraph.node list, limit : int} -> plan
  (* Opt-in complete original-EVAL portfolio, with the same definition-only
     needed occurrence/category and allocated-endpoint exclusions. Both raw
     and binder-inclusive original operands and the fixed expected result T
     are bounded before execution/type callbacks. Unknown graph sizes use
     genuine public bounded native admission, including opaque binders; no
     FV/groundness fact is inferred. execute uses fixed bossLib.EVAL once per
     distinct admitted Source (including nonoriented open identities), while
     preserving the ordered duplicate occurrences and their shared witness.
     False, unevaluated and ordinary EVAL HOL_ERR outcomes stay ordinary;
     resource/caller errors propagate. No new policy or implicit cap. *)
  val prepare_complete_recorded : SmtReplayGraph.graph ->
    {scope : SmtReplayGraph.scope, allocated : SmtReplayGraph.node list,
     sources : SmtReplayGraph.node list, needed : SmtReplayGraph.node list,
     definitions : SmtReplayGraph.node list, limit : int} -> plan
  (* For the old preparations, fixed public EVAL is called only on admitted
     local operator spines,
     after child results are joined by checked MK_COMB. False/unevaluated
     ordinary HOL_ERR outcomes stay ordinary; resource errors propagate.
     Every returned proof is CLOSED/clean with exact original Source pointer.
     The old lowering remains unfinished, not full legacy EVAL.
     prepare_complete_recorded instead admits and evaluates whole originals,
     without nodewise prediction, SUBST_CONV or a semantic search. *)
  val execute : plan ->
    {check_type : Type.hol_type -> unit} ->
    (SmtReplayGraph.node * Thm.thm) list
end
