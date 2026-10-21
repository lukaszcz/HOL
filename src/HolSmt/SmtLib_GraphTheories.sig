(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtLib_GraphTheories =
sig
  datatype support = Recipe | Scoped of string | Shape of string
                   | Unregistered
  type limits =
    {template_limit : int, index_limit : int, operand_limit : int,
     token_limit : int}
  type entry =
    {theory : string, name : string, overload : int, support : support,
     metadata : SmtLib_Theories.symbol_metadata list}
  type 'a dictionaries =
    Type.hol_type SmtLib_Parser.dict * 'a SmtLib_Parser.construction_dict

  (* Select exactly the ordinary registry's solver/logic packet and callback
     order. Admitted recipes receive schematic holes and types, never actual
     graph representatives. Deferred callbacks produce explicit refusals. *)
  val select : 'a SmtLib_GraphBackend.backend -> limits ->
    {logic : string, solver : string option} ->
    {dictionaries : 'a dictionaries, entries : entry list,
     metadata : SmtLib_Theories.symbol_metadata list}
  (* Install an explicitly scoped/ID-aware implementation for deferred
     callbacks. The override sees its exact callback description. *)
  val select_with : 'a SmtLib_GraphBackend.backend -> limits ->
    (entry -> 'a SmtLib_Parser.construction_parse_fn option) ->
    {logic : string, solver : string option} ->
    {dictionaries : 'a dictionaries, entries : entry list,
     metadata : SmtLib_Theories.symbol_metadata list}
  (* Explicit audited dialect adapters use the same bounded schematic
     admission as registry recipes; actual operands never enter builders. *)
  val recipe_parsefn : 'a SmtLib_GraphBackend.backend -> limits ->
    (string -> Term.term list -> Term.term list -> Term.term) ->
    'a SmtLib_Parser.construction_parse_fn
  (* Declared source objects retain their declaration identity and origin
     bridges; they are not reconstructed as arbitrary schematic variables. *)
  val bind_sources : 'a SmtLib_GraphBackend.backend ->
    'a SmtLib_GraphBackend.frame ->
    (string * Term.term) list -> 'a SmtLib_Parser.construction_dict ->
    'a SmtLib_Parser.construction_dict
  (* Legacy retry coercion from cached operand types and a tiny recipe. *)
  val coerce_arguments : 'a SmtLib_GraphBackend.backend ->
    'a SmtLib_GraphBackend.frame -> 'a list -> 'a list * bool
  type policy_limits = SmtReplayResourcePolicy.recipe_policy
  val recipe_parsefn_with_policy : 'a SmtLib_GraphBackend.backend ->
    policy_limits ->
    (string -> Term.term list -> Term.term list -> Term.term) ->
    'a SmtLib_Parser.construction_parse_fn
  val select_with_policy : 'a SmtLib_GraphBackend.backend -> policy_limits ->
    (entry -> 'a SmtLib_Parser.construction_parse_fn option) ->
    {logic:string,solver:string option} ->
    {dictionaries:'a dictionaries,entries:entry list,
     metadata:SmtLib_Theories.symbol_metadata list}
  val select_with_policy_no_override : 'a SmtLib_GraphBackend.backend ->
    policy_limits -> {logic:string,solver:string option} ->
    {dictionaries:'a dictionaries,entries:entry list,
     metadata:SmtLib_Theories.symbol_metadata list}

end
