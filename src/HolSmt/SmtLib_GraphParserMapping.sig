(* Immutable lexical DATA for a future graph-native parser adapter. *)
signature SmtLib_GraphParserMapping =
sig
  type mapping
  type graph_reference
  type node_id = int
  type slot = int
  datatype arity = Exact of int | AtMost of int
  datatype form =
      ExistingGraph of graph_reference
    | Constant of Term.term
    | FreeVariable of
        {identity:int,kind:SmtReplayGraph.variable_kind,lexical:Term.term}
    | BoundSlot of slot
    | Application of node_id * node_id
    | Abstraction of {slot:slot,lexical:Term.term,body:node_id}
  type entry = {id:node_id,hol_type:Type.hol_type,form:form}
  type dependency =
    {slot:slot,kind:SmtReplayGraph.variable_kind,lexical:Term.term,
     hol_type:Type.hol_type}
  datatype origin = Ordinary of node_id
    | Fallback of {dependencies:dependency list,expression:node_id}
  type declaration =
    {token:string,rank:int,arity:arity,value:node_id,origin:origin,
     hol_type:Type.hol_type,sorts:(string list * string) option}

  (* Call while the carrier borrow is live, using committed store symbols
     and the actual emission's type dictionary. No borrowed carrier,
     callback, semantic key or temporary construction node is retained.
     Entries are dependency-first; declaration/dependency order is exact.
     Atomic graph aliases require root visibility and complete free IDs.
     All composite syntax is frozen as a typed DAG, never rejected merely for
     having an opaque original or a synthetic abstraction.

     Local slots preserve exact variable identity under ordered binders;
     they are not lexical-name matches. Graph references remain subject to
     their original graph/scope/epoch guards. No Source, equality, assertion
     or theorem permission is produced. Interpretation of general recipe
     closures by the proof parser is separate work: this module never calls
     G.abstraction, constructs whole HOL terms or installs parser aliases. *)
  val freeze : SmtLib_GraphQueryAnalysis.outbound_context ->
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     regime:SmtLib.regime,types:(Type.hol_type,string) Redblackmap.dict,
     symbols:SmtLib_GraphCarrierStore.symbol list} -> mapping
  (* Additional committed syntax observations share the SAME typed DAG.
     Input order and duplicates are retained in the returned IDs. They are
     metadata roots, not assertions or new lexical declarations. External
     Bound variables retain their actual identity; no lexical name alias
     or Source permission is inferred from an observation. Existing symbol
     declarations are frozen first, preserving freeze's node/slot order. *)
  val freeze_with_inputs : SmtLib_GraphQueryAnalysis.outbound_context ->
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     regime:SmtLib.regime,types:(Type.hol_type,string) Redblackmap.dict,
     symbols:SmtLib_GraphCarrierStore.symbol list,
     inputs:SmtLib_GraphQueryAnalysis.carrier list} ->
    {mapping:mapping,inputs:node_id list}
  val validate : mapping -> unit
  (* Compare the caller's expected graph/scope before activating any held
     mapping references, then perform the unchanged full validation. *)
  val validate_for : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    mapping -> unit
  val entries : mapping -> entry list
  val entry : mapping -> node_id -> entry
  val declarations : mapping -> declaration list
  val types : mapping -> (Type.hol_type,string) Redblackmap.dict
  val reference_node : mapping -> graph_reference -> SmtReplayGraph.node
end
