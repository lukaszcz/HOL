signature SmtLib_GraphStringTransfer =
sig
  type alias =
    {image : SmtReplayGraph.node, operand : SmtReplayGraph.node,
     free_variables : SmtReplayGraph.node list}
  type producer =
    {propose : SmtReplayGraph.node -> SmtReplayCanonGraph.graph_schema option,
     aliases : unit -> alias list,
     install_aliases : SmtLib_GraphFrontend.session ->
       (string * SmtReplayGraph.node) list -> unit,
     character_bound : SmtReplayGraph.node ->
       {fact : SmtLib_GraphPreprocessFacts.fact,target : SmtReplayGraph.node},
     substring_after_end :
       {string : SmtReplayGraph.node,start : SmtReplayGraph.node,
        length : SmtReplayGraph.node} ->
       {rule : SmtLib_GraphPreprocessDerived.rule,
        premise : SmtReplayGraph.node,target : SmtReplayGraph.node}}
  (* The five actual ordinary HOL string transfer laws; guarded substrings
     are separate dependency rules, never unconditional conversions. *)
  val create : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {template_limit : int,prefix_depth : int,
     check_type : Type.hol_type -> unit} -> producer
end
