(* SAME raw-resolution dictionary and selective fallback discovery. *)
signature SmtReplayRawClause =
sig
  type ('node,'tree,'key) operations =
    {tick:unit -> unit,header:unit -> unit,error:string -> exn,
     boolean:'node -> unit,constructor:'node -> unit,
     constant:Term.term -> 'node -> bool,
     operands:Term.term -> int -> 'node -> 'node list option,
     node_key:'node -> 'key,compare_node:'node * 'node -> order,
     compare_key:'key * 'key -> order,
     compare_ordinal:IntInf.int * IntInf.int -> order,
     root:'tree -> 'node,
     view:'tree -> ('node,'tree) SmtReplayNamedClause.tree_view,
     literal:{node:'node,atom:'node,negative:bool} -> 'tree,
     disjunction:{node:'node,left:'tree,right:'tree} -> 'tree,
     copy:unit -> unit,write:unit -> unit}
  (* Returns discovery-order reversed fallbacks. The caller retains real
     typed occurrences and ownership guards, and reverses after validation.
     Dictionary membership is syntax DATA, never a proof/Source permission.
     Units are literal atoms; only the real head is selectively expanded. *)
  val discover : ('node,'tree,'key) operations ->
    {head:unit -> 'tree,units:'unit list,unit_tree:'unit -> 'tree,
     target:unit -> 'tree} -> 'tree list
end
