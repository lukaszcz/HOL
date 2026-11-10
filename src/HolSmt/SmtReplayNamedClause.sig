(* Exact shared compact programme; caller retains ownership/admission. *)
signature SmtReplayNamedClause =
sig
  type profile =
    {raw:IntInf.int,inc:IntInf.int,ann:IntInf.int,ty:IntInf.int}
  datatype ('node,'tree) tree_view = ClauseFalse of 'node
    | ClauseLiteral of {node:'node,atom:'node,negative:bool}
    | ClauseOr of {node:'node,left:'tree,right:'tree}
  datatype 'node node_view = NodeAtom | NodeConstant
    | NodeApplication of 'node * 'node
  type ('node,'tree,'edge,'dependency) operations =
    {guard:unit -> unit,tick:unit -> unit,
     pay:IntInf.int -> unit,future:IntInf.int -> unit,
     profile:Term.term -> profile,type_weight:Type.hol_type -> IntInf.int,
     template:IntInf.int,metadata_template:SmtReplayResourcePolicy.limit,
     ceiling:IntInf.int,hypothesis:Term.term -> bool,error:string -> exn,
     tree_view:'tree -> ('node,'tree) tree_view,
     node_view:'node -> 'node node_view,same_node:'node * 'node -> bool,
     named:'node -> Term.term,constant:Term.term -> 'node -> bool,
     constant_term:'node -> Term.term,
     operator:Term.term -> int -> 'node -> 'node list,
     theorem:'edge -> Thm.thm,definition:'node -> 'edge,
     dependency:'edge -> 'dependency}
  type ('node,'edge,'dependency) congruence_operations =
    {guard:unit -> unit,tick:unit -> unit,
     pay:IntInf.int -> unit,future:IntInf.int -> unit,
     profile:Term.term -> profile,type_weight:Type.hol_type -> IntInf.int,
     template:IntInf.int,metadata_template:SmtReplayResourcePolicy.limit,
     ceiling:IntInf.int,hypothesis:Term.term -> bool,error:string -> exn,
     node_view:'node -> 'node node_view,same_node:'node * 'node -> bool,
     named:'node -> Term.term,constant_term:'node -> Term.term,
     theorem:'edge -> Thm.thm,definition:'node -> 'edge,
     dependency:'edge -> 'dependency}
  type 'dependency plan
  val prepare : ('node,'tree,'edge,'dependency) operations ->
    {premises:{tree:'tree,edge:'edge} list,target:'tree,
     target_expanded:'tree option,fallbacks:'tree list} -> 'dependency plan
  (* Syntax aliases alone authorize nothing: this preparation proves each
     demanded equality from the actual constructor definitions. *)
  val prepare_with_atom_aliases : ('node * 'node) list ->
    ('node,'tree,'edge,'dependency) operations ->
    {premises:{tree:'tree,edge:'edge} list,target:'tree,
     target_expanded:'tree option,fallbacks:'tree list} -> 'dependency plan
  val execute :
    {guard:unit -> unit,check_type:Type.hol_type -> unit,error:string -> exn}
    -> 'dependency plan -> {theorem:Thm.thm,dependencies:'dependency list}
  (* Constructor equations establish an actual native equality between
     these authentic names. No syntax identity is accepted as a proof. *)
  type 'dependency congruence_plan
  val prepare_atom_congruence :
    ('node,'edge,'dependency) congruence_operations -> 'node * 'node ->
    'dependency congruence_plan
  val execute_atom_congruence :
    {guard:unit -> unit,check_type:Type.hol_type -> unit,error:string -> exn}
    -> 'dependency congruence_plan ->
    {theorem:Thm.thm,dependencies:'dependency list}
  val atom_congruence_dependencies : 'dependency congruence_plan ->
    'dependency list
  (* Same actual constructor proof programme, for one authentic
     node cursor. Neither a fake clause tree nor a native theorem enters. *)
  type 'dependency constructor_plan
  val prepare_constructor :
    ('node,'edge,'dependency) congruence_operations -> 'node ->
    'dependency constructor_plan
  val execute_constructor :
    {guard:unit -> unit,check_type:Type.hol_type -> unit,error:string -> exn}
    -> 'dependency constructor_plan ->
    {theorem:Thm.thm,dependencies:'dependency list}
  val constructor_dependencies : 'dependency constructor_plan ->
    'dependency list
  (* Retained prospective DATA, not a theorem or edge. Caller must guard
     its actual owner before observing this immutable prepared model. *)
  val constructor_model : 'dependency constructor_plan ->
    {conclusion:Term.term,hypotheses:Term.term list}
  type 'node literal = {atom:'node,negative:bool}
  type ('node,'tree,'occurrence) discovery_operations =
    {node:'node -> unit,is_constant:Term.term -> 'node -> bool,
     operands:Term.term -> int -> 'node -> 'node list option,
     need_constructor:'node -> unit,same_node:'node * 'node -> bool,
     occurrence_node:'occurrence -> 'node,root:'tree -> 'node,
     clause_false:'node -> 'tree,
     clause_literal:{node:'node,atom:'node,negative:bool} -> 'tree,
     clause_or:{node:'node,left:'tree,right:'tree} -> 'tree,
     memo_semantic:'node -> (unit -> 'tree) -> 'tree,error:string -> exn}
  val discover : ('node,'tree,'occurrence) discovery_operations ->
    {literal_node:'node -> 'tree * 'node literal,
     recorded:'occurrence list -> 'node -> 'tree * 'node literal list,
     semantic:'node -> 'tree}
end
