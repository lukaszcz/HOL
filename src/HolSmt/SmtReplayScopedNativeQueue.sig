(* Finite programme DATA; only its execution returns kernel theorems. *)
signature SmtReplayScopedNativeQueue =
sig
  type queue
  type proof
  val create : SmtReplayNamedContext.admission -> queue
  (* Seed slots denote the actual sparse constructor ASSUMEs. They are
     not Current/Original Sources. The owner retains the real freeze plan
     and supplies its exact theorem slots only during execution. *)
  val seed : queue -> int -> Term.term -> proof
  val fixed : queue -> Term.term SmtReplayNamedContext.primitive ->
    proof list -> proof
  val boolean : queue -> Term.term SmtReplayNamedContext.boolean_rule ->
    proof list -> proof
  (* The SAME named Boolean worker, statically instantiated on private
     forecast tokens. Its SAT/CNF instructions are not caller thunks and
     can only be emitted by that actual shared worker after its forecasts.
     The enclosing owner supplies syntax observations/constructor proofs;
     this lower record confers no scoped-result or Source authority. *)
  type 'node boolean_operations =
    {native:SmtReplayNativeContract.limits,
     type_weight:Type.hol_type -> IntInf.int,
     type_of:'node -> Type.hol_type,view:'node -> 'node
       SmtReplayNamedContext.view,constant:'node -> Term.term,
     same:'node * 'node -> bool,name:'node -> Term.term,
     constructor:'node -> proof,error:string -> exn}
  val assemble_boolean : queue -> 'node boolean_operations ->
    {root:'node,premises:('node * proof) list} -> proof
  type 'node equality_operations =
    {key:'node -> int,same:'node * 'node -> bool,
     name:'node -> Term.term,equality:'node -> ('node * 'node) option,
     application:'node -> ('node * 'node) option,
     constructor:'node -> proof,definition:'node -> proof,
     error:string -> exn}
  val assemble_equality : queue -> 'node equality_operations ->
    {rule:string,target:'node,premises:('node * proof) list} -> proof
  type ('node,'tree) recorded_operations =
    {metadata_template:SmtReplayResourcePolicy.limit,
     tree_view:'tree -> ('node,'tree) SmtReplayNamedClause.tree_view,
     node_view:'node -> ('node * 'node) option,
     constant_node:'node -> bool,same_node:'node * 'node -> bool,
     named:'node -> Term.term,constant:Term.term -> 'node -> bool,
     constant_term:'node -> Term.term,
     operator:Term.term -> int -> 'node -> 'node list,
     definition:'node -> proof,error:string -> exn}
  val recorded : queue -> ('node,'tree) recorded_operations ->
    {premises:{tree:'tree,edge:proof} list,target:'tree,
     target_expanded:'tree option,fallbacks:'tree list} -> proof
  val conclusion : proof -> Term.term
  val hypotheses : proof -> Term.term list
  val compact_profile : queue -> Term.term ->
    SmtReplayNamedContext.profile
  (* A clean-token forecast for the static Boolean metadata instance;
     not the tag of a checked theorem. Every actual native result is
     independently checked through the SAME genuine N tag predicate. *)
  val forecast_tag : proof -> Tag.tag
  (* Sealing closes metadata construction; it is not native admission or
     a scoped result. The enclosing genuine owner must settle its entire
     command/closing queue before calling check_types. No callback runs
     while a later logical Needs can still be discovered. *)
  val seal : queue -> unit
  (* Immutable actual Type observations only; the owner includes this
     forest in its complete prospective callback portfolio. *)
  val type_ports : queue -> Type.hol_type list
  val check_types : queue -> (Type.hol_type -> unit) -> unit
  (* SAME caller action. Every native future portfolio was charged once
     by the actual N preparation; execution cannot adopt caller credit.
     Instructions execute in emission order, not recursive proof order.
     A seed result must be the exact cached constructor ASSUME theorem. *)
  val execute : queue -> (int -> Thm.thm) -> unit
  val theorem : queue -> proof -> Thm.thm
  val close : queue -> unit
end
