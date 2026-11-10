(* The existing checked CNF programme; no alternative Boolean engine. *)
signature SmtReplayNamedBoolean =
sig
  datatype 'node view = Atom | Constant | Application of 'node * 'node
  type ('node,'edge) operations =
    {native:SmtReplayNativeContract.limits,
     spend:int -> unit,pay:IntInf.int -> unit,guard:unit -> unit,
     profile:Term.term -> SmtReplayNamedContext.profile,
     type_weight:Type.hol_type -> IntInf.int,
     type_of:'node -> Type.hol_type,view:'node -> 'node view,
     constant:'node -> Term.term,same:'node * 'node -> bool,
     name:'node -> Term.term,theorem:'edge -> Thm.thm,
     constructor:'node -> 'edge,closed:Thm.thm -> 'edge,
     equality_mp:'edge list -> 'edge,conjunction:'edge list -> 'edge,
     implication_mp:'edge list -> 'edge,error:string -> exn}
  val assemble : ('node,'edge) operations ->
    {root:'node,premises:('node * 'edge) list} -> 'edge
  (* Only the upper owned consumer supplies these privately proved
     atom equations. No syntax identity is treated as a theorem. *)
  val assemble_with_equations : 'edge list ->
    ('node,'edge) operations ->
    {root:'node,premises:('node * 'edge) list} -> 'edge
  (* Proper clauses produced by the one authentic named fixed-law
     worker; the same Boolean core converts equations and applies its
     checked conjunction equivalence before using either kind of fact. *)
  val assemble_with_equations_and_clauses : 'edge list -> 'edge list ->
    ('node,'edge) operations ->
    {root:'node,premises:('node * 'edge) list} -> 'edge
end
