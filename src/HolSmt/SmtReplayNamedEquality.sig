(* The actual policy equality programme, over authenticated named ports. *)
signature SmtReplayNamedEquality =
sig
  type ('node,'edge) operations =
    {guard:unit -> unit,tick:unit -> unit,key:'node -> int,
     compare_keys:int * int -> order,
     same:'node * 'node -> bool,name:'node -> Term.term,
     equality:'node -> ('node * 'node) option,
     application:'node -> ('node * 'node) option,
     theorem:'edge -> Thm.thm,constructor:'node -> 'edge,
     definition:'node -> 'edge,reflexive:'node -> 'edge,
     symmetry:'edge list -> 'edge,transitivity:'edge list -> 'edge,
     congruence:'edge list -> 'edge,equality_mp:'edge list -> 'edge,
     conjunction:'edge list -> 'edge,conjunct_left:'edge list -> 'edge,
     error:string -> exn}
  (* Each decoded proof must conclude the exact equality between
     the two actual named endpoints. No synthetic PV wrapper is used. *)
  val assemble_with_equations : (('node * 'node) * 'edge) list ->
    ('node,'edge) operations ->
    {rule:string,target:'node,premises:('node * 'edge) list} -> 'edge
  val assemble : ('node,'edge) operations ->
    {rule:string,target:'node,premises:('node * 'edge) list} -> 'edge
end
