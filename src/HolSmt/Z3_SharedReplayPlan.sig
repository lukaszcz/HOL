(* The SAME registry-driven syntax plan, with no Source/proof permission. *)
signature Z3_SharedReplayPlan =
sig
  datatype resolution_mode=RecordedResolution|LegacyRawResolution
  datatype ('node,'syntax) plan=Original of 'node
    | OriginalSlot of int * 'node
    | Alias of Z3_GraphProofParser.proof_id
    | Equality of string * 'node * Z3_GraphProofParser.proof_id list
    | Boolean of 'node * Z3_GraphProofParser.proof_id list
    | Resolution of 'node * Z3_GraphProofParser.proof_id list *
        'syntax SmtLib_GraphFrontend.constructed_term
    | RawResolution of 'node * Z3_GraphProofParser.proof_id list *
        'syntax SmtLib_GraphFrontend.constructed_term
    | ScopedEquality of 'node * Z3_GraphProofParser.proof_id
    | Quantified of
        {source:'node,instance:'node,target:'node,arguments:'node list}
  type observer =
    {registry:Z3_Proof.registry_observer,
     rule_comparison:Z3_Proof.proof_rule * Z3_Proof.proof_rule -> unit,
     normalization_character:unit -> unit,
     premises:Z3_GraphProofParser.proof_id list -> unit,
     argument_copy:unit -> unit,kept_item:unit -> unit,
     copied_roots:unit -> unit}
  type ('node,'syntax) operations =
    {observer:observer,prior:Z3_GraphProofParser.proof_id -> 'node,
     located:'syntax SmtLib_GraphFrontend.constructed_term -> 'node,
     processed:'node -> bool,original_slot:'node -> int,
     operands:Term.term -> int -> 'node -> 'node list option,
     keep:'node -> unit,error:string -> string -> exn}
  val silent_observer : observer
  (* Same actual registry/normalization programme for a scoped producer;
     no second rule table or alternative version policy. *)
  val canonical_name : observer -> (string -> string -> exn) -> string ->
    Z3_Proof.proof_rule -> string
  val classify_with_bindings : ('node,'syntax) operations ->
    {version:string,mode:resolution_mode} ->
    'syntax Z3_GraphProofParser.constructed_step ->
    'node * ('node,'syntax) plan
  val classify : ('node,'syntax) operations ->
    {version:string,mode:resolution_mode} ->
    'syntax Z3_GraphProofParser.constructed_step ->
    'node * ('node,'syntax) plan
end
