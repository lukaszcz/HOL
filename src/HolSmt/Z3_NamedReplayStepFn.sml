(* Static callbacks; no Source, Scope or theorem authority is supplied. *)
signature Z3_NamedReplayStepInput =
sig
  type expected
  type context
  type command
  type node
  type syntax
  type edge
  val original : expected -> context -> command -> node -> edge
  val original_slot : expected -> context -> command -> int * node -> edge
  val alias : expected -> context -> command ->
    Z3_GraphProofParser.proof_id -> edge
  val equality : expected -> context -> command ->
    string * node * Z3_GraphProofParser.proof_id list -> edge
  val boolean : expected -> context -> command ->
    node * Z3_GraphProofParser.proof_id list -> edge
  val scoped_equality : expected -> context -> command ->
    node * Z3_GraphProofParser.proof_id -> edge
  val quantified : expected -> context -> command ->
    {source:node,instance:node,target:node,arguments:node list} -> edge
  val raw_resolution : expected -> context -> command ->
    node * Z3_GraphProofParser.proof_id list *
      syntax SmtLib_GraphFrontend.constructed_term -> edge
  val resolution : expected -> context -> command ->
    node * Z3_GraphProofParser.proof_id list *
      syntax SmtLib_GraphFrontend.constructed_term -> edge
  val unfinished : expected -> context -> command -> unit -> edge
end

functor Z3_NamedReplayStepFn(Input:Z3_NamedReplayStepInput) =
struct
  structure Plan=Z3_SharedReplayPlan
  fun execute expected context command plan=
    case plan of Plan.Original value=>
        Input.original expected context command value
      | Plan.OriginalSlot value=>
          Input.original_slot expected context command value
      | Plan.Alias value=>Input.alias expected context command value
      | Plan.Equality value=>Input.equality expected context command value
      | Plan.Boolean value=>Input.boolean expected context command value
      | Plan.ScopedEquality value=>
          Input.scoped_equality expected context command value
      | Plan.Quantified value=>Input.quantified expected context command value
      | Plan.RawResolution value=>
          Input.raw_resolution expected context command value
      | Plan.Resolution value=>Input.resolution expected context command value
      | _=>Input.unfinished expected context command ()
end
