(* Shared constructor/tester/selector syntax; no Source or proof authority. *)
signature SmtLib_GraphDatatypeParser =
sig
  val sort_dictionary_from_types :
    (Type.hol_type,string) Redblackmap.dict ->
    Type.hol_type SmtLib_Parser.dict
  (* The caller owns the active backend action and lifetime. guard executes
     before all callback fast paths and after successful construction; only
     fixed small templates are compiled. Actual operands stay carrier DATA.
     error preserves the caller's existing diagnostic origin. *)
  val install_with_policy :
    {limits:SmtReplayResourcePolicy.recipe_policy,
     error:string -> string -> exn} ->
    (Type.hol_type,string) Redblackmap.dict ->
    (unit -> SmtLib.parser_datatype_declaration list) ->
    (unit -> unit) -> 'a SmtLib_GraphFrontend.constructed_session ->
    ('a list -> unit) -> unit
end
