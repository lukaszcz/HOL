(* Native compact placeholders; no syntax-to-Source/proof permission. *)
signature SmtReplayValueNames =
sig
  type value=SmtLib_GraphParserValue.value
  type syntax=SmtLib_GraphParserValue.proof_term
  type ('a,'b) mapper=('a -> 'b) -> 'a list -> 'b list
  (* Existing guarded callbacks and visitor functions are direct arguments.
     No dynamic callback/context record is made. The returned closure is
     the same one native name lookup used by the actual named block. *)
  val allocate : (unit -> unit) -> (unit -> unit) ->
    (IntInf.int -> unit) -> SmtLib_GraphParserValue.context ->
    (syntax -> int) -> SmtReplayNativeContract.limits ->
    (Type.hol_type -> unit) -> (string -> string -> exn) ->
    (value list -> value list -> value list) ->
    (syntax list -> syntax list -> syntax list) ->
    (value,syntax) mapper -> (Thm.thm,Term.term) mapper ->
    value list -> value list -> syntax list -> syntax list ->
    syntax -> Term.term
end
