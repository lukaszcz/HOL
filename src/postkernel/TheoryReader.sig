signature TheoryReader =
sig

  exception TheoryReader of string
  type raw_theory = RawTheory_dtype.raw_theory
  type sharing_tables = RawTheory_dtype.sharing_tables
  type 'a raw_exports = 'a RawTheory_dtype.raw_exports
  type 'a raw_core = {tables : sharing_tables, exports : 'a raw_exports}
  val load_thydata : {thyname:string,path:string,hash:string} ->
                     (Thm.thm * DB_dtype.thminfo) Symtab.table
  val core_decode : string raw_core HOLsexp.decoder

  val load_raw_thydata : {path:string} -> raw_theory

  (* Hook for alternative theorem sources (e.g., proof trace replay).
     When set to something other than the default, load_thydata dispatches
     to this function instead of loading theorems from .dat files. *)
  val load_thydata_fn :
      ({thyname:string,path:string,hash:string} ->
       (Thm.thm * DB_dtype.thminfo) Symtab.table) ref

  (* Intrinsic immutable default-decoder constructor origin only. The
     equality query cannot mint or register a theorem/forest certificate.
     Current declarations, epochs, Scope and Work remain a later reader's
     separate responsibility. No proof or term getter is exposed here. *)
  type bool_left_decode_origin
  val bool_left_decode_origin : unit -> bool_left_decode_origin option
  val bool_left_decode_origin_matches : bool_left_decode_origin ->
    {proof: Thm.thm, statement: Term.term} -> bool
  val bool_left_decode_origin_counts : bool_left_decode_origin ->
    {hypotheses: int}


end

(* [load_thydata thyname fname] loads the filename and makes the appropriate
   changes to the theory hierarchy in response to the data stored there.  In
   other words, this is done mostly for the side-effects. The map returned
   allows <nm>Theory.sml files to then bind SML identifiers corresponding to
   theorem names to theorem values.
*)
