(* Lambda translation for the new HolyHammer problem generator. *)
signature hhLamTrans =
sig

  type term = Term.term

  (* Accepted modes are lifting, combs, combs_and_lifting, and keep_lams.
     The empty string denotes the legacy exporter and is deliberately
     rejected here.  The problem generator, rather than this module,
     downgrades keep_lams to lifting for formats without full HO syntax. *)
  val valid_mode : string -> bool
  val translate :
    string -> term list -> term list * (string * term) list
  (* mode -> formulas -> (rewritten formulas, named lambda definitions) *)

end
