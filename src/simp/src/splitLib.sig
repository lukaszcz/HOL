signature splitLib =
sig
  include Abbrev

  (* Analyse the supplied rules when the conversion is constructed. *)
  val SPLIT_CONV : thm list -> conv

  (* Perform one conclusion split.  Assumption splitting is added by the
     next layer of the splitter. *)
  val SPLIT_TAC : thm list -> tactic
end
