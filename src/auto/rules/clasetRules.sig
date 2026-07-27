signature clasetRules =
sig
  type term = Term.term
  type thm = Thm.thm
  type thname = KernelSig.kernelname

  datatype rulekind = Intro | Elim | Dest
  type rulespec = {kind : rulekind, safe : bool, prio : int option}
  type tag = {weight : int, index : int}
  type brl = bool * thm
  type rl = thm * thm option
  type info = {rl : rl, dup_rl : rl}
  type decl =
    {name : string, spec : rulespec, tag : tag, info : info, orig : thm}

  type canonical =
    {thm : thm, patvars : term HOLset.set, prems : term list, concl : term}

  val canonical_rule : thm -> thm
  val canonical_rule_of : rulekind -> thm -> thm
  val canonical_form : thm -> canonical
  val canonical_form_of : rulekind -> thm -> canonical
  val canonical_form_of_measured :
    (unit -> unit) -> rulekind -> thm -> canonical
  val rule_index : rulekind -> thm -> term
  val rule_index_of : rulekind -> canonical -> term
  val rule_premises : thm -> term list
  val rule_premises_of : rulekind -> thm -> term list
  val rule_conclusion : thm -> term
  val is_elim : rulekind -> bool

  val MAKE_ELIM_RULE : thm -> thm
  val CLASSICAL_RULE : thm -> thm
  val SWAP_INTRO_RULE : thm -> thm option
  val DUP_INTRO_RULE : thm -> thm
  val DUP_ELIM_RULE : thm -> thm
  val REV_DUP_ELIM_RULE : thm -> thm
  val ext_info : rulespec -> thm -> info

  datatype safe_class = Safe0 | SafeP
  val subgoals_of : brl -> int
  val safe_class_of : rulespec -> info -> safe_class option

  type decls
  val empty_decls : decls
  val make_decl : {name : string, spec : rulespec, weight : int,
                   info : info, orig : thm} -> decl
  val extend_decl : decl -> decls -> decl option * decls
  val extend_derived_decl : decl -> decls -> decl option * decls
  val remove_decl : string -> decls -> decl list * decls
  val has_decls : decls -> thm -> bool
  val decl_name_member : decls -> string -> bool
  val get_decls : decls -> thm -> decl list
  val dest_decls : decls -> decl list
  val merge_decls : decls * decls -> decl list * decls
  val candidate_order : (tag * brl) list -> (tag * brl) list
  val candidate_order_measured :
    (unit -> unit) -> (tag * brl) list -> (tag * brl) list

  datatype cdelta = ADD of {name : thname, spec : rulespec} | RM of string
  val encode_delta : cdelta -> ThyDataSexp.t
  val decode_delta : ThyDataSexp.t -> cdelta option
  val load_delta : cdelta -> (thname * rulespec * thm) option
  val uptodate_delta : cdelta -> bool
end
