signature clasetLib =
sig
  include Abbrev

  type rulekind = clasetRules.rulekind
  type rulespec = clasetRules.rulespec
  type tag = clasetRules.tag
  type brl = clasetRules.brl

  type claset
  type claset_part

  datatype part = Safe0Part | SafePPart | UnsafePart | DupPart

  val empty_cs : claset

  val add_rule : rulespec -> string * thm -> claset -> claset

  (* Adds a rule a library derived from a user declaration.  Behaves as
     add_rule, but a duplicate or cross-kind clash among derived rules is
     dropped silently instead of warning on every invocation. *)
  val add_derived_rule : rulespec -> string * thm -> claset -> claset

  val add_sintros : (string * thm) list -> claset -> claset
  val add_intros : (string * thm) list -> claset -> claset
  val add_selims : (string * thm) list -> claset -> claset
  val add_elims : (string * thm) list -> claset -> claset
  val add_sdests : (string * thm) list -> claset -> claset
  val add_dests : (string * thm) list -> claset -> claset
  val remove_rule : string -> claset -> claset
  val merge_cs : claset * claset -> claset

  val the_claset : unit -> claset
  val export_rule : rulespec -> string -> unit
  val temp_add_rule : rulespec -> string * thm -> unit
  val delrule : string -> unit
  val temp_delrule : string -> unit
  val augment_claset : (claset -> claset) -> unit

  (* Reconstruct only the ancestry-persistent declarations recorded for the
     named theory.  Unlike [claset_of_theory], this excludes rules derived
     from the caller's current TypeBase. *)
  val persistent_claset_of_theory :
      {thyname : string} -> claset option

  (* Reconstruct the named theory's persistent declarations and then catch
     them up with rules derived from the caller's current TypeBase. *)
  val claset_of_theory : {thyname : string} -> claset option
  val merge_clasets : string list -> claset option
  val with_claset : claset -> ('a -> 'b) -> ('a -> 'b)

  val add_safe_wrapper : string * NTactical.wrapper -> claset -> claset
  val add_unsafe_wrapper : string * NTactical.wrapper -> claset -> claset
  val del_safe_wrapper : string -> claset -> claset
  val del_unsafe_wrapper : string -> claset -> claset
  val app_safe_wrappers : claset -> NTactical.ntactic -> NTactical.ntactic
  val app_unsafe_wrappers : claset -> NTactical.ntactic -> NTactical.ntactic

  val rules_of : claset -> (rulespec * (string * thm)) list
  val pp_claset : claset Parse.pprinter

  val claset_part : part -> claset -> claset_part
  val safe0_part : claset -> claset_part
  val safep_part : claset -> claset_part
  val unsafe_part : claset -> claset_part
  val dup_part : claset -> claset_part
  val match_intro_candidates : claset_part -> term -> (tag * brl) list
  val match_elim_candidates : claset_part -> term -> (tag * brl) list
  val unify_intro_candidates : claset_part -> term -> (tag * brl) list
  val unify_elim_candidates : claset_part -> term -> (tag * brl) list
  val unify_intro_candidates_measured :
    (unit -> unit) -> claset_part -> term -> (tag * brl) list
  val unify_elim_candidates_measured :
    (unit -> unit) -> claset_part -> term -> (tag * brl) list

  val SIntro : thm -> thm
  val Intro : thm -> thm
  val SElim : thm -> thm
  val Elim : thm -> thm
  val SDest : thm -> thm
  val Dest : thm -> thm
  val Simp : thm -> thm
  val Iff : thm -> thm
  val Del : string -> thm

  val destSIntro : thm -> thm option
  val destIntro : thm -> thm option
  val destSElim : thm -> thm option
  val destElim : thm -> thm option
  val destSDest : thm -> thm option
  val destDest : thm -> thm option
  val destSimp : thm -> thm option
  val destIff : thm -> thm option
  val destDel : thm -> string option

  val process_claset_tags : thm list -> claset -> claset * thm list

  type simp_arg_split =
    {simp_rules : thm list,
     iff_rules : thm list,
     simp_controls : thm list,
     rest : thm list}
  val classify_simp_args : thm list -> simp_arg_split

  (* Assemble the classical rules and inserted facts for one tactic
     invocation.  Engines insert the facts with INSERT_FACTS_TAC, lifting it
     into their own tactic representation where necessary. *)
  val invocation_claset : claset -> thm list -> claset * thm list

  (* Inserts the facts so that they appear in the assumption list in the
     order given, as Isabelle's cut_facts_tac does. *)
  val INSERT_FACTS_TAC : thm list -> tactic

  (* The persistent form of a rule name, as recorded in the claset delta
     stream: a "Thy$Name" kernel name where the source name identifies a
     stored theorem, and the name unchanged otherwise. *)
  val normalise_rule_name : string -> string

  (* A contribution must be pure and deterministic.  Its result for a given
     tyinfo may be evaluated more than once; invocation count and timing are
     not API guarantees. *)
  val register_tyinfo_contribution :
      string * (TypeBasePure.tyinfo -> (rulespec * (string * thm)) list)
      -> unit

  val iff_rules :
    string -> thm -> (rulespec * (string * thm)) list

  val claset_config : {hyp_subst_tac : tactic, size_of : goal -> int}
end
