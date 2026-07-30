signature clasetLib =
sig
  include Abbrev

  type rulekind = clasetRules.rulekind
  type rulespec = clasetRules.rulespec
  type tag = clasetRules.tag
  type brl = clasetRules.brl
  type info = clasetRules.info

  type claset
  type claset_part

  (* A declaration as the aesop retrieval paths return it.  [info] is the
     canonicalisation the claset derived when the rule was declared -- the
     classical forms clasetRules.ext_info builds with real kernel
     inferences (CLASSICAL_RULE, MAKE_ELIM_RULE, DUP_ELIM_RULE,
     SWAP_INTRO_RULE).  An engine needing those forms -- the aesop engine
     needs them both to classify a rule as Safe0 or SafeP and to build its
     step -- reads them here rather than re-deriving them from [thm] on
     every goal expansion. *)
  type aesop_rule =
    {name : string, spec : rulespec, thm : thm, info : info}

  datatype part = Safe0Part | SafePPart | UnsafePart | DupPart

  val empty_cs : claset

  val add_rule : rulespec -> string * thm -> claset -> claset

  (* Adds a rule a library derived from a user declaration.  Behaves as
     add_rule, but a cross-kind clash is not reported -- the caller never
     named the rule, and invocation-scoped tactics would warn on every goal
     -- and a rule whose conclusion duplicates an installed one is added
     rather than dropped, so each declaration owns the rules derived from
     it and retracting one leaves another's in place.  A name already in
     use is still refused. *)
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

  (* Every declaration of the claset, in canonical declaration order.  A
     caller that compares a theorem against a declaration's derived forms
     -- classical replay identifies the declaration an applied theorem came
     from that way -- reads them here rather than deriving them again for
     each declaration it scans. *)
  val all_rules : claset -> aesop_rule list
  (* The name/theorem view of [all_rules], in the same order. *)
  val rules_of : claset -> (rulespec * (string * thm)) list
  (* The claset's Norm declarations, in [rules_of] order.  The aesop
     normalisation phase applies all of them to every goal rather than
     retrieving by goal shape, so they are kept as a list; this is the
     precomputed equivalent of filtering [rules_of] by kind. *)
  val norm_rules : claset -> aesop_rule list
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

  (* Aesop retrieval is unification-based and retains each declaration's
     complete rulespec.  Target candidates comprise Intro rules;
     hypothesis candidates comprise Elim, Dest, and Forward rules.  Safe
     rules precede unsafe rules.  Within those groups the order is
     classical candidate order, and decreasing success percentage followed
     by classical candidate order, respectively. *)
  val aesop_target_rules :
    claset -> {q : term, qvars : term HOLset.set} -> aesop_rule list
  val aesop_hyp_rules :
    claset -> {q : term, qvars : term HOLset.set} -> aesop_rule list

  val SIntro : thm -> thm
  val Intro : thm -> thm
  val SElim : thm -> thm
  val Elim : thm -> thm
  val SDest : thm -> thm
  val Dest : thm -> thm
  val Simp : thm -> thm
  val Iff : thm -> thm
  val Norm : thm -> thm
  val Forward : thm -> thm
  val SForward : thm -> thm
  val Del : string -> thm

  val destSIntro : thm -> thm option
  val destIntro : thm -> thm option
  val destSElim : thm -> thm option
  val destElim : thm -> thm option
  val destSDest : thm -> thm option
  val destDest : thm -> thm option
  val destSimp : thm -> thm option
  val destIff : thm -> thm option
  val destNorm : thm -> thm option
  val destForward : thm -> thm option
  val destSForward : thm -> thm option
  val destDel : thm -> string option

  val process_claset_tags : thm list -> claset -> claset * thm list

  (* A name of the form "<prefix><n>", with n at least [from], that no
     declaration in the claset uses.  Engines name invocation-scoped rules
     -- those coming from marker arguments -- this way, so that such a rule
     can never collide with a user declaration. *)
  val fresh_rule_name : {prefix : string, from : int} -> claset -> string

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
     order given.  They occupy the most-recent end, ahead of the goal's own
     assumptions, which is what the classical engines' recency tie-break and
     FIRST_ASSUM see first; Isabelle's cut_facts_tac instead makes them the
     first premises, so a traversal that starts from the oldest assumption
     -- asm_full_simp's, for one -- reaches them last rather than first. *)
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
