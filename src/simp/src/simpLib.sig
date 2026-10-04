(* =====================================================================
 * FILE        : simpLib.sig
 * DESCRIPTION : A programmable, contextual, conditional simplifier
 *
 * AUTHOR      : Donald Syme
 *               Based loosely on original HOL rewriting by
 *               Larry Paulson et al, and on the Isabelle simplifier.
 * =====================================================================*)


signature simpLib =
sig
 include Abbrev

   (* ---------------------------------------------------------------------
    * type simpset
    *
    * A simpset contains:
    *    - a collection of rewrite rules
    *    - a collection of equational conversions
    *    - a traversal strategy for applying them
    *
    * The traversal strategy may include other actions, especially
    * decision procedures, which can work cooperatively with
    * rewriting during simplification.
    *
    * REWRITE RULES
    *
    * Simpsets are foremost a collection of rewrite theorems stored
    * efficiently in a termnet.  These are made into conversions
    * by using COND_REWR_CONV.
    *
    * CONVERSIONS IN SIMPSETS
    *
    * Simpsets can contain arbitrary user conversions, as well as
    * rewrites and contextual-rewrites.  These conversions should
    * be thought of as infinite families of rewrites.
    *
    * Conversions can be keyed by term patterns (implemented
    * using termnets).  Thus a conversion won't even be called if
    * the target term doesn't match (in the termnet sense of matching)
    * its key.
    * ---------------------------------------------------------------------*)

 type thname = KernelSig.kernelname
 type convdata = { name: string,
                    key: (term list * term) option,
                  trace: int,
                   conv: (term list -> term -> thm) -> term list -> conv}

  type stdconvdata = { name: string,
                       pats: term list,
                       conv: conv}

  type relsimpdata = {refl: thm,
                      trans:thm,
                      weakenings:thm list,
                      subsets : thm list,
                      rewrs : thm list}

  type controlled_thm = BoundedRewrites.controlled_thm

  type ssfrag
  type simpset
  type rewrite_source

  val SSFRAG :
    {name : string option,
     convs: convdata list,
     rewrs: (thname option * thm) list,
        ac: (thm * thm) list,
    filter: (controlled_thm -> controlled_thm list) option,
    dprocs: Traverse.reducer list,
     congs: thm list} -> ssfrag

  val empty_ssfrag : ssfrag
  val ssf_upd_rewrs :
    ((thname option * thm) list -> (thname option * thm) list) ->
    ssfrag -> ssfrag
  val frag_rewrites : ssfrag -> thm list
  val frag_name : ssfrag -> string option

  val register_frag : ssfrag -> ssfrag
  val lookup_named_frag : string -> ssfrag option
  val all_named_frags : unit -> string list

  (*------------------------------------------------------------------------*)
  (* Easy building of common kinds of ssfrag objects                        *)
  (*------------------------------------------------------------------------*)

  val Cong        : thm -> thm
  val Split       : thm -> thm
  val AC          : thm -> thm -> thm
  val Excl        : string -> thm
  val ExclSF      : string -> thm
  val Req0        : thm -> thm
  val ReqD        : thm -> thm
  val SF          : ssfrag -> thm

  val rewrites       : thm list -> ssfrag
  val rewrites_with_names : (thname * thm) list -> ssfrag
  val dproc_ss       : Traverse.reducer -> ssfrag
  val ac_ss          : (thm * thm) list -> ssfrag
  val conv_ss        : convdata -> ssfrag
  val relsimp_ss     : relsimpdata -> ssfrag
  val looper_ss      : string * (simpset -> tactic) -> ssfrag
  val solver_ss      : Traverse.ssolver -> ssfrag
  val safe_solver_ss : Traverse.ssolver -> ssfrag
  val std_conv_ss    : stdconvdata -> ssfrag
  val merge_ss       : ssfrag list -> ssfrag
  val name_ss        : string -> ssfrag -> ssfrag
  val named_rewrites : string -> thm list -> ssfrag
  val named_rewrites_with_names : string -> (thname * thm) list -> ssfrag
  val named_merge_ss : string -> ssfrag list -> ssfrag
  val type_ssfrag    : hol_type -> ssfrag
  val tyi_to_ssdata  : TypeBasePure.tyinfo -> ssfrag

  val partition_ssfrags : string list -> ssfrag list ->
                          (ssfrag list * ssfrag list)

   (* ---------------------------------------------------------------------
    * mk_simpset: Joins several ssfrag fragments to make a simpset.
    * This is a "runtime" object - the ssfrag can be thought of as the
    * static, data objects.
    * Beware of duplicating information - you should only
    * merge distinct ssfrag fragments! (like BOOL_ss and PURE_ss).
    * You cannot merge simpsets with lower-case names (like bool_ss).
    *
    * The order of the merge is significant w.r.t. congruence rules
    * and rewrite makers.
    * ---------------------------------------------------------------------*)

  type weakener_data = Travrules.preorder list * thm list * Traverse.reducer

  val empty_ss        : simpset
  val ssfrags_of      : simpset -> ssfrag list
  (* Actual compiled rewrite sources after the supplied controls, and
     untagged supplied rewrites. Conversions are excluded. Strategy and
     decision-procedure copies share the source list; new rules prepend
     their sources. Filtering, exclusions and clearing remove sources. *)
  val rewrite_sources : simpset -> thm list ->
      (thname option * thm) list * thm list
  (* Handles identify native rule occurrences across history replay;
     installed views are omitted. Views share the current source's
     exact compiled name and rewrite allowance, and disappear if that
     source is removed or its compiled statement changes. *)
  val rewrite_source_handles : simpset -> rewrite_source list
  (* Apply ordinary argument directives before binding supplied rewrites.
     Compatible surviving native occurrences retain their remaining uses. *)
  val prepare_rewrite_arguments : simpset -> thm list -> simpset * thm list
  val source_rewrite : rewrite_source -> thname option * thm
  val same_rewrite_source : rewrite_source * rewrite_source -> bool
  (* Stable origin order; compatibility also requires same_rewrite_source. *)
  val rewrite_source_compare : rewrite_source * rewrite_source -> order
  val rewrite_views : (rewrite_source * thm) list -> ssfrag
  type rewrite_bundle
  (* Compile supplied rules without installing or priming ambient reducers.
     Install once per simpset; nested consumers of the same binding and its
     associated views share the compiled rules' actual controls. History
     replay retains these compiled shapes without calling the rewrite maker
     again. Ordinary replay resets declared quotas, preserving sharing
     between conjuncts; opt-in control preservation keeps remaining uses. *)
  val prepare_rewrite_bundle : simpset -> thm list -> rewrite_bundle
  (* Combine existing compiled bundles without refreshing quotas or origins.
     Duplicate bindings are rejected; installation retains each event. *)
  val combine_rewrite_bundles : rewrite_bundle list -> rewrite_bundle
  val rewrite_bundle_rules : rewrite_bundle ->
    (thm * rewrite_source list) list
  val install_rewrite_bundle : rewrite_bundle ->
    (rewrite_source * thm) list -> simpset -> simpset
  (* Suspend exact active compiled occurrences and their attached views.
     Other conjuncts keep their names and remaining rewrite allowances;
     history replay retains suspension and opaque contexts lose the
     suspended conjuncts. Missing/incompatible handles change nothing. *)
  val suspend_rewrite_sources : rewrite_source list -> simpset -> simpset
  (* Changed conversion keys and opaque traversal/context changes.
     Existing decision procedures may depend on every added context rule. *)
  val rewrite_context_changes : simpset * simpset ->
    {keys : (term list * term) list, rebuild : bool,
     context_sensitive : bool}
  val mk_simpset      : ssfrag list -> simpset
  val remove_ssfrags  : string list -> simpset -> simpset
  (* Opt-in fragment removal sharing surviving sources' actual controls,
     including exhausted counters, with the input and its existing views.
     Missing names raise UNCHANGED, as with ordinary removal. *)
  val remove_ssfrags_preserving_controls :
    string list -> simpset -> simpset

  (* Removes from every fragment the rewrites the predicate rejects,
     keeping the rest of the simpset's history -- what it has excluded
     by name, its limit, its rewrite maker, its strategy -- as it
     stands.  Rebuilding from ssfrags_of does not: that keeps the
     fragments alone.  Returns the simpset itself where nothing is
     rejected, and never raises Conv.UNCHANGED. *)
  val filter_rewrites :
    ((thname option * thm) -> bool) -> simpset -> simpset
  (* Invocation filtering retains surviving sources' actual controls,
     including exhausted quotas shared with their installed aliases. *)
  val filter_rewrites_preserving_controls :
    ((thname option * thm) -> bool) -> simpset -> simpset

  (* Like remove_ssfrags, but additionally records the names so that any
     subsequent ++ of a named fragment with one of those names is silently
     a no-op.  force_add is the override for that prohibition.
     Never raises Conv.UNCHANGED. *)
  val exclude_ssfrags : string list -> simpset -> simpset
  val force_add       : simpset -> ssfrag -> simpset

  val ssfrag_names_of : simpset -> string list
  val ++              : simpset * ssfrag -> simpset  (* infix *)
  val -*              : simpset * string list -> simpset (* infix *)
  val remove_simps    : string list -> simpset -> simpset (* curried version *)
  val &&              : simpset * thm list -> simpset  (* infix *)
  val limit           : int -> simpset -> simpset
  val unlimit         : simpset -> simpset
  val add_named_rwt   : (thname * thm) -> ssfrag -> ssfrag

  val add_looper : string * (simpset -> tactic) -> simpset -> simpset
  val del_looper : string -> simpset -> simpset
  val set_looper : string * (simpset -> tactic) -> simpset -> simpset
  val add_split : thm -> simpset -> simpset
  val del_split : string -> simpset -> simpset
  val split_ss : ssfrag
  val add_unsafe_solver : Traverse.ssolver -> simpset -> simpset
  val add_safe_solver : Traverse.ssolver -> simpset -> simpset
  val set_unsafe_solvers : Traverse.ssolver list -> simpset -> simpset
  val set_safe_solvers : Traverse.ssolver list -> simpset -> simpset
  val remove_solver : string -> simpset -> simpset
  val set_subgoaler : Traverse.subgoaler -> simpset -> simpset
  val set_cond_depth : int -> simpset -> simpset
  val set_term_ord : (term * term -> order) -> simpset -> simpset
  val mk_tactic_solver : string * tactic -> Traverse.ssolver
  val clear_rules : simpset -> simpset

  val add_weakener : weakener_data -> simpset -> simpset

  val add_relsimp  : relsimpdata -> simpset -> simpset

  val traversedata_for_ss: simpset -> Traverse.traverse_data

  (* The traversal-strategy settings that traverse_data does not carry;
     xtraversedata_for_ss is the pair the extended Traverse entry points
     take.  traversedata_for_ss alone therefore describes a traversal at
     the default settings, not at the simpset's own. *)
  val traverseconfig_for_ss: simpset -> Traverse.traverse_config
  val xtraversedata_for_ss: simpset -> Traverse.xtraverse_data


   (* ---------------------------------------------------------------------
    * SIMP_CONV : simpset -> conv
    *
    * SIMP_CONV makes a simplification conversion from the given simpset.  The
    * conversion uses a top-depth strategy for rewriting.  It sets both
    * the solver and the depther to be SIMP_CONV itself.
    *
    * FAILURE CONDITIONS
    *
    * SIMP_CONV never fails, though it may diverge.  Beware of
    * divergence when trying to solve conditions to conditional rewrites.
    * ---------------------------------------------------------------------*)

   val SIMP_PROVE : simpset -> thm list -> term -> thm
   val SIMP_CONV  : simpset -> thm list -> conv
   (* Opt-in child-first conversion. A certified eta contraction preserves
      function argument heads before child descent, except at logical
      binders and applications selected by keep_abstraction. The standard
      ETA fragment also respects this selection after descent. Congruence
      rules control descent; charge runs before contraction, descent and
      reducer work. Traverse.charge_only retains the contraction policy.
      The ordinary SIMP_CONV strategy is unchanged. *)
   val SIMP_CONV_CHILD_FIRST :
     Traverse.child_first_policy -> simpset -> thm list -> conv

   (* Prepare one ambient child-first traversal for rewrite-view
      derivation. Arguments preserves the root. Each conversion uses
      fresh declared bounded allowances privately and restores the
      caller's counters, including on exceptions. Derivation cannot
      spend an invocation's allowance or depend on earlier consumption.
      The indexed
      pre-test is conservative for opaque reducers and congruences;
      conditional premises require attempting normalization regardless. *)
   val prepare_child_first : Traverse.child_first_policy -> simpset ->
     {normalize : thm list -> conv,
      arguments : thm list -> conv,
      may_reduce_arguments : term -> bool}
   (* As prepare_child_first, also observing inputs, results and every
      child/condition offered to traversal. Failed conditional attempts
      and unchanged terms remain dependencies. *)
   val prepare_child_first_observed :
     (term -> unit) -> Traverse.child_first_policy -> simpset ->
     {normalize : thm list -> conv,
      arguments : thm list -> conv,
      may_reduce_arguments : term -> bool}

   (* ---------------------------------------------------------------------
    * SIMP_TAC : simpset -> tactic
    * ASM_SIMP_TAC : simpset -> tactic
    * FULL_SIMP_TAC : simpset -> tactic
    *
    * SIMP_TAC makes a simplification tactic from the given simpset.  The
    * tactic uses a top-depth strategy for rewriting, and will be recursively
    * reapplied when a simplification step makes a change to a term.
    * This is done in the same way as similar to TOP_DEPTH_CONV.
    *
    * ASM_SIMP_TAC draws extra rewrites (conditional and unconditional)
    * from the assumption list.  These are also added to the context that
    * will be passed to conversions.
    *
    * FULL_SIMP_TAC simplifies the assumptions one by one, before
    * simplifying the goal.  The assumptions are simplified in the order
    * that they are found in the assumption list, and the simplification
    * of each assumption is used when simplifying the next assumption.
    *
    * FAILURE CONDITIONS
    *
    * These tactics never fail, though they may diverge.
    * ---------------------------------------------------------------------*)

   type simp_mode = {safe : bool}
   val GEN_SIMP_TAC  : simp_mode -> simpset -> thm list -> tactic
   val GEN_SIMP_TAC_CHILD_FIRST :
     Traverse.child_first_policy -> simp_mode -> simpset -> thm list -> tactic
   val SIMP_TAC      : simpset -> thm list -> tactic
   val simp_tac      : simpset -> thm list -> tactic
   val ASM_SIMP_TAC  : simpset -> thm list -> tactic
   val asm_simp_tac  : simpset -> thm list -> tactic
   val FULL_SIMP_TAC : simpset -> thm list -> tactic
   val full_simp_tac : simpset -> thm list -> tactic

   val REV_FULL_SIMP_TAC          : simpset -> thm list -> tactic
   val rev_full_simp_tac          : simpset -> thm list -> tactic
   val NO_STRIP_FULL_SIMP_TAC     : simpset -> thm list -> tactic
   val NO_STRIP_REV_FULL_SIMP_TAC : simpset -> thm list -> tactic

   type simptac_config =
        {strip : bool, elimvars : bool, droptrues : bool, oldestfirst : bool}
   val psr : simptac_config -> simpset -> tactic
     (* Pop, Simp, Rotate to back *)
   val allasms : simptac_config -> simpset -> tactic
     (* do the above to all the assumptions in turn *)
   type xsimptac_config =
        {base : simptac_config, concl_in_fixpoint : bool,
         imp_rebuild : bool, imp_premises : bool}
     (* imp_premises discharges the conclusion's leading implications
        into the assumptions before the fixpoint, so that a premise
        written as an antecedent is simplified with the others in
        context rather than only with the ones before it. *)
   val GEN_GLOBAL_SIMP_TAC :
     simp_mode -> xsimptac_config -> simpset -> thm list -> tactic
   (* The same assumption/conclusion fixpoint, with opt-in child-first
      traversal for each simplification pass. Root-rebuild flags retain
      their explicit wrapper behavior. *)
   val GEN_GLOBAL_SIMP_TAC_CHILD_FIRST :
     Traverse.child_first_policy -> simp_mode -> xsimptac_config ->
     simpset -> thm list -> tactic
   (* The bundle is already installed in the given invocation simpset.
      Retain its untagged solver context and own rewrite controls across
      local marker replay; never reinstall or recompile it as arguments. *)
   val GEN_GLOBAL_SIMP_TAC_CHILD_FIRST_BOUND :
     Traverse.child_first_policy -> simp_mode -> xsimptac_config ->
     simpset -> rewrite_bundle -> thm list -> tactic
   val global_simp_tac : simptac_config -> simpset -> thm list -> tactic
     (* do allasms until quiescence, then simp in the goal as well *)

   (* ---------------------------------------------------------------------
    * SIMP_RULE : simpset -> tactic
    * ASM_SIMP_RULE : simpset -> tactic
    *
    * Make a simplification rule from the given simpset.  The
    * rule uses a top-depth strategy for rewriting.
    *
    * FAILURE CONDITIONS
    *
    * These rules never fail, though they may diverge.
    * ---------------------------------------------------------------------*)

   val SIMP_RULE     : simpset -> thm list -> thm -> thm
   val ASM_SIMP_RULE : simpset -> thm list -> thm -> thm

   (* ---------------------------------------------------------------------*)
   (* Reporting which rewrite rules actually fired.  This is an aid for a
      human watching a simplification, so it hands the list back with the
      result rather than leaving it in a ref to be read afterwards; there
      is no flag to set and none to forget to unset.  Nested tracking
      reports only the inner extent.                                     *)
   (* ---------------------------------------------------------------------*)

   val track : ('a -> 'b) -> 'a -> 'b * thm list

   (* ---------------------------------------------------------------------*)
   (* Prettyprinters for ssfrags and simpsets.                             *)
   (* ---------------------------------------------------------------------*)

   val pp_ssfrag : ssfrag Parse.pprinter
   val pp_simpset : simpset Parse.pprinter

end
