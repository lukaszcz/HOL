(* Nested structures make inter-module sharing equations executable SML.
   Names T/C/O/R/S/G/Pure/Bool/Default denote the modules in DESIGN.md.
   No structure implementing this entire signature is fabricated here. *)
signature Task08API =
sig
  structure T : Task08TraverseExt
  structure C :
  sig
    include Abbrev
    type config =
      {solver : term list -> term -> thm, stack : term list,
       cond_depth : int option, term_ord : term * term -> order}
    val is_var_perm : term * term -> bool
    val COND_REWR_CONVS : string * thm -> bool ->
      {legacy : (term list -> term -> thm) -> term list -> conv,
       configured : config -> conv}
    val COND_REWR_CONV_WITH_CONFIG : string * thm -> bool -> config -> conv
    val COND_REWR_CONV_WITH_CONTEXT : string * thm -> bool ->
      {solver : term list -> term -> thm, stack : term list,
       cond_depth : int, term_ord : term * term -> order} -> conv
  end
  structure O :
  sig
    type congproc = Opening.congproc
    val THREADED_CONGPROC :
      ({Rinst : Term.term, arg : Term.term} -> Thm.thm) ->
      Thm.thm -> congproc
  end
  structure R :
  sig
    type preorder = Travrules.preorder
    type travrules = Travrules.travrules
    val mk_threaded_travrules : preorder list -> Thm.thm list -> travrules
  end
  structure S :
  sig
    include Abbrev
    type thname = KernelSig.kernelname
    type convdata =
      {name : string, key : (term list * term) option, trace : int,
       conv : (term list -> term -> thm) -> term list -> conv}
    type stdconvdata = {name : string, pats : term list, conv : conv}
    type relsimpdata =
      {refl : thm, trans : thm, weakenings : thm list,
       subsets : thm list, rewrs : thm list}
    type controlled_thm = BoundedRewrites.controlled_thm
    type ssfrag
    type simpset
    type rewrite_source
    type rewrite_bundle
    val SSFRAG :
      {name : string option, convs : convdata list,
       rewrs : (thname option * thm) list, ac : (thm * thm) list,
       filter : (controlled_thm -> controlled_thm list) option,
       dprocs : T.reducer list, congs : thm list} -> ssfrag
    val empty_ssfrag : ssfrag
    val ssf_upd_rewrs :
      ((thname option * thm) list -> (thname option * thm) list) ->
      ssfrag -> ssfrag
    val frag_rewrites : ssfrag -> thm list
    val frag_name : ssfrag -> string option
    val register_frag : ssfrag -> ssfrag
    val lookup_named_frag : string -> ssfrag option
    val all_named_frags : unit -> string list
    val Cong : thm -> thm
    val Split : thm -> thm
    val AC : thm -> thm -> thm
    val Excl : string -> thm
    val ExclX : string -> thm
    val ExclSF : string -> thm
    val Req0 : thm -> thm
    val ReqD : thm -> thm
    val SF : ssfrag -> thm
    val rewrites : thm list -> ssfrag
    val rewrites_with_names : (thname * thm) list -> ssfrag
    val threaded_cong_ss : thm list -> ssfrag
    val dproc_ss : T.reducer -> ssfrag
    val ac_ss : (thm * thm) list -> ssfrag
    val conv_ss : convdata -> ssfrag
    val relsimp_ss : relsimpdata -> ssfrag
    val looper_ss : string * (simpset -> tactic) -> ssfrag
    val solver_ss : T.ssolver -> ssfrag
    val safe_solver_ss : T.ssolver -> ssfrag
    val std_conv_ss : stdconvdata -> ssfrag
    val merge_ss : ssfrag list -> ssfrag
    val name_ss : string -> ssfrag -> ssfrag
    val named_rewrites : string -> thm list -> ssfrag
    val named_rewrites_with_names : string -> (thname * thm) list -> ssfrag
    val named_merge_ss : string -> ssfrag list -> ssfrag
    val type_ssfrag : hol_type -> ssfrag
    val tyi_to_ssdata : TypeBasePure.tyinfo -> ssfrag
    val partition_ssfrags : string list -> ssfrag list ->
      ssfrag list * ssfrag list
    type weakener_data = Travrules.preorder list * thm list * T.reducer
    val empty_ss : simpset
    val mk_simpset : ssfrag list -> simpset
    val ssfrags_of : simpset -> ssfrag list
    val ssfrag_names_of : simpset -> string list
    val ++ : simpset * ssfrag -> simpset
    val -* : simpset * string list -> simpset
    val && : simpset * thm list -> simpset
    val remove_simps : string list -> simpset -> simpset
    val remove_ssfrags : string list -> simpset -> simpset
    val remove_ssfrags_preserving_controls : string list -> simpset -> simpset
    val filter_rewrites : ((thname option * thm) -> bool) ->
      simpset -> simpset
    val filter_rewrites_preserving_controls :
      ((thname option * thm) -> bool) -> simpset -> simpset
    val exclude_ssfrags : string list -> simpset -> simpset
    val force_add : simpset -> ssfrag -> simpset
    val limit : int -> simpset -> simpset
    val unlimit : simpset -> simpset
    val add_named_rwt : (thname * thm) -> ssfrag -> ssfrag
    val rewrite_sources : simpset -> thm list ->
      (thname option * thm) list * thm list
    val rewrite_source_handles : simpset -> rewrite_source list
    val prepare_rewrite_arguments : simpset -> thm list -> simpset * thm list
    val source_rewrite : rewrite_source -> thname option * thm
    val same_rewrite_source : rewrite_source * rewrite_source -> bool
    val rewrite_source_compare : rewrite_source * rewrite_source -> order
    val rewrite_views : (rewrite_source * thm) list -> ssfrag
    val prepare_rewrite_bundle : simpset -> thm list -> rewrite_bundle
    val combine_rewrite_bundles : rewrite_bundle list -> rewrite_bundle
    val rewrite_bundle_rules : rewrite_bundle ->
      (thm * rewrite_source list) list
    val install_rewrite_bundle : rewrite_bundle ->
      (rewrite_source * thm) list -> simpset -> simpset
    val suspend_rewrite_sources : rewrite_source list -> simpset -> simpset
    val rewrite_context_changes : simpset * simpset ->
      {keys : (term list * term) list, rebuild : bool,
       context_sensitive : bool}
    val add_looper : string * (simpset -> tactic) -> simpset -> simpset
    val del_looper : string -> simpset -> simpset
    val set_looper : string * (simpset -> tactic) -> simpset -> simpset
    val add_split : thm -> simpset -> simpset
    val del_split : string -> simpset -> simpset
    val split_ss : ssfrag
    val add_unsafe_solver : T.ssolver -> simpset -> simpset
    val add_safe_solver : T.ssolver -> simpset -> simpset
    val set_unsafe_solvers : T.ssolver list -> simpset -> simpset
    val set_safe_solvers : T.ssolver list -> simpset -> simpset
    val remove_solver : string -> simpset -> simpset
    val set_subgoaler : T.subgoaler -> simpset -> simpset
    val set_cond_depth : int -> simpset -> simpset
    val set_term_ord : (term * term -> order) -> simpset -> simpset
    val mk_tactic_solver : string * tactic -> T.ssolver
    val clear_rules : simpset -> simpset
    val add_weakener : weakener_data -> simpset -> simpset
    val add_relsimp : relsimpdata -> simpset -> simpset
    val traversedata_for_ss : simpset -> T.traverse_data
    val traverseconfig_for_ss : simpset -> T.traverse_config
    val xtraversedata_for_ss : simpset -> T.xtraverse_data
    val SIMP_PROVE : simpset -> thm list -> term -> thm
    val SIMP_CONV : simpset -> thm list -> conv
    val SIMP_CONV_CHILD_FIRST : T.child_first_policy ->
      simpset -> thm list -> conv
    val prepare_child_first : T.child_first_policy -> simpset ->
      {normalize : thm list -> conv, arguments : thm list -> conv,
       may_reduce_arguments : term -> bool}
    val prepare_child_first_observed : (term -> unit) ->
      T.child_first_policy -> simpset ->
      {normalize : thm list -> conv, arguments : thm list -> conv,
       may_reduce_arguments : term -> bool}
    type simp_mode = {safe : bool}
    val GEN_SIMP_TAC : simp_mode -> simpset -> thm list -> tactic
    val GEN_SIMP_TAC_CHILD_FIRST : T.child_first_policy -> simp_mode ->
      simpset -> thm list -> tactic
    val SIMP_TAC : simpset -> thm list -> tactic
    val simp_tac : simpset -> thm list -> tactic
    val ASM_SIMP_TAC : simpset -> thm list -> tactic
    val asm_simp_tac : simpset -> thm list -> tactic
    val FULL_SIMP_TAC : simpset -> thm list -> tactic
    val full_simp_tac : simpset -> thm list -> tactic
    val REV_FULL_SIMP_TAC : simpset -> thm list -> tactic
    val rev_full_simp_tac : simpset -> thm list -> tactic
    val NO_STRIP_FULL_SIMP_TAC : simpset -> thm list -> tactic
    val NO_STRIP_REV_FULL_SIMP_TAC : simpset -> thm list -> tactic
    type simptac_config =
      {strip : bool, elimvars : bool, droptrues : bool, oldestfirst : bool}
    val psr : simptac_config -> simpset -> tactic
    val allasms : simptac_config -> simpset -> tactic
    type xsimptac_config =
      {base : simptac_config, concl_in_fixpoint : bool,
       imp_rebuild : bool, imp_premises : bool}
    val GEN_GLOBAL_SIMP_TAC : simp_mode -> xsimptac_config ->
      simpset -> thm list -> tactic
    val GEN_GLOBAL_SIMP_TAC_CHILD_FIRST : T.child_first_policy ->
      simp_mode -> xsimptac_config -> simpset -> thm list -> tactic
    val GEN_GLOBAL_SIMP_TAC_CHILD_FIRST_BOUND : T.child_first_policy ->
      simp_mode -> xsimptac_config -> simpset -> rewrite_bundle ->
      thm list -> tactic
    val global_simp_tac : simptac_config -> simpset -> thm list -> tactic
    val SIMP_RULE : simpset -> thm list -> thm -> thm
    val ASM_SIMP_RULE : simpset -> thm list -> thm -> thm
    val track : ('a -> 'b) -> 'a -> 'b * thm list
    val pp_ssfrag : ssfrag Parse.pprinter
    val pp_simpset : simpset Parse.pprinter
  end
  structure G :
  sig
    include Abbrev
    datatype congsetfrag = CSFRAG of
      {relations : Travrules.preorder list, rewrs : thm list,
       congs : thm list, dprocs : T.reducer list}
    type congset
    val lift_fragment : congLib.congsetfrag -> congsetfrag
    val empty_congset : congset
    val mk_congset : congsetfrag list -> congset
    val cs_addfrag : congset -> congsetfrag -> congset
    val merge_cs : congsetfrag list -> congsetfrag
    val csfrag_rewrites : thm list -> congsetfrag
    val add_csfrag_rewrites : congsetfrag -> thm list -> congsetfrag
    val CONGRUENCE_SIMP_CONV : term -> congset -> S.simpset ->
      thm list -> conv
    val CONGRUENCE_SIMP_QCONV : term -> congset -> S.simpset ->
      thm list -> conv
    val CONGRUENCE_EQ_SIMP_CONV : congset -> S.simpset -> thm list -> conv
    val CONGRUENCE_SIMP_RULE : congset -> S.simpset -> thm list -> thm -> thm
    val CONGRUENCE_SIMP_TAC : congset -> S.simpset -> thm list -> tactic
    val ASM_CONGRUENCE_SIMP_TAC : congset -> S.simpset -> thm list -> tactic
    val FULL_CONGRUENCE_SIMP_TAC : congset -> S.simpset -> thm list -> tactic
  end
  structure Pure :
  sig
    val PURE_ss : S.ssfrag
    val pure_ss : S.simpset
  end
  structure Bool :
  sig
    val BOOL_ss : S.ssfrag
    val NOT_ss : S.ssfrag
    val CONG_ss : S.ssfrag
    val ETA_ss : S.ssfrag
    val UNWIND_ss : S.ssfrag
    val NORMEQ_ss : S.ssfrag
    val ABBREV_ss : S.ssfrag
    val LABEL_CONG_ss : S.ssfrag
    val HIDE_ss : S.ssfrag
    val bool_ss : S.simpset
  end
  structure Default :
  sig
    (* Explicit construction inputs, never an ordinary compiled set. *)
    datatype delta = Add of KernelSig.kernelname * Thm.thm | Remove of string
    datatype step = TheoryBatch of string * delta list
                  | LocalDelta of delta
                  | Fragment of S.ssfrag
                  | TypeInfo of TypeBasePure.tyinfo
                  | Update of (S.simpset -> S.simpset)
    type recipe = {seed : unit -> S.simpset, steps : step list}
    type provider
    val build : recipe -> provider
    val value : provider -> S.simpset
    val map : (S.simpset -> S.simpset) -> provider -> provider
    val install : provider -> Context.t -> Context.t
    (* Unprepared => NONE; never builds or translates ordinary state. *)
    val get_of : Context.t -> provider option
    val map_of : (S.simpset -> S.simpset) -> Context.t -> Context.t
    val with_updates : (S.simpset -> S.simpset) ->
      ('a -> 'b) -> 'a -> 'b
  end
end
