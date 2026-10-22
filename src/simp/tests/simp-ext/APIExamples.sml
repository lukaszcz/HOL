(* Compiled clients of the actual, sealed production modules. No promotion
   from an ordinary simpset or fragment is available or needed. *)
structure APIExamples =
struct
  val pure : simpExtLib.simpset = pureSimpsExt.pure_ss
  val bools : simpExtLib.simpset = boolSimpsExt.bool_ss
  val fragments : simpExtLib.ssfrag list =
    [pureSimpsExt.PURE_ss, boolSimpsExt.BOOL_ss, boolSimpsExt.NOT_ss,
     boolSimpsExt.CONG_ss, boolSimpsExt.UNWIND_ss, boolSimpsExt.ETA_ss,
     boolSimpsExt.NORMEQ_ss, boolSimpsExt.ABBREV_ss,
     boolSimpsExt.LABEL_CONG_ss, boolSimpsExt.HIDE_ss,
     boolSimpsExt.CONJ_ss, boolSimpsExt.DISJ_ss,
     boolSimpsExt.COND_elim_ss, boolSimpsExt.LIFT_COND_ss,
     boolSimpsExt.LET_ss, boolSimpsExt.literal_case_ss,
     boolSimpsExt.DNF_ss, boolSimpsExt.EQUIV_EXTRACT_ss]

  fun install_opaque ss (r : Traverse.reducer) : simpExtLib.simpset =
    simpExtLib.++ (ss,simpExtLib.dproc_ss (TraverseExt.lift r))
  fun install_configured ss (r : TraverseExt.reducer_config_data) =
    simpExtLib.++ (ss,simpExtLib.dproc_ss (TraverseExt.CONFIG_REDUCER r))
  fun default_data ss : TraverseExt.traverse_data =
    simpExtLib.traversedata_for_ss ss
  fun configured_data ss : TraverseExt.xtraverse_data =
    simpExtLib.xtraversedata_for_ss ss
  fun default_conv ss facts = TraverseExt.TRAVERSE (default_data ss) facts
  fun configured_conv ss facts =
    TraverseExt.XTRAVERSE (configured_data ss) facts

  (* Factory inputs are immutable declarations, not ordinary fragments. *)
  fun ac th1 th2 : simpExtLib.ssfrag = simpExtLib.ac_ss [(th1,th2)]
  fun type_recipe ty : simpExtLib.ssfrag = simpExtLib.type_ssfrag ty
  fun type_info_recipe info : simpExtLib.ssfrag = simpExtLib.tyi_to_ssdata info
  fun relational_recipe (data : simpExtLib.relsimpdata) =
    simpExtLib.relsimp_ss data
  fun threaded_recipe ths : simpExtLib.ssfrag =
    simpExtLib.threaded_cong_ss ths

  (* Public ordinary congruence fragments admit explicit opaque lifting;
     compiled ordinary congsets do not. *)
  fun congruence_fragment (fragment : congLib.congsetfrag) =
    congExtLib.lift_fragment fragment
  fun congruence ss (fragment : congExtLib.congsetfrag) facts =
    congExtLib.CONGRUENCE_EQ_SIMP_CONV
      (congExtLib.mk_congset [fragment]) ss facts

  (* Explicit extension recipes and entry points: ordinary clients continue
     to use simpLib, boolSimps and Traverse without migration. *)
  val policy : TraverseExt.child_first_policy =
    TraverseExt.charge_only (fn () => ())
  val mode : simpExtLib.simp_mode = {safe = false}
  val global_config : simpExtLib.xsimptac_config =
    {base = {strip = true, elimvars = false, droptrues = true,
             oldestfirst = true},
     concl_in_fixpoint = true, imp_rebuild = false, imp_premises = true}

  val solver : TraverseExt.ssolver = simpExtLib.mk_tactic_solver
    ("assumption", Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC)
  val strategy : simpExtLib.ssfrag = simpExtLib.merge_ss
    [simpExtLib.safe_solver_ss solver,
     simpExtLib.looper_ss ("conjunction", fn _ => Tactic.CONJ_TAC)]
  val configured : simpExtLib.simpset =
    simpExtLib.set_cond_depth 2 (simpExtLib.++ (bools,strategy))

  fun explicit ss facts : Abbrev.tactic =
    simpExtLib.GEN_SIMP_TAC mode ss facts
  fun global ss facts : Abbrev.tactic =
    simpExtLib.GEN_GLOBAL_SIMP_TAC mode global_config ss facts
  fun child_first ss facts : Abbrev.conv =
    simpExtLib.SIMP_CONV_CHILD_FIRST policy ss facts
  fun child_first_tac ss facts : Abbrev.tactic =
    simpExtLib.GEN_SIMP_TAC_CHILD_FIRST policy mode ss facts
  fun child_first_global ss facts : Abbrev.tactic =
    simpExtLib.GEN_GLOBAL_SIMP_TAC_CHILD_FIRST
      policy mode global_config ss facts

  (* Non-global GEN binds supplied rules once across looper branches and
     recursive passes. Bounds qualify directives, not marker rewrites. The
     generic marker constructors/identity remain unchanged. *)
  fun nested_arguments split_rule ignored : Thm.thm list =
    [simpExtLib.Req0 (BoundedRewrites.Once
       (simpExtLib.SF (simpExtLib.name_ss "EXAMPLE_STRATEGY" strategy))),
     BoundedRewrites.Ntimes
       (simpExtLib.Req0 (simpExtLib.Split split_rule)) 2,
     BoundedRewrites.Once
       (simpExtLib.ExclX "looper:conjunction"),
     BoundedRewrites.Once (markerLib.IgnAsm ignored)]
  fun nested_strategy split_rule ignored : Abbrev.tactic =
    explicit bools (nested_arguments split_rule ignored)

  (* BOUND consumes a bundle already installed in this invocation. The
     bundle retains untagged solver facts: do not resupply them as rewrite
     arguments. Local marker replay preserves all installed controls. *)
  fun bound_global ss facts : Abbrev.tactic = let
    val (base,args) = simpExtLib.prepare_rewrite_arguments ss facts
    val bundle = simpExtLib.prepare_rewrite_bundle base args
    val invocation = simpExtLib.install_rewrite_bundle bundle [] base
  in
    simpExtLib.GEN_GLOBAL_SIMP_TAC_CHILD_FIRST_BOUND
      policy mode global_config invocation bundle []
  end

  (* Both global paths retain the assumption policy, including when it is
     nested beneath a bound; neither reinstalls a supplied bundle. *)
  fun without_assumptions ss facts =
    child_first_global ss (markerLib.NoAsms :: facts)
  fun bound_without_assumption ss facts ignored = let
    val (base,args) = simpExtLib.prepare_rewrite_arguments ss facts
    val bundle = simpExtLib.prepare_rewrite_bundle base args
    val invocation = simpExtLib.install_rewrite_bundle bundle [] base
  in
    simpExtLib.GEN_GLOBAL_SIMP_TAC_CHILD_FIRST_BOUND
      policy mode global_config invocation bundle
      [BoundedRewrites.Once (markerLib.IgnAsm ignored)]
  end

  fun prepare ss facts = let
    val (base,args) = simpExtLib.prepare_rewrite_arguments ss facts
    val bundle = simpExtLib.prepare_rewrite_bundle base args
    val rules : (Thm.thm * simpExtLib.rewrite_source list) list =
      simpExtLib.rewrite_bundle_rules bundle
    val installed = simpExtLib.install_rewrite_bundle bundle [] base
  in (installed,bundle,rules) end
end
