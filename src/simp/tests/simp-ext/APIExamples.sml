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

  fun prepare ss facts = let
    val (base,args) = simpExtLib.prepare_rewrite_arguments ss facts
    val bundle = simpExtLib.prepare_rewrite_bundle base args
    val rules : (Thm.thm * simpExtLib.rewrite_source list) list =
      simpExtLib.rewrite_bundle_rules bundle
    val installed = simpExtLib.install_rewrite_bundle bundle [] base
  in (installed,bundle,rules) end
end
