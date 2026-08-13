(* Copyright (c) 2026 The HOL4 contributors. *)

(* Solver-neutral checked replay support for genuine SMT-LIB Seq lemmas. *)

structure SmtSeqProve :> SmtSeqProve =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtSeqProve"

  fun is_smtstr_value tm =
    case boolSyntax.strip_comb tm of
      (head, [_]) =>
        Term.is_const head andalso
        let val {Thy, Name, ...} = Term.dest_thy_const head
        in Thy = "smtstring" andalso Name = "SmtStr" end
    | _ => false

  fun list_element_type tm =
    Lib.total listSyntax.dest_list_type (Term.type_of tm)

  (* String remains on SmtStringProve's carrier.  A list type alone is not
     Seq provenance: ArrayEx lowering can contain list-typed implementation
     artefacts.  Require a sequence operation as well. *)
  fun has_seq_type t =
    let
      fun sequence_head tm =
        Term.is_const tm andalso
        let val {Thy, Name, ...} = Term.dest_thy_const tm in
          (Thy = "list" andalso List.exists (Lib.equal Name)
            ["APPEND", "LENGTH", "CONS", "NIL", "TAKE", "DROP", "EL",
             "MAP", "FOLDL", "REVERSE", "isPREFIX", "LUPDATE"])
          orelse (Thy = "rich_list" andalso
            List.exists (Lib.equal Name) ["IS_SUBLIST", "IS_SUFFIX"])
          orelse (Thy = "HolSmt" andalso
            List.exists (Lib.equal Name)
              ["smt_seq_nth", "smt_seq_extract", "smt_seq_at",
               "smt_seq_indexof", "smt_seq_replace", "smt_seq_replace_all",
               "smt_seq_update"])
        end
      fun visit tm =
        if is_smtstr_value tm then false
        else if sequence_head tm then true
        else
          (let val (rator, rand) = Term.dest_comb tm
           in visit rator orelse visit rand end
           handle Feedback.HOL_ERR _ =>
             (let val (_, body) = Term.dest_abs tm
              in visit body end
              handle Feedback.HOL_ERR _ => false))
    in
      visit t
    end

  val metis_limit : mlibMeter.limit = {time = SOME 1.0, infs = SOME 5000}
  fun with_metis_limit f = Lib.with_flag (metisTools.limit, metis_limit) f

  val list_rewrites = [
    listTheory.APPEND,
    listTheory.APPEND_ASSOC,
    listTheory.APPEND_11,
    listTheory.APPEND_eq_NIL,
    listTheory.CONS_11,
    listTheory.LENGTH_APPEND,
    integerTheory.INT_OF_NUM_ADD,
    listTheory.LENGTH_EQ_0,
    listTheory.LENGTH_EQ_1,
    listTheory.NOT_CONS_NIL,
    listTheory.EL,
    listTheory.MAP_APPEND,
    rich_listTheory.FOLDL_APPEND,
    integerTheory.INT_ADD_COMM,
    HolSmtTheory.smt_seq_nth_def,
    HolSmtTheory.smt_seq_extract_def,
    HolSmtTheory.smt_seq_at_def
  ]

  val seq_ss = simpLib.++ (bossLib.srw_ss(), intSimps.INT_RWTS_ss)

  fun simp_prove_with rewrites t =
    let
      val normalized = simpLib.SIMP_CONV seq_ss rewrites t
        handle Conv.UNCHANGED =>
          raise ERR "simp_prove_with" "no rewrite applies to this rung"
      val t' = boolSyntax.rhs (Thm.concl normalized)
      val thm = tautLib.TAUT_PROVE t'
        handle Feedback.HOL_ERR _ => intLib.ARITH_PROVE t'
    in
      Thm.EQ_MP (Thm.SYM normalized) thm
    end

  fun simp_prove t = simp_prove_with list_rewrites t

  fun named thy names tm =
    Term.is_const tm andalso
    let val {Thy, Name, ...} = Term.dest_thy_const tm
    in Thy = thy andalso List.exists (Lib.equal Name) names end

  fun mentions pred t = Lib.can (HolKernel.find_term pred) t

  fun is_append tm = named "list" ["APPEND"] tm
  fun is_length tm = named "list" ["LENGTH"] tm
  fun is_cons_or_nil tm = named "list" ["CONS", "NIL"] tm
  fun is_access tm =
    named "HolSmt" ["smt_seq_nth", "smt_seq_extract", "smt_seq_at"] tm
    orelse named "list" ["TAKE", "DROP", "EL"] tm

  (* Z3's native Seq certificate uses its internal `seq.eq` and `seq.tail`
     witnesses for this list fact.  The parser reconstructs them as equality
     and DROP, so one generic theorem handles all element types. *)
  val head_tail_thm = Tactical.prove
    (``(&(LENGTH (s : 'a list)):int) = 0 \/
        s = [EL 0 s] ++ DROP 1 s``,
     Tactical.THEN (bossLib.Cases_on `s`,
       bossLib.RW_TAC (bossLib.srw_ss()) []))

  val head_tail_zero_thm = Tactical.prove
    (``0 = (&(LENGTH (s : 'a list)):int) \/
        s = [EL 0 s] ++ DROP 1 s``,
     bossLib.METIS_TAC [head_tail_thm])

  val head_tail_zero_add_thm = Tactical.prove
    (``0 = (&(LENGTH (s : 'a list)):int) \/
        s = [EL 0 s] ++ DROP (0 + 1) s``,
     Tactical.THEN (bossLib.Cases_on `s`,
       bossLib.RW_TAC (bossLib.srw_ss()) [listTheory.EL, listTheory.HD]))

  val nth_of_unit_thm = Tactical.prove
    (``[x] = (s : 'a list) ==> EL 0 s = x``,
     bossLib.METIS_TAC [listTheory.EL, listTheory.HD])

  fun nth_decomposition_prove t =
    if mentions is_access t then
      with_metis_limit (fn () => metisLib.METIS_PROVE
        [head_tail_thm, head_tail_zero_thm, head_tail_zero_add_thm,
         nth_of_unit_thm] t) ()
      handle Feedback.HOL_ERR _ =>
        let
          val normalized = simpLib.SIMP_CONV seq_ss list_rewrites t
            handle Conv.UNCHANGED =>
              raise ERR "nth_decomposition_prove"
                "normalization did not change the conclusion"
          val target = boolSyntax.rhs (Thm.concl normalized)
          val thm = with_metis_limit (fn () => metisLib.METIS_PROVE
            [head_tail_thm, head_tail_zero_thm, head_tail_zero_add_thm,
             nth_of_unit_thm] target) ()
        in
          Thm.EQ_MP (Thm.SYM normalized) thm
        end
    else
      raise ERR "nth_decomposition_prove" "not a Seq nth decomposition"

  fun is_prefix_suffix_contains tm =
    named "rich_list" ["IS_SUBLIST", "IS_SUFFIX"] tm orelse
    named "list" ["isPREFIX"] tm

  fun is_indexof_replace tm =
    named "HolSmt"
      ["smt_seq_indexof", "smt_seq_replace", "smt_seq_replace_all"] tm

  fun is_update_reverse tm =
    named "HolSmt" ["smt_seq_update"] tm orelse
    named "list" ["REVERSE", "LUPDATE"] tm

  (* Keep recursive unfolding off the core ladder: these rungs run only after
     recognising their operator, and use the constructor equations exposed by
     the native list model.  This makes symbolic residue fail loudly instead
     of accidentally expanding without a structural bound. *)
  (* Keep the append witness explicit.  Unfolding IS_SUBLIST_APPEND first
     leaves an existential that neither simplification nor tautology chooses. *)
  val contains_append_left_thm = Tactical.prove
    (``IS_SUBLIST ((xs : 'a list) ++ ys) xs``,
     Tactical.THEN
       (bossLib.RW_TAC (bossLib.srw_ss()) [rich_listTheory.IS_SUBLIST_APPEND],
        Tactical.THEN (Tactic.EXISTS_TAC ``[] : 'a list``,
          Tactical.THEN (Tactic.EXISTS_TAC ``ys : 'a list``,
            bossLib.RW_TAC (bossLib.srw_ss()) [listTheory.APPEND]))))

  val contains_append_right_thm = Tactical.prove
    (``IS_SUBLIST ((xs : 'a list) ++ ys) ys``,
     Tactical.THEN
       (bossLib.RW_TAC (bossLib.srw_ss()) [rich_listTheory.IS_SUBLIST_APPEND],
        Tactical.THEN (Tactic.EXISTS_TAC ``xs : 'a list``,
          Tactical.THEN (Tactic.EXISTS_TAC ``[] : 'a list``,
            bossLib.RW_TAC (bossLib.srw_ss()) [listTheory.APPEND]))))

  val prefix_suffix_contains_rewrites = list_rewrites @ [
    listTheory.isPREFIX_THM,
    rich_listTheory.IS_SUBLIST,
    rich_listTheory.IS_SUBLIST_APPEND,
    rich_listTheory.IS_SUFFIX,
    rich_listTheory.IS_SUFFIX_APPEND,
    rich_listTheory.IS_PREFIX_IS_SUBLIST,
    rich_listTheory.IS_PREFIX_REFL
  ]

  val indexof_replace_rewrites = list_rewrites @ [
    HolSmtTheory.smt_seq_indexof_def,
    HolSmtTheory.smt_seq_indexof_aux_def,
    HolSmtTheory.smt_seq_replace_def,
    HolSmtTheory.smt_seq_replace_raw_def,
    HolSmtTheory.smt_seq_replace_all_def,
    HolSmtTheory.smt_seq_replace_all_aux_def
  ]

  (* Recursive replacement is deliberately not a general simp rule.  It is
     nevertheless safe to compute a closed certificate conclusion. *)
  val replace_all_compset =
    computeLib.add_thms [HolSmtTheory.smt_seq_replace_all_def,
      HolSmtTheory.smt_seq_replace_all_aux_def]
      (computeLib.copy (computeLib.the_compset ()))

  fun ground_replace_all_prove t =
    if List.null (Term.free_vars t) then
      SmtResource.with_bitblast_step_time "seq-replace-all"
        (fn t => Drule.EQT_ELIM (computeLib.CBV_CONV replace_all_compset t)) t
    else
      raise ERR "ground_replace_all_prove" "replacement is not ground"

  val update_reverse_rewrites = list_rewrites @ [
    HolSmtTheory.smt_seq_update_def,
    integerTheory.INT_SUB,
    listTheory.LUPDATE_def,
    listTheory.REVERSE_DEF
  ]

  fun shape_of t =
    if mentions is_prefix_suffix_contains t then
      "prefix-suffix-contains"
    else if mentions is_indexof_replace t then
      "indexof-replace"
    else if mentions is_update_reverse t then
      "update-reverse"
    else if mentions is_append t orelse mentions is_length t then
      "concat-length"
    else if mentions is_access t then
      "extract-nth"
    else if mentions is_cons_or_nil t then
      "unit-empty"
    else
      "unrecognised"

  fun unsupported t =
    raise ERR "seq_prove"
      ("unsupported th-lemma shape: theory=seq; shape=" ^ shape_of t ^
       "; attempted rungs=[concat-length, unit-empty, extract-nth, " ^
       "prefix-suffix-contains, indexof-replace, update-reverse]; " ^
       "all rungs are bounded by the native list term structure; " ^
       "conclusion=" ^ Library.term_to_string t)

  fun concat_length_prove t =
    if mentions is_append t orelse mentions is_length t then simp_prove t
    else raise ERR "concat_length_prove" "not a concat/length shape"

  fun unit_empty_prove t =
    if mentions is_cons_or_nil t then simp_prove t
    else raise ERR "unit_empty_prove" "not a unit/empty shape"

  fun access_prove t =
    if mentions is_access t then simp_prove t
    else raise ERR "access_prove" "not an extract/nth shape"

  fun prefix_suffix_contains_prove t =
    if mentions is_prefix_suffix_contains t then
      with_metis_limit (fn () => metisLib.METIS_PROVE
        [contains_append_left_thm, contains_append_right_thm] t) ()
      handle Feedback.HOL_ERR _ =>
        simp_prove_with prefix_suffix_contains_rewrites t
    else
      raise ERR "prefix_suffix_contains_prove"
        "not a prefix/suffix/contains shape"

  fun indexof_replace_prove t =
    if mentions is_indexof_replace t then
      simp_prove_with indexof_replace_rewrites t
      handle Feedback.HOL_ERR _ => ground_replace_all_prove t
    else
      raise ERR "indexof_replace_prove" "not an indexof/replace shape"

  fun update_reverse_prove t =
    if mentions is_update_reverse t then
      simp_prove_with update_reverse_rewrites t
    else
      raise ERR "update_reverse_prove" "not an update/reverse shape"

  fun seq_contextual_prove context t =
    if has_seq_type t then
      SmtResource.with_bitblast_step_time "seq-contextual"
        (fn () => Tactical.TAC_PROOF ((context, t),
          bossLib.ASM_SIMP_TAC seq_ss list_rewrites)) ()
    else
      unsupported t

  fun seq_prove t =
    if not (has_seq_type t) then
      unsupported t
    else
      concat_length_prove t
      handle Feedback.HOL_ERR _ =>
      unit_empty_prove t
      handle Feedback.HOL_ERR _ =>
      access_prove t
      handle Feedback.HOL_ERR _ =>
      nth_decomposition_prove t
      handle Feedback.HOL_ERR _ =>
      prefix_suffix_contains_prove t
      handle Feedback.HOL_ERR _ =>
      indexof_replace_prove t
      handle Feedback.HOL_ERR _ =>
      update_reverse_prove t
      handle Feedback.HOL_ERR _ =>
      unsupported t

end
