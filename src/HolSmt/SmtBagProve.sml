(* Copyright (c) 2026 The HOL4 contributors. *)

(* Solver-neutral checked replay support for Z3's Int-array bag encoding. *)

structure SmtBagProve :> SmtBagProve =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtBagProve"

  fun named thy names tm =
    Term.is_const tm andalso
    let val {Thy, Name, ...} = Term.dest_thy_const tm
    in Thy = thy andalso List.exists (Lib.equal Name) names end

  val mentions = SmtResource.contains

  fun is_bag_constant tm =
    named "bag"
      ["BAG_IN", "BAG_INN", "BAG_INSERT", "BAG_UNION", "BAG_DIFF", "BAG_MERGE",
       "BAG_INTER", "SUB_BAG", "EMPTY_BAG", "BAG_CARD", "BAG_FILTER",
       "BAG_CHOICE", "BAG_IMAGE", "BAG_EVERY", "ITBAG", "SET_OF_BAG",
       "BAG_OF_SET"] tm

  (* The proof parser turns Z3's [(_ map +) a b] into
     [\x. a x + b x].  Do not classify arbitrary Int-valued lambdas as bags:
     array and arithmetic lemmas use those too. *)
  fun is_int_count_lambda tm =
    Term.is_abs tm andalso
    let
      val (x, body) = Term.dest_abs tm
      val (head, args) = boolSyntax.strip_comb body
      fun selected_at_x array =
        let val (_, index) = Term.dest_comb array
        in Term.aconv index x end
    in
      Library.same_const intSyntax.plus_tm head andalso
      (case args of
         [left, right] => selected_at_x left andalso selected_at_x right
       | _ => false)
    end
    handle Feedback.HOL_ERR _ => false

  fun has_bag_encoding t =
    mentions is_bag_constant t orelse mentions is_int_count_lambda t

  fun has_native_bag_encoding t = mentions is_bag_constant t

  fun bag_const name = Term.prim_mk_const {Thy = "bag", Name = name}

  (* Each admitted bag head has its own count/pointwise characterization.
     In particular CARD, FILTER, IMAGE and ITBAG are not admitted merely
     because the recognizer can name them. *)
  val bag_fact_table = [
    ("BAG_IN", bag_const "BAG_IN",
      [bagTheory.BAG_IN, bagTheory.BAG_INN]),
    ("BAG_INN", bag_const "BAG_INN", [bagTheory.BAG_INN]),
    ("BAG_INSERT", bag_const "BAG_INSERT", [bagTheory.BAG_INSERT]),
    ("BAG_UNION", bag_const "BAG_UNION", [bagTheory.BAG_UNION]),
    ("BAG_DIFF", bag_const "BAG_DIFF", [bagTheory.BAG_DIFF]),
    ("BAG_MERGE", bag_const "BAG_MERGE", [bagTheory.BAG_MERGE]),
    ("BAG_INTER", bag_const "BAG_INTER", [bagTheory.BAG_INTER]),
    ("SUB_BAG", bag_const "SUB_BAG", [bagTheory.SUB_BAG]),
    ("EMPTY_BAG", bag_const "EMPTY_BAG", [bagTheory.EMPTY_BAG]),
    ("BAG_CARD", bag_const "BAG_CARD",
      [bagTheory.BAG_CARD_THM, bagTheory.BAG_CARD_EMPTY,
       bagTheory.BAG_CARD_UNION, bagTheory.BAG_CARD_DIFF,
       bagTheory.BAG_CARD_BAG_INN]),
    ("BAG_FILTER", bag_const "BAG_FILTER",
      [bagTheory.BAG_FILTER_DEF, bagTheory.BAG_INN_BAG_FILTER,
       bagTheory.BAG_IN_BAG_FILTER]),
    ("BAG_IMAGE", bag_const "BAG_IMAGE",
      [bagTheory.BAG_IMAGE_DEF, bagTheory.BAG_IN_FINITE_BAG_IMAGE]),
    ("ITBAG", bag_const "ITBAG",
      [bagTheory.ITBAG_THM, bagTheory.ITBAG_EMPTY, bagTheory.ITBAG_INSERT]),
    ("BAG_CHOICE", bag_const "BAG_CHOICE", [bagTheory.BAG_CHOICE_DEF]),
    ("BAG_EVERY", bag_const "BAG_EVERY", [bagTheory.BAG_EVERY_THM]),
    ("SET_OF_BAG", bag_const "SET_OF_BAG", [bagTheory.SET_OF_BAG]),
    ("BAG_OF_SET", bag_const "BAG_OF_SET", [bagTheory.BAG_OF_SET])
  ]

  val supported_bag_operator_names_for_test =
    List.map (fn (name, _, _) => name) bag_fact_table

  fun bag_rewrites_for t =
    Library.goal_directed_rewrites bag_fact_table t @
    [integerTheory.INT_GE,
     integerTheory.INT_OF_NUM,
     integerTheory.NUM_OF_INT,
     integerTheory.INT_LE,
     integerTheory.INT_OF_NUM_LE,
     integerTheory.INT_OF_NUM_LT,
     integerTheory.INT_OF_NUM_ADD,
     combinTheory.UPDATE_def,
     combinTheory.APPLY_UPDATE_THM,
     boolTheory.FUN_EQ_THM]

  fun simp_prove t =
    simpLib.SIMP_PROVE (simpLib.++ (bossLib.srw_ss(), intSimps.INT_RWTS_ss))
      (bag_rewrites_for t) t

  fun pointwise_prove t =
    SmtResource.with_resource_step_time "Bag" "bag-condition-splitting"
      (fn t => Tactical.prove (t,
        let val rewrites = bag_rewrites_for t in
        Tactical.THEN (bossLib.RW_TAC
          (simpLib.++ (bossLib.srw_ss(), intSimps.INT_RWTS_ss)) rewrites,
          Tactical.THEN (Tactical.REPEAT boolLib.COND_CASES_TAC,
            Tactical.THEN
              (bossLib.FULL_SIMP_TAC
                (simpLib.++ (bossLib.srw_ss(), intSimps.INT_RWTS_ss))
                rewrites,
               intLib.ARITH_TAC))) end)) t

  fun unsupported t =
    raise ERR "bag_prove"
      ("unsupported bag encoding shape; checked replay handles native " ^
       "bag count characterizations and Z3 (_ map +) Int-array " ^
       "normalization; conclusion=" ^ Library.term_to_string t)

  fun bag_prove_with_arith_unbounded arith_prove t =
    if not (has_bag_encoding t) then
      unsupported t
    else
      simp_prove t
      handle Feedback.HOL_ERR holerr =>
        if SmtResource.is_resource_gate holerr then
          raise Feedback.HOL_ERR holerr
        else pointwise_prove t
      handle Feedback.HOL_ERR holerr =>
        if SmtResource.is_resource_gate holerr then
          raise Feedback.HOL_ERR holerr
        else arith_prove t
      handle Feedback.HOL_ERR holerr =>
        if SmtResource.is_resource_gate holerr then
          raise Feedback.HOL_ERR holerr
        else unsupported t

  fun bag_prove_with_arith arith_prove t =
    if not (has_bag_encoding t) then
      unsupported t
    else
      SmtResource.with_resource_step_time "Bag" "bag-replay"
        (fn t =>
          (SmtResource.check_resource_goal "Bag" "bag-replay" t;
           bag_prove_with_arith_unbounded arith_prove t)) t

  fun bag_prove t = bag_prove_with_arith intLib.ARITH_PROVE t

end
