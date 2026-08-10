(* Copyright (c) 2026 The HOL4 contributors. *)

(* Solver-neutral checked replay support for Z3's Int-array bag encoding. *)

structure SmtBagProve :> SmtBagProve =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtBagProve"

  fun named thy names tm =
    Term.is_const tm andalso
    let val {Thy, Name, ...} = Term.dest_thy_const tm
    in Thy = thy andalso List.exists (Lib.equal Name) names end

  fun mentions pred t = Lib.can (HolKernel.find_term pred) t

  fun is_bag_constant tm =
    named "bag"
      ["BAG_IN", "BAG_INSERT", "BAG_UNION", "BAG_DIFF", "BAG_MERGE",
       "BAG_INTER", "SUB_BAG", "EMPTY_BAG", "BAG_CARD", "BAG_FILTER",
       "BAG_CHOICE", "BAG_IMAGE", "BAG_EVERY", "ITBAG", "SET_OF_BAG",
       "BAG_OF_SET"] tm

  (* The proof parser turns Z3's [(_ map +) a b] into
     [\x. a x + b x].  Do not classify arbitrary Int-valued lambdas as bags:
     array and arithmetic lemmas use those too. *)
  fun is_int_count_lambda tm =
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

  val bag_rewrites = [
    bagTheory.BAG_UNION,
    bagTheory.BAG_DIFF,
    bagTheory.BAG_MERGE,
    bagTheory.BAG_INTER,
    bagTheory.BAG_INSERT,
    bagTheory.BAG_IN,
    bagTheory.SUB_BAG,
    combinTheory.UPDATE_def,
    combinTheory.APPLY_UPDATE_THM,
    boolTheory.FUN_EQ_THM
  ]

  fun simp_prove t =
    simpLib.SIMP_PROVE (simpLib.++ (bossLib.srw_ss(), intSimps.INT_RWTS_ss))
      bag_rewrites t

  fun pointwise_prove t =
    SmtResource.with_bitblast_step_time "bag-condition-splitting"
      (fn t => Tactical.prove (t,
        Tactical.THEN (bossLib.RW_TAC
          (simpLib.++ (bossLib.srw_ss(), intSimps.INT_RWTS_ss)) bag_rewrites,
          Tactical.THEN (Tactical.REPEAT boolLib.COND_CASES_TAC,
            bossLib.RW_TAC
              (simpLib.++ (bossLib.srw_ss(), intSimps.INT_RWTS_ss))
              bag_rewrites)))) t

  fun unsupported t =
    raise ERR "bag_prove"
      ("unsupported bag encoding shape; checked replay handles native " ^
       "bag count characterizations and Z3 (_ map +) Int-array " ^
       "normalization; conclusion=" ^ Library.term_to_string t)

  fun bag_prove_with_arith arith_prove t =
    if not (has_bag_encoding t) then
      unsupported t
    else
      simp_prove t
      handle Feedback.HOL_ERR _ =>
      pointwise_prove t
      handle Feedback.HOL_ERR _ =>
      arith_prove t
      handle Feedback.HOL_ERR holerr =>
        if SmtResource.is_resource_gate holerr then
          raise Feedback.HOL_ERR holerr
        else
          unsupported t

  fun bag_prove t = bag_prove_with_arith intLib.ARITH_PROVE t

end
