(* Copyright (c) 2026 The HOL4 contributors. *)

(* Solver-neutral checked replay support for Z3's Int-array bag encoding. *)

structure SmtBagProve :> SmtBagProve =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtBagProve"

  fun named thy names tm =
    Term.is_const tm andalso
    let val {Thy, Name, ...} = Term.dest_thy_const tm
    in Thy = thy andalso List.exists (Lib.equal Name) names end

  (* Classification keeps the ordinary non-family bypass. Before either
     the predicate or the shared DAG walker opens a binder, admit its full
     annotation under the existing primitive-Type allowance. This is local
     syntax policy, not a process-wide admission hook. *)
  fun mentions predicate root =
    let
      exception Found
      val maximum = SmtResource.max_bv_replay_term_nodes
      val check_type = SmtReplayArithmetic.new_type_check (fn () => ())
      fun children tm = if not (Term.is_abs tm) then
          SmtResource.term_children tm
        else
          (case SmtReplayImport.bounded_raw_size_with_type_check
              check_type maximum tm of
             NONE =>
               (SmtResource.check_term_size_for "BitVector" "binder-opening"
                  (maximum+1);[])
           | SOME _ =>
               [#2 (SmtReplayImport.dest_abs_preserving_names tm)])
      fun inspect tm =
        (if Term.is_abs tm then check_type (Term.type_of tm) else ();
         if predicate tm then raise Found else ())
      fun search () =
        (let val summary = SmtResource.bounded_structure_with_children
               children inspect maximum root
             val _ = if #complete summary then () else
               SmtResource.check_dag_size_with_limit "Skeleton"
                 "theory-classification" maximum (#dag_nodes summary)
         in false end) handle Found => true
    in search () end

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
      (* Recognition is not authority to open an unbounded native binder.
         Use the existing public resource metric and primitive-Type gate. *)
      val check_type = SmtReplayArithmetic.new_type_check (fn () => ())
      val _ = case SmtReplayImport.bounded_raw_size_with_type_check
          check_type SmtResource.max_bv_replay_term_nodes tm of
          SOME _ => ()
        | NONE => SmtResource.check_term_size_for "BitVector" "binder-opening"
            (SmtResource.max_bv_replay_term_nodes+1)
      val (x, body) = SmtReplayImport.dest_abs_preserving_names tm
      val (head, args) = boolSyntax.strip_comb body
      fun selected_at_x array =
        let val (_, index) = Term.dest_comb array
            val _ = check_type (Term.type_of index)
        in Term.aconv index x end
    in
      Library.same_const intSyntax.plus_tm head andalso
      (case args of
         [left, right] => selected_at_x left andalso selected_at_x right
       | _ => false)
    end
    handle Feedback.HOL_ERR detail =>
      if SmtResource.is_resource_gate detail then raise Feedback.HOL_ERR detail
      else false

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
     (* srw's set-membership conversion, expressed as its checked equation. *)
     boolTheory.IN_DEF,
     boolTheory.FUN_EQ_THM]

  (* Preserve the bag portfolio and its constructor/count equations. Only
     free graph variables may be named by the caller: counts, elements and
     guards are not independent holes. Admission is invocation-local, and
     failures must survive both tactic and consumer fallback handlers. *)
  fun checked_procedures check =
  let
    exception AdmissionFailure of exn
    fun admit tm = check tm handle primary => raise AdmissionFailure primary
    fun protect f x = f x handle AdmissionFailure primary =>
      SmtReplayArithmetic.propagate_admission_error primary
    fun goal tactic (assumptions,conclusion) =
      (List.app admit (conclusion::assumptions);
       tactic (assumptions,conclusion))
    fun cases input = goal (fn input as (_,conclusion) =>
      let
        val _ = HolKernel.find_term (fn tm => boolSyntax.is_cond tm andalso
          not (Term.is_const (#1 (boolSyntax.dest_cond tm)))) conclusion
        (* COND_CASES_TAC instantiates these fixed schemas at the admitted
           conditional's result type before splitting the bounded goal. *)
        val _ = admit (Thm.concl boolTheory.COND_CLAUSES)
        val _ = admit (Thm.concl boolTheory.EXCLUDED_MIDDLE)
      in Tactic.COND_CASES_TAC input end) input
    fun with_rewrites facts prove =
      SmtDatatypeProve.with_checked_rewrites admit
        (fn () => simpLib.++
          (simpLib.++ (bossLib.srw_ss(),intSimps.INT_RWTS_ss),
           simpLib.rewrites facts)) prove
    fun simp_prove t =
      (admit t;with_rewrites (bag_rewrites_for t)
        (fn ss => simpLib.SIMP_PROVE ss [] t))
    fun pointwise_prove t =
      SmtResource.with_resource_step_time "Bag" "bag-condition-splitting"
        (fn t =>
          (admit t;with_rewrites (bag_rewrites_for t) (fn ss =>
            Tactical.prove (t,
              Tactical.THEN (goal (simpLib.SIMP_TAC ss []),
                Tactical.THEN (Tactical.REPEAT (goal Tactic.STRIP_TAC),
                  Tactical.THEN
                    (Tactical.REPEAT (Tactical.THEN
                       (cases,
                        goal (simpLib.FULL_SIMP_TAC ss []))),
                     Tactical.THEN (goal (simpLib.FULL_SIMP_TAC ss []),
                       goal intLib.ARITH_TAC)))))))) t
    (* CPC's scoped fallback deliberately uses its old srw portfolio, not
       extra bag equations. Admit every actual Hyp and generated branch. *)
    fun contextual (context,t) =
      SmtResource.with_resource_step_time "Bag" "contextual" (fn () =>
        (List.app admit (t::context);
         SmtResource.check_resource_goal "Bag" "contextual" t;
         SmtDatatypeProve.with_checked_rewrites admit bossLib.srw_ss
           (fn ss => Tactical.TAC_PROOF ((context,t),
             Tactical.THEN (Tactical.REPEAT cases,
               Tactical.THEN (goal (bossLib.FULL_SIMP_TAC ss []),
                 goal intLib.ARITH_TAC)))))) ()

    fun unsupported t =
      raise ERR "bag_prove"
        ("unsupported bag encoding shape; checked replay handles native " ^
         "bag count characterizations and Z3 (_ map +) Int-array " ^
         "normalization; conclusion=" ^ Library.term_to_string t)

    fun bag_prove_with_arith_unbounded arith_prove t =
      if not (has_bag_encoding t) then unsupported t
      else
        simp_prove t
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else pointwise_prove t
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else (admit t;arith_prove t)
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else unsupported t

    fun bag_prove_with_arith arith_prove t =
      if not (has_bag_encoding t) then unsupported t
      else
        SmtResource.with_resource_step_time "Bag" "bag-replay"
          (fn t =>
            (SmtResource.check_resource_goal "Bag" "bag-replay" t;
             bag_prove_with_arith_unbounded arith_prove t)) t

  in
    {prove=fn arith => protect (bag_prove_with_arith arith),
     contextual=protect contextual}
  end

  fun default_admission () = SmtReplayArithmetic.new_term_check
    {limit=SmtResource.max_bv_replay_term_nodes,observe=fn () => ()}
  fun bag_prove_with_admission admit arith =
    #prove (checked_procedures admit) arith
  fun bag_contextual_prove_with_admission admit context t =
    #contextual (checked_procedures admit) (context,t)
  fun bag_prove_with_arith arith t =
    bag_prove_with_admission (default_admission ()) arith t
  fun bag_prove t = bag_prove_with_arith intLib.ARITH_PROVE t

end
