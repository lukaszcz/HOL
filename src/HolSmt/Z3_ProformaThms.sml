(* Copyright (c) 2009-2010 Tjark Weber. All rights reserved. *)

(* Proforma theorems, used for Z3 proof reconstruction *)

structure Z3_ProformaThms =
struct

  val ERR = Feedback.mk_HOL_ERR "Z3_ProformaThms"

  (* The Unicode-string carrier bounds every code point, so string lemmas
     about literal characters carry a '<= 196607' antecedent.  'prove'
     matches on the conclusion and discharges hypotheses, so such a lemma
     would never match at all; move exactly those antecedents into the
     sequent, where the ground instance discharges by simplification.  Any
     other antecedent is left alone: it is part of what the net matches. *)
  local
    val max_code_point = Arbnum.fromInt 196607

    fun is_code_point_bound tm =
      case Lib.total boolSyntax.dest_conj tm of
        SOME (left, right) =>
          is_code_point_bound left andalso is_code_point_bound right
      | NONE =>
          (case Lib.total numSyntax.dest_leq tm of
             SOME (_, bound) =>
               (case Lib.total numSyntax.dest_numeral bound of
                  SOME value => Arbnum.compare (value, max_code_point) = EQUAL
                | NONE => false)
           | NONE => false)
  in
    (* '|- bound /\ rest ==> concl'  becomes  'bound |- rest ==> concl', so
       the surviving implication is what the net matches. *)
    fun split_leading_bound th antecedent =
      case Lib.total boolSyntax.dest_conj antecedent of
        SOME (bound, rest) =>
          if is_code_point_bound bound then
            SOME (Thm.DISCH rest
              (Drule.PROVE_HYP
                (Thm.CONJ (Thm.ASSUME bound) (Thm.ASSUME rest))
                (Drule.UNDISCH th)))
          else NONE
      | NONE => NONE

    fun undisch_code_point_bounds th =
      case Lib.total boolSyntax.dest_imp (Thm.concl th) of
        SOME (antecedent, _) =>
          if is_code_point_bound antecedent then
            undisch_code_point_bounds (Drule.UNDISCH th)
          else
            (case split_leading_bound th antecedent of
               SOME split => undisch_code_point_bounds split
             | NONE => th)
      | NONE => th
  end

  (* Both forms are indexed: the original still matches a goal that carries
     the bound as its own antecedent, while the undischarged form matches a
     goal shaped like the bare conclusion. *)
  fun thm_forms th =
    let val undisched = undisch_code_point_bounds th
    in
      if Term.aconv (Thm.concl undisched) (Thm.concl th) then [th]
      else [th, undisched]
    end

  fun thm_net_from_list thms =
    let
      fun insert (th, net) = Net.insert (Thm.concl th, th) net
    in
      List.foldl insert Net.empty (List.concat (List.map thm_forms thms))
    end

  val array_thm_list = [
    Library.prove
      (``((i =+ e) a) i = e``,
        bossLib.RW_TAC (bossLib.srw_ss()) [combinTheory.APPLY_UPDATE_THM]),
    Library.prove
      (``i <> j ==> ((i =+ e) a) j = a j``,
        bossLib.RW_TAC (bossLib.srw_ss()) [combinTheory.APPLY_UPDATE_THM]),
    Library.prove
      (``(i =+ f) ((i =+ e) a) = (i =+ f) a``,
        bossLib.RW_TAC (bossLib.srw_ss()) [
          boolTheory.FUN_EQ_THM,
          combinTheory.APPLY_UPDATE_THM
        ]),
    Library.prove
      (``i <> j ==>
          (j =+ f) ((i =+ e) a) = (i =+ e) ((j =+ f) a)``,
        Tactical.THEN (bossLib.RW_TAC (bossLib.srw_ss()) [
            boolTheory.FUN_EQ_THM,
            combinTheory.APPLY_UPDATE_THM
          ], bossLib.METIS_TAC [])),
    Library.prove
      (``i <> j ==> ((j =+ f) ((i =+ e) a)) i = e``,
        bossLib.RW_TAC (bossLib.srw_ss()) [combinTheory.APPLY_UPDATE_THM]),
    Library.prove
      (``i <> j ==> ((j =+ f) ((i =+ e) a)) j = f``,
        bossLib.RW_TAC (bossLib.srw_ss()) [combinTheory.APPLY_UPDATE_THM]),
    Library.prove
      (``(!i. a i = b i) ==> (a = b)``,
        bossLib.RW_TAC (bossLib.srw_ss()) [boolTheory.FUN_EQ_THM]),
    Library.prove
      (``(a = b) <=> (!i. a i = b i)``,
        bossLib.RW_TAC (bossLib.srw_ss()) [boolTheory.FUN_EQ_THM])
  ]

  (* Z3 encodes sets as Bool-valued arrays.  The proof parser restores the
     D13 carrier 'a -> bool, so the pointwise pred_set facts below are the
     checked counterparts of Z3's map/select and constant-array shapes.
     These are precisely the operations recorded in the Phase-6 Z3 corpus. *)
  val set_thm_list = [
    pred_setTheory.IN_UNION,
    pred_setTheory.IN_INTER,
    pred_setTheory.IN_DIFF,
    pred_setTheory.IN_COMPL,
    pred_setTheory.SUBSET_DEF,
    pred_setTheory.EXTENSION,
    (* Z3's array-set subset rewrite is [a SUBSET b =
       ((\x. a x /\ ~b x) = EMPTY)].  It is the recorded map-and/map-not
       lowering, not a guessed alternative Set encoding. *)
    Library.prove
      (``((s:'a set) SUBSET t) =
          ((\x. x IN s /\ x NOTIN t) = (EMPTY:'a set))``,
       Tactical.THEN (bossLib.RW_TAC (bossLib.srw_ss())
         [pred_setTheory.SUBSET_DEF, pred_setTheory.EXTENSION],
         bossLib.METIS_TAC [])),
    (* A store pushed through Z3's Boolean map-not. *)
    Library.prove
      (``(\x. ~((i =+ v) (s:'a set)) x) =
          (i =+ ~v) (\x. ~s x)``,
       Tactical.THEN (bossLib.RW_TAC (bossLib.srw_ss())
         [boolTheory.FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM],
         Tactical.THEN (Tactical.REPEAT boolLib.COND_CASES_TAC,
           bossLib.RW_TAC (bossLib.srw_ss()) []))),
    Library.prove
      (``(!x:'a. x IN s <=> x IN t) ==> (s = t)``,
       bossLib.RW_TAC (bossLib.srw_ss()) [pred_setTheory.EXTENSION]),
    Library.prove
      (``F = ((x:'a) IN (EMPTY:'a set))``,
       bossLib.RW_TAC (bossLib.srw_ss()) [pred_setTheory.NOT_IN_EMPTY]),
    Library.prove
      (``((x:'a) IN (UNIV:'a set)) = T``,
       bossLib.RW_TAC (bossLib.srw_ss()) [pred_setTheory.IN_UNIV])
  ]

  (* Floating-point rewrite seed.  The literal facts are stored with their
     side conditions in the sequent: the net first matches the concrete
     triple printed by Z3, then [prove] discharges its numeral conditions.
     Each group names its Phase-5 proof-corpus case(s). *)
  local
    open smtfloatTheory

    val literal_normalization_thms =
      List.map Drule.UNDISCH
        [smtfloatTheory.smtfp_bits_pzero,
         smtfloatTheory.smtfp_pzero_bits,
         smtfloatTheory.smtfp_bits_nzero,
         smtfloatTheory.smtfp_nzero_bits,
         smtfloatTheory.smtfp_bits_pinf,
         smtfloatTheory.smtfp_pinf_bits,
         smtfloatTheory.smtfp_bits_ninf,
         smtfloatTheory.smtfp_ninf_bits,
         smtfloatTheory.smtfp_bits_nan,
         smtfloatTheory.smtfp_nan_bits]

    val rounding_distinct_thms =
      Drule.CONJUNCTS smtfloatTheory.smt_rounding_distinctness
  in
    val fp_thm_list =
      (* literal_positive/negative_zero, literal_positive/negative_infinity,
         literal_nan, and nan_payload_equality *)
      literal_normalization_thms @
      (* symbolic_classification_nan_positive and the arbitrary-format
         classification probes' abs normalization *)
      [smtfloatTheory.smtfp_is_nan_bits,
       smtfloatTheory.smtfp_abs_bits,
       smtfloatTheory.smtfp_neg_neg,
       smtfloatTheory.smtfp_abs_abs,
       smtfloatTheory.smtfp_abs_neg] @
      (* Ground rewrites use reflexivity; symbolic comparisons contain
         equality/symmetry transport and an fp.eq atom. *)
      [smtfloatTheory.smtfp_equality_refl,
       smtfloatTheory.smtfp_equality_symm,
       smtfloatTheory.smtfp_eq_refl,
       smtfloatTheory.smtfp_eq_of_equality,
       smtfloatTheory.smtfp_eq_signed_zero] @
      (* ground_add/ground_div and conversions print RNE/RNA/RTZ literals;
         constructor distinctness and exhaustion are their enum boundary. *)
      [smtfloatTheory.smt_rounding_refl,
       Drule.SPEC_ALL smtfloatTheory.smt_rounding_cases] @
      rounding_distinct_thms

    val fp_thms = thm_net_from_list fp_thm_list
  end

local
  open HolSmtTheory
in
  val def_axiom_thms = thm_net_from_list
    [HolSmtTheory.d001, HolSmtTheory.d002, HolSmtTheory.d003,
     HolSmtTheory.d004, HolSmtTheory.d005, HolSmtTheory.d006,
     HolSmtTheory.d007, HolSmtTheory.d008, HolSmtTheory.d009,
     HolSmtTheory.d010, HolSmtTheory.d011, HolSmtTheory.d012,
     HolSmtTheory.d013, HolSmtTheory.d014, HolSmtTheory.d015,
     HolSmtTheory.d016, HolSmtTheory.d017, HolSmtTheory.d018,
     HolSmtTheory.d019, HolSmtTheory.d020, HolSmtTheory.d021,
     HolSmtTheory.d022, HolSmtTheory.d023, HolSmtTheory.d024,
     HolSmtTheory.d025, HolSmtTheory.d026, HolSmtTheory.d027,
     HolSmtTheory.d028]

  val rewrite_thm_list =
    [HolSmtTheory.r001, HolSmtTheory.r002, HolSmtTheory.r003,
     HolSmtTheory.r004, HolSmtTheory.r005, HolSmtTheory.r006,
     HolSmtTheory.r007, HolSmtTheory.r008, HolSmtTheory.r009,
     HolSmtTheory.r010, HolSmtTheory.r011, HolSmtTheory.r012,
     HolSmtTheory.r014, HolSmtTheory.r015, HolSmtTheory.r016,
     HolSmtTheory.r017, HolSmtTheory.r018, HolSmtTheory.r019,
     HolSmtTheory.r020, HolSmtTheory.r022, HolSmtTheory.r024,
     HolSmtTheory.r026, HolSmtTheory.r027, HolSmtTheory.r028,
     HolSmtTheory.r029, HolSmtTheory.r031, HolSmtTheory.r032,
     HolSmtTheory.r037, HolSmtTheory.r038, HolSmtTheory.r039,
     HolSmtTheory.r040, HolSmtTheory.r041, HolSmtTheory.r042,
     HolSmtTheory.r043, HolSmtTheory.r044, HolSmtTheory.r045,
     HolSmtTheory.r046, HolSmtTheory.r047, HolSmtTheory.r048,
     HolSmtTheory.r049, HolSmtTheory.r050, HolSmtTheory.r051,
     HolSmtTheory.r052, HolSmtTheory.r053, HolSmtTheory.r054,
     HolSmtTheory.r055, HolSmtTheory.r056, HolSmtTheory.r057,
     HolSmtTheory.r058, HolSmtTheory.r059, HolSmtTheory.r060,
     HolSmtTheory.r061, HolSmtTheory.r062, HolSmtTheory.r067,
     HolSmtTheory.r068, HolSmtTheory.r219, HolSmtTheory.r220,
     HolSmtTheory.r221, HolSmtTheory.r222, HolSmtTheory.r223,
     HolSmtTheory.r224, HolSmtTheory.r225, HolSmtTheory.r226,
     HolSmtTheory.r227, HolSmtTheory.r228, HolSmtTheory.r229,
     HolSmtTheory.r230, HolSmtTheory.r231, HolSmtTheory.r232,
     HolSmtTheory.r233, HolSmtTheory.r234, HolSmtTheory.r235,
     HolSmtTheory.r236, HolSmtTheory.r237, HolSmtTheory.r238,
     HolSmtTheory.r239, HolSmtTheory.r240, HolSmtTheory.r241,
     HolSmtTheory.r242, HolSmtTheory.r243, HolSmtTheory.r244,
     HolSmtTheory.r245, HolSmtTheory.r246, HolSmtTheory.r247,
     HolSmtTheory.r248, HolSmtTheory.r249, HolSmtTheory.r250,
     HolSmtTheory.r251, HolSmtTheory.r252, HolSmtTheory.r253,
     HolSmtTheory.r254, HolSmtTheory.r255, HolSmtTheory.r256,
     HolSmtTheory.r257, HolSmtTheory.r258, HolSmtTheory.r259,
     HolSmtTheory.r260, HolSmtTheory.r261] @ set_thm_list

  val rewrite_thms = thm_net_from_list rewrite_thm_list

  val rewrite_side_thms =
    let
      fun insert (th, net) =
        case Lib.total boolSyntax.dest_eq (Thm.concl th) of
          NONE => net
        | SOME (left, right) =>
            let
              fun insert_nonvar (term, net) =
                if Term.is_var term then net else Net.insert (term, th) net
            in
              insert_nonvar (right, insert_nonvar (left, net))
            end
    in
      List.foldl insert Net.empty
        (List.concat (List.map thm_forms rewrite_thm_list))
    end

  val th_lemma_thms = thm_net_from_list
    ([HolSmtTheory.t001, HolSmtTheory.t002, HolSmtTheory.t003,
      HolSmtTheory.t004, HolSmtTheory.t005, HolSmtTheory.t006,
      HolSmtTheory.t007, HolSmtTheory.t008, HolSmtTheory.t009,
      HolSmtTheory.t010, HolSmtTheory.t011, HolSmtTheory.t012,
      HolSmtTheory.t013, HolSmtTheory.t014, HolSmtTheory.t015,
      HolSmtTheory.t016, HolSmtTheory.t017, HolSmtTheory.t018,
      HolSmtTheory.t019, HolSmtTheory.t020, HolSmtTheory.t021,
      HolSmtTheory.t022, HolSmtTheory.t023, HolSmtTheory.t024,
      HolSmtTheory.t025, HolSmtTheory.t026, HolSmtTheory.t027,
      HolSmtTheory.t028, HolSmtTheory.t029, HolSmtTheory.t030,
      HolSmtTheory.t031, HolSmtTheory.t032, HolSmtTheory.t033,
      HolSmtTheory.t034, HolSmtTheory.t035] @
     array_thm_list @ set_thm_list)

  val prove_hyp_thms = thm_net_from_list
    [HolSmtTheory.p001, HolSmtTheory.p002]
end  (* local *)

  (* finds a matching theorem, instantiates it, attempts to prove all
     hypotheses of the instantiated theorem (by instantiation or
     simplification) *)
  fun prove net t =
    Lib.tryfind
      (fn th =>
        let
          val th = Drule.INST_TY_TERM (Term.match_term (Thm.concl th) t) th
          fun prove_hyp (hyp, th) =
            let
              val hyp_th = prove prove_hyp_thms hyp
                handle Feedback.HOL_ERR _ =>
                  simpLib.SIMP_PROVE
                    (simpLib.++
                      (simpLib.++ (bossLib.std_ss, wordsLib.SIZES_ss),
                       wordsLib.WORD_GROUND_ss)) [] hyp
            in
              Drule.PROVE_HYP hyp_th th
            end
        in
          HOLset.foldl prove_hyp th (Thm.hypset th)
        end)
      (Net.match t net)

  (* Canonicalization is not substitution-stable: a schematic variable's
     Term.compare order can change when it is instantiated.  If the direct
     net lookup misses, infer an instance from either side of the rewrite,
     then canonicalize that concrete theorem and compare its exact result.
     This is generic theorem transport, not a list of commuted shapes. *)
  fun prove_rewrite t =
    prove rewrite_thms t
    handle Feedback.HOL_ERR _ =>
      let
        val (target_left, target_right) = boolSyntax.dest_eq t

        fun prove_hyp (hyp, th) =
          let
            val hyp_th = prove prove_hyp_thms hyp
              handle Feedback.HOL_ERR _ =>
                simpLib.SIMP_PROVE
                  (simpLib.++
                    (simpLib.++ (bossLib.std_ss, wordsLib.SIZES_ss),
                     wordsLib.WORD_GROUND_ss)) [] hyp
          in
            Drule.PROVE_HYP hyp_th th
          end

        fun instantiate th (pattern, target) =
          let
            val th = Drule.INST_TY_TERM
              (Term.match_term pattern target) th
            val th = Conv.CONV_RULE
              SmtReplayCanon.z3_rewrite_canon_conv th
            val _ = Term.aconv (Thm.concl th) t orelse
              raise ERR "prove_rewrite" "canonical conclusion does not match"
          in
            HOLset.foldl prove_hyp th (Thm.hypset th)
          end

        fun try_theorem th =
          let
            val (left, right) = boolSyntax.dest_eq (Thm.concl th)
          in
            Lib.tryfind (instantiate th)
              [(left, target_left), (left, target_right),
               (right, target_left), (right, target_right)]
          end
      in
        Lib.tryfind try_theorem
          (Net.match target_left rewrite_side_thms @
           Net.match target_right rewrite_side_thms)
      end

end
