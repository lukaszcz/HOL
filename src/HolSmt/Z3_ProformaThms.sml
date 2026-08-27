(* Copyright (c) 2009-2010 Tjark Weber. All rights reserved. *)

(* Proforma theorems, used for Z3 proof reconstruction *)

structure Z3_ProformaThms =
struct

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
  fun thm_net_from_list thms =
    let
      fun insert (th, net) = Net.insert (Thm.concl th, th) net
      fun forms th =
        let val undisched = undisch_code_point_bounds th
        in
          if Term.aconv (Thm.concl undisched) (Thm.concl th) then [th]
          else [th, undisched]
        end
    in
      List.foldl insert Net.empty (List.concat (List.map forms thms))
    end

  val array_thm_list = [
    Tactical.prove
      (``((i =+ e) a) i = e``,
        bossLib.RW_TAC (bossLib.srw_ss()) [combinTheory.APPLY_UPDATE_THM]),
    Tactical.prove
      (``i <> j ==> ((i =+ e) a) j = a j``,
        bossLib.RW_TAC (bossLib.srw_ss()) [combinTheory.APPLY_UPDATE_THM]),
    Tactical.prove
      (``(i =+ f) ((i =+ e) a) = (i =+ f) a``,
        bossLib.RW_TAC (bossLib.srw_ss()) [
          boolTheory.FUN_EQ_THM,
          combinTheory.APPLY_UPDATE_THM
        ]),
    Tactical.prove
      (``i <> j ==>
          (j =+ f) ((i =+ e) a) = (i =+ e) ((j =+ f) a)``,
        Tactical.THEN (bossLib.RW_TAC (bossLib.srw_ss()) [
            boolTheory.FUN_EQ_THM,
            combinTheory.APPLY_UPDATE_THM
          ], bossLib.METIS_TAC [])),
    Tactical.prove
      (``i <> j ==> ((j =+ f) ((i =+ e) a)) i = e``,
        bossLib.RW_TAC (bossLib.srw_ss()) [combinTheory.APPLY_UPDATE_THM]),
    Tactical.prove
      (``i <> j ==> ((j =+ f) ((i =+ e) a)) j = f``,
        bossLib.RW_TAC (bossLib.srw_ss()) [combinTheory.APPLY_UPDATE_THM]),
    Tactical.prove
      (``(!i. a i = b i) ==> (a = b)``,
        bossLib.RW_TAC (bossLib.srw_ss()) [boolTheory.FUN_EQ_THM]),
    Tactical.prove
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
    Tactical.prove
      (``((s:'a set) SUBSET t) =
          ((\x. x IN s /\ x NOTIN t) = (EMPTY:'a set))``,
       Tactical.THEN (bossLib.RW_TAC (bossLib.srw_ss())
         [pred_setTheory.SUBSET_DEF, pred_setTheory.EXTENSION],
         bossLib.METIS_TAC [])),
    (* A store pushed through Z3's Boolean map-not. *)
    Tactical.prove
      (``(\x. ~((i =+ v) (s:'a set)) x) =
          (i =+ ~v) (\x. ~s x)``,
       Tactical.THEN (bossLib.RW_TAC (bossLib.srw_ss())
         [boolTheory.FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM],
         Tactical.THEN (Tactical.REPEAT boolLib.COND_CASES_TAC,
           bossLib.RW_TAC (bossLib.srw_ss()) []))),
    Tactical.prove
      (``(!x:'a. x IN s <=> x IN t) ==> (s = t)``,
       bossLib.RW_TAC (bossLib.srw_ss()) [pred_setTheory.EXTENSION]),
    Tactical.prove
      (``F = ((x:'a) IN (EMPTY:'a set))``,
       bossLib.RW_TAC (bossLib.srw_ss()) [pred_setTheory.NOT_IN_EMPTY]),
    Tactical.prove
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
        [smtfp_bits_pzero, smtfp_pzero_bits,
         smtfp_bits_nzero, smtfp_nzero_bits,
         smtfp_bits_pinf, smtfp_pinf_bits,
         smtfp_bits_ninf, smtfp_ninf_bits,
         smtfp_bits_nan, smtfp_nan_bits]

    val rounding_distinct_thms = Drule.CONJUNCTS smt_rounding_distinctness
  in
    val fp_thm_list =
      (* literal_positive/negative_zero, literal_positive/negative_infinity,
         literal_nan, and nan_payload_equality *)
      literal_normalization_thms @
      (* symbolic_classification_nan_positive and the arbitrary-format
         classification probes' abs normalization *)
      [smtfp_is_nan_bits, smtfp_abs_bits, smtfp_neg_neg,
       smtfp_abs_abs, smtfp_abs_neg] @
      (* Ground rewrites use reflexivity; symbolic comparisons contain
         equality/symmetry transport and an fp.eq atom. *)
      [smtfp_equality_refl, smtfp_equality_symm,
       smtfp_eq_refl, smtfp_eq_of_equality, smtfp_eq_signed_zero] @
      (* ground_add/ground_div and conversions print RNE/RNA/RTZ literals;
         constructor distinctness and exhaustion are their enum boundary. *)
      [smt_rounding_refl, Drule.SPEC_ALL smt_rounding_cases] @
      rounding_distinct_thms

    val fp_thms = thm_net_from_list fp_thm_list
  end

local
  open HolSmtTheory
in
  val def_axiom_thms = thm_net_from_list
    [d001, d002, d003, d004, d005, d006, d007, d008, d009, d010, d011, d012,
     d013, d014, d015, d016, d017, d018, d019, d020, d021, d022, d023, d024,
     d025, d026, d027, d028]

  val rewrite_thms = thm_net_from_list
    ([r001, r002, r003, r004, r005, r006, r007, r008, r009, r010, r011, r012,
     r013, r014, r015, r016, r017, r018, r019, r020, r021, r022, r023, r024,
     r025, r026, r027, r028, r029, r030, r031, r032,
     r037, r038, r039, r040, r041, r042, r043, r044, r045, r046, r047, r048,
     r049, r050, r051, r052, r053, r054, r055, r056, r057, r058, r059, r060,
     r061, r062, r063, r064, r065, r066, r067, r068, r069, r070,
     r219, r220, r221, r222, r223, r224, r225, r226, r227, r228,
     r229, r230, r231, r232, r233, r234, r235, r236, r237, r238, r239, r240,
     r241, r242, r243, r244, r245, r246, r247, r248, r249, r250, r251, r252,
     r253, r254, r255, r256, r257, r258, r259, r260, r261] @
    set_thm_list)

  val th_lemma_thms = thm_net_from_list
    ([t001, t002, t003, t004, t005, t006, t007, t008, t009, t010, t011,
      t012, t013, t014, t015, t016, t017, t018, t019, t020, t021, t022,
      t023, t024, t025, t026, t027, t028, t029, t030, t031, t032, t033,
      t034, t035] @ array_thm_list @ set_thm_list)

  val prove_hyp_thms = thm_net_from_list
    [p001, p002]
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

end
