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

  val array_thms = thm_net_from_list array_thm_list

  (* Datatype replay facts are type-specific and are harvested from TypeBase
     by SmtDatatypeProve.  There is no shared schematic layer yet. *)
  val datatype_thm_list = []
  val datatype_thms = thm_net_from_list datatype_thm_list

  (* TASK_11 seed candidates.  TASK_18 constructs the string net and appends
     it to th_lemma_thms when the string replay handler is wired. *)
  local
    open smtstringTheory smtstringz3Theory
  in
    val string_thm_list = [
      smtstr_concat_assoc,
      smtstr_concat_nil_left,
      smtstr_concat_nil_right,
      smtstr_len_concat,
      smtstr_len_nonnegative,
      smtstr_len_char,
      smtstr_unit_concat,
      smtstr_literal3_units,
      smtstr_prefixof_decompose,
      smtstr_suffixof_decompose,
      smtstr_contains_decompose,
      smtstr_lt_irrefl,
      smtstr_lt_trans,
      smtstr_lt_trichotomy,
      smtstr_le_trans,
      smtstr_le_total,
      smtstr_len_substr,
      smtstr_len_substr_source_bound,
      smtstr_len_substr_count_bound,
      smtstr_at_in_range,
      smtstr_len_at,
      smtstr_indexof_lower_bound,
      smtstr_indexof_upper_bound,
      smtstr_is_digit_to_code_bounds,
      smtstr_from_code_to_code,
      smt_in_re_concat_cons,
      smt_in_re_star_cons,
      seq_unit_length,
      seq_head_tail,
      seq_tail_step,
      seq_tail_length,
      seq_at_nth,
      char_is_digit_unicode,
      seq_digit2int_digit_bounds,
      seq_digit2int_digit,
      unicode_lt_2exp18,
      char_bit_above_unicode
    ]

    val string_thms = thm_net_from_list string_thm_list
  end

local
  open HolSmtTheory
in
  val def_axiom_thms = thm_net_from_list
    [d001, d002, d003, d004, d005, d006, d007, d008, d009, d010, d011, d012,
     d013, d014, d015, d016, d017, d018, d019, d020, d021, d022, d023, d024,
     d025, d026, d027, d028]

  val intro_def_thms = thm_net_from_list
    [i001, i002, i003, i004, i005, i006]

  val rewrite_thms = thm_net_from_list
    [r001, r002, r003, r004, r005, r006, r007, r008, r009, r010, r011, r012,
     r013, r014, r015, r016, r017, r018, r019, r020, r021, r022, r023, r024,
     r025, r026, r027, r028, r029, r030, r031, r032, r033, r034, r035, r036,
     r037, r038, r039, r040, r041, r042, r043, r044, r045, r046, r047, r048,
     r049, r050, r051, r052, r053, r054, r055, r056, r057, r058, r059, r060,
     r061, r062, r063, r064, r065, r066, r067, r068, r069, r070, r071, r072,
     r073, r074, r075, r076, r077, r078, r079, r080, r081, r082, r083, r084,
     r085, r086, r087, r088, r089, r090, r091, r092, r093, r094, r095, r096,
     r097, r098, r099, r100, r101, r102, r103, r104, r105, r106, r107, r108,
     r109, r110, r111, r112, r113, r114, r115, r116, r117, r118, r119, r120,
     r121, r122, r123, r124, r125, r126, r127, r128, r129, r130, r131, r132,
     r133, r134, r135, r136, r137, r138, r139, r140, r141, r142, r143, r144,
     r145, r146, r147, r148, r149, r150, r151, r152, r153, r154, r155, r156,
     r157, r158, r159, r160, r161, r162, r163, r164, r165, r166, r167, r168,
     r169, r170, r171, r172, r173, r174, r175, r176, r177, r178, r179, r180,
     r181, r182, r183, r184, r185, r186, r187, r188, r189, r190, r191, r192,
     r193, r194, r195, r196, r197, r198, r199, r200, r201, r202, r203, r204,
     r205, r206, r207, r208, r209, r210, r211, r212, r213, r214, r215, r216,
     r217, r218, r219, r220, r221, r222, r223, r224, r225, r226, r227, r228,
     r229, r230, r231, r232, r233, r234, r235, r236, r237, r238, r239, r240,
     r241, r242, r243, r244, r245, r246, r247, r248, r249, r250, r251, r252,
     r253, r254, r255, r256, r257, r258, r259, r260, r261]

  val th_lemma_thms = thm_net_from_list
    ([t001, t002, t003, t004, t005, t006, t007, t008, t009, t010, t011,
      t012, t013, t014, t015, t016, t017, t018, t019, t020, t021, t022,
      t023, t024, t025, t026, t027, t028, t029, t030, t031, t032, t033,
      t034, t035] @ array_thm_list @ datatype_thm_list @ string_thm_list)

  val prove_hyp_thms = thm_net_from_list
    [p001, p002, p003, p004, p005, p006, p007, p008, p009]
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
                  simpLib.SIMP_PROVE (simpLib.++ (bossLib.std_ss,
                    wordsLib.SIZES_ss)) [] hyp
            in
              Drule.PROVE_HYP hyp_th th
            end
        in
          HOLset.foldl prove_hyp th (Thm.hypset th)
        end)
      (Net.match t net)

end
