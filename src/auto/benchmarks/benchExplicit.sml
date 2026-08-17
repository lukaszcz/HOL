structure benchExplicit =
struct

open HolKernel

fun split_display display =
  case String.fields (equal #"$") display of
      [theory, theorem] => (theory, theorem)
    | _ => raise Fail ("invalid theorem display name: " ^ display)

fun preferred_theorem display fallback_theory fallback_theorem =
  let
    val fallback = DB.fetch fallback_theory fallback_theorem
    val (display_theory, display_theorem) = split_display display
  in
    DB.fetch display_theory display_theorem
    handle HOL_ERR _ => fallback
  end

fun named_at display theory theorem : benchLib.named_thm =
  {name = display,
   theorem = preferred_theorem display theory theorem}

fun named_once_at display theory theorem : benchLib.named_thm =
  {name = display,
   theorem =
     BoundedRewrites.Once
       (preferred_theorem display theory theorem)}

fun named display =
  case display of
      "pred_set$MEMBER_NOT_EMPTY_reverse" =>
        {name = display,
         theorem =
           Drule.GEN_ALL
             (Thm.SYM
               (Drule.SPEC_ALL pred_setTheory.MEMBER_NOT_EMPTY))}
    | "list$SNOC_APPEND[symmetric]" =>
        {name = display, theorem = Conv.GSYM listTheory.SNOC_APPEND}
    | "list$HD_CONV_EL" =>
        {name = display,
         theorem =
           Drule.GEN_ALL
             (Thm.SYM
               (Drule.SPEC_ALL (CONJUNCT1 listTheory.EL)))}
    | "list$MAP_REVERSE[symmetric]" =>
        {name = display,
         theorem =
           Drule.GEN_ALL
             (Thm.SYM (Drule.SPEC_ALL listTheory.MAP_REVERSE))}
    | "list$FILTER_REVERSE[symmetric]" =>
        {name = display,
         theorem =
           Drule.GEN_ALL
             (Thm.SYM (Drule.SPEC_ALL listTheory.FILTER_REVERSE))}
    | "list$nub_set_for_card_set" =>
        {name = display, theorem = listTheory.nub_set}
    | "list$ALL_DISTINCT_CARD_LIST_TO_SET_for_nub" =>
        {name = display,
         theorem = listTheory.ALL_DISTINCT_CARD_LIST_TO_SET}
    | "list$all_distinct_nub" =>
        {name = display, theorem = listTheory.all_distinct_nub}
    | "list$LIST_REL_NIL" =>
        {name = display, theorem = CONJUNCT1 listTheory.LIST_REL_NIL}
    | "option$FORALL_OPTION[of-not-P]" =>
        {name = display, theorem = optionTheory.FORALL_OPTION}
    | "pair$case_prod_eta" =>
        {name = display,
         theorem =
           Drule.GEN_ALL
             (Thm.SYM (Drule.SPEC_ALL pairTheory.LAMBDA_PROD))}
    | _ =>
        let
          val (theory, theorem) = split_display display
        in
          named_at display theory theorem
        end

fun zip_map1 () : benchLib.named_thm =
  {name = "parityTranslation$source_zip_map_map",
   theorem =
     simpLib.SIMP_RULE boolSimps.bool_ss
       [listTheory.MAP_ID, combinTheory.I_THM, pairTheory.LAMBDA_PROD]
       (Drule.ISPECL
          [``v_xs0 : 'c list``, ``v_ys0 : 'b list``,
           ``v_f0 : 'c -> 'a``, ``I : 'b -> 'b``]
          parityTranslationTheory.source_zip_map_map)}

fun zip_map2 () : benchLib.named_thm =
  {name = "parityTranslation$source_zip_map_map",
   theorem =
     simpLib.SIMP_RULE boolSimps.bool_ss
       [listTheory.MAP_ID, combinTheory.I_THM, pairTheory.LAMBDA_PROD]
       (Drule.ISPECL
          [``v_xs0 : 'a list``, ``v_ys0 : 'c list``,
           ``I : 'a -> 'a``, ``v_f0 : 'c -> 'b``]
          parityTranslationTheory.source_zip_map_map)}

fun named_specialized display target =
  let
    val base = #theorem (named display)
    val theorem =
      if List.exists (equal display)
           ["pred_set$MEMBER_NOT_EMPTY_reverse",
            "list$SNOC_APPEND[symmetric]", "list$HD_CONV_EL",
            "list$MAP_REVERSE[symmetric]",
            "list$FILTER_REVERSE[symmetric]", "list$LIST_REL_NIL",
            "pair$case_prod_eta"]
      then base
      else
        Drule.PART_MATCH I base target
        handle error as HOL_ERR _ =>
          raise Fail
            ("cannot specialize " ^ display ^ ": " ^
             Feedback.exn_to_string error)
  in
    {name = display, theorem = theorem}
  end

val list_predicate_normalization_frag =
  simpLib.name_ss "benchmark list predicate normalization"
    (simpLib.merge_ss
      [simpLib.std_conv_ss
         {name = "benchmark EVERY membership normalization",
          pats = [``EVERY (predicate : 'a -> bool) xs``],
          conv = Conv.REWR_CONV listTheory.EVERY_MEM},
       simpLib.std_conv_ss
         {name = "benchmark EXISTS membership normalization",
          pats = [``EXISTS (predicate : 'a -> bool) xs``],
          conv = Conv.REWR_CONV listTheory.EXISTS_MEM}])

fun fragment name =
  if name = "benchmark list predicate normalization" then
    benchLib.SimpFragmentAdd (name, list_predicate_normalization_frag)
  else
    case simpLib.lookup_named_frag name of
        SOME value => benchLib.SimpFragmentAdd (name, value)
      | NONE => raise Fail ("unknown simp fragment: " ^ name)

end
