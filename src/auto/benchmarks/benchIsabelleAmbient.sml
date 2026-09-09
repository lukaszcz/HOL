structure benchIsabelleAmbient :> benchIsabelleAmbient =
struct

datatype introduction =
    Fun
  | Primrec
  | Datatype
  | Simp
  | Notation
  | Representation
  | Alias
  | Definition
  | Function
  | Constructor

(* Isabelle's default simpset carries the equations of a [fun], a
   [primrec] and a datatype's selectors and predicator, and carries a
   plain [definition]'s only where one is separately declared.  The
   translation's own constants -- the ones Isabelle writes inline, the
   ones encoding a type HOL4 states differently, and the ones that
   rename a constant HOL4 already has -- withhold nothing the source
   had, so they stay.  A constructor is the other way round:
   Isabelle's simpset cannot unfold one, and the translation's equation
   for it would give a goal more than the source proof had.

   Cited lines are Isabelle2025-2, the sources the corpus commit
   f7e02b7e belongs to.  An Isabelle [abbreviation] -- [sorted],
   [sort], [insort], [insort_insert] -- is expanded by the parser, so
   an Isabelle goal carries the abbreviated application and not the
   name; the translation's equation for it is Notation, and the
   abbreviated constant's own introduction is a separate row. *)
val introductions =
  [
   ("source_Char_def", Representation, "src/HOL/String.thy:24"),
   ("source_INF_def", Notation, "src/HOL/Complete_Lattices.thy:24"),
   ("source_Id_on_def", Definition, "src/HOL/Relation.thy:1090"),
   ("source_Literal_def", Constructor, "src/HOL/String.thy:522"),
   ("source_Literal_prime_def", Simp, "src/HOL/String.thy:712"),
   ("source_SUP_def", Notation, "src/HOL/Complete_Lattices.thy:24"),
   ("source_abort_def", Simp, "src/HOL/String.thy:914"),
   ("source_abort_empty_set_def", Simp, "src/HOL/List.thy:3307"),
   ("source_add_image_def", Notation, "src/HOL/Set.thy:994"),
   ("source_alookup_def", Primrec, "src/HOL/Map.thy:90"),
   ("source_ascii_of_def", Definition, "src/HOL/String.thy:373"),
   ("source_asym_def", Definition, "src/HOL/Relation.thy:361"),
   ("source_atLeastAtMost_def", Simp, "src/HOL/Set_Interval.thy:204"),
   ("source_atLeastLessThan_def", Simp, "src/HOL/Set_Interval.thy:198"),
   ("source_atLeast_def", Simp, "src/HOL/Set_Interval.thy:120"),
   ("source_atMost_def", Simp, "src/HOL/Set_Interval.thy:126"),
   ("source_ball_def", Definition, "src/HOL/Set.thy:207"),
   ("source_bex_def", Definition, "src/HOL/Set.thy:210"),
   ("source_bit_cut_integer_def", Definition, "src/HOL/Code_Numeral.thy:715"),
   ("source_bool_num_def", Representation, "src/HOL/String.thy:24"),
   ("source_can_select_def", Simp, "src/HOL/Set.thy:1903"),
   ("source_char_of_def", Definition, "src/HOL/String.thy:57"),
   ("source_char_of_integer_def", Definition, "src/HOL/String.thy:338"),
   ("source_distinct_adj_def", Definition, "src/HOL/List.thy:259"),
   ("source_equiv_def", Definition, "src/HOL/Equiv_Relations.thy:13"),
   ("source_extract_def", Definition, "src/HOL/List.thy:217"),
   ("source_fold_def", Primrec, "src/HOL/List.thy:109"),
   ("source_foldr_def", Primrec, "src/HOL/List.thy:113"),
   ("source_greaterThanAtMost_def", Simp, "src/HOL/Set_Interval.thy:201"),
   ("source_greaterThan_def", Simp, "src/HOL/Set_Interval.thy:110"),
   ("source_hd_def", Datatype, "src/HOL/List.thy:13"),
   ("source_horner8_def", Representation, "src/HOL/String.thy:24"),
   ("source_image_def", Alias, "src/HOL/Set.thy:880"),
   ("source_indexed_from_def", Simp, "src/HOL/List.thy:5077"),
   ("source_inj_on_def", Definition, "src/HOL/Fun.thy:140"),
   ("source_insort_def", Notation, "src/HOL/List.thy:431"),
   ("source_insort_insert_def", Notation, "src/HOL/List.thy:432"),
   ("source_insort_insert_key_def", Definition, "src/HOL/List.thy:426"),
   ("source_insort_key_def", Primrec, "src/HOL/List.thy:418"),
   ("source_int_horner8_def", Representation, "src/HOL/String.thy:24"),
   ("source_integer_of_char_def", Definition, "src/HOL/String.thy:341"),
   ("source_last_def", Primrec, "src/HOL/List.thy:70"),
   ("source_lenlex_def", Alias, "src/HOL/List.thy:7064"),
   ("source_lessThan_def", Simp, "src/HOL/Set_Interval.thy:100"),
   ("source_lex_def", Definition, "src/HOL/List.thy:7061"),
   ("source_lexord_def", Alias, "src/HOL/List.thy:7305"),
   ("source_lexordp_def", Simp, "src/HOL/List.thy:7565"),
   ("source_lexordp_eq_def", Simp, "src/HOL/List.thy:7576"),
   ("source_list_all_def", Datatype, "src/HOL/List.thy:17"),
   ("source_list_ex1_def", Definition, "src/HOL/List.thy:8118"),
   ("source_list_relation_def", Notation, "src/HOL/List.thy:8701"),
   ("source_listrel1_def", Definition, "src/HOL/List.thy:7735"),
   ("source_lists_def", Simp, "src/HOL/List.thy:6861"),
   ("source_literal_append_def", Definition, "src/HOL/String.thy:634"),
   ("source_literal_asciis_def", Definition, "src/HOL/String.thy:399"),
   ("source_literal_bij", Representation, "src/HOL/String.thy:366"),
   ("source_literal_empty_def", Definition, "src/HOL/String.thy:522"),
   ("source_literal_implode_def", Definition, "src/HOL/String.thy:590"),
   ("source_literal_of_asciis_def", Definition, "src/HOL/String.thy:404"),
   ("source_literal_valid_def", Representation, "src/HOL/String.thy:366"),
   ("source_map_filter_def", Definition, "src/HOL/List.thy:8474"),
   ("source_measures_def", Simp, "src/HOL/List.thy:7719"),
   ("source_minimum_def", Definition, "src/HOL/Lattices_Big.thy:460"),
   ("source_minus_list_mset_def", Definition, "src/HOL/List.thy:241"),
   ("source_minus_list_set_def", Definition, "src/HOL/List.thy:244"),
   ("source_nths_def", Definition, "src/HOL/List.thy:292"),
   ("source_ntrancl_def", Simp, "src/HOL/Transitive_Closure.thy:1455"),
   ("source_num_upto_def", Primrec, "src/HOL/List.thy:194"),
   ("source_numeral_def", Primrec, "src/HOL/Num.thy:255"),
   ("source_of_char_def", Alias, "src/HOL/String.thy:31"),
   ("source_of_nat_def", Representation, "src/HOL/Nat.thy:1696"),
   ("source_refl_on_def", Definition, "src/HOL/Relation.thy:153"),
   ("source_rel_image_def", Definition, "src/HOL/Relation.thy:1563"),
   ("source_remove1_def", Primrec, "src/HOL/List.thy:233"),
   ("source_removeAll_def", Primrec, "src/HOL/List.thy:237"),
   ("source_rotate1_def", Primrec, "src/HOL/List.thy:285"),
   ("source_rotate_def", Definition, "src/HOL/List.thy:289"),
   ("source_set_Cons_def", Definition, "src/HOL/List.thy:6976"),
   ("source_shuffles_def", Function, "src/HOL/List.thy:313"),
   ("source_sort_def", Notation, "src/HOL/List.thy:430"),
   ("source_sort_key_def", Simp, "src/HOL/List.thy:6191"),
   ("source_sorted_def", Notation, "src/HOL/List.thy:409"),
   ("source_sorted_key_list_of_set_def", Definition, "src/HOL/List.thy:6558"),
   ("source_sorted_list_of_set_def", Definition, "src/HOL/List.thy:6726"),
   ("source_sorted_wrt_def", Fun, "src/HOL/List.thy:400"),
   ("source_stable_sort_key_def", Definition, "src/HOL/List.thy:434"),
   ("source_strict_sorted_def", Fun, "src/HOL/List.thy:400"),
   ("source_subseqs_def", Primrec, "src/HOL/List.thy:295"),
   ("source_successively_def", Fun, "src/HOL/List.thy:254"),
   ("source_superset_def", Simp, "src/HOL/List.thy:8188"),
   ("source_takeWhile_def", Primrec, "src/HOL/List.thy:166"),
   ("source_take_bit_def", Definition, "src/HOL/Bit_Operations.thy:622"),
   ("source_these_def", Definition, "src/HOL/Option.thy:277"),
   ("source_trans_list_step_def", Definition, "src/HOL/List.thy:6996"),
   ("source_transpose_def", Function, "src/HOL/List.thy:5590"),
   ("source_unit_le_def", Simp, "src/HOL/Product_Type.thy:140"),
   ("source_unit_lt_def", Simp, "src/HOL/Product_Type.thy:146"),
   ("source_unrotate1_def", Notation, "src/HOL/List.thy:285"),
   ("source_upto_aux_def", Definition, "src/HOL/List.thy:3643"),
   ("source_upto_def", Function, "src/HOL/List.thy:3572")
  ]

fun ambient introduction =
  case introduction of
      Fun => true
    | Primrec => true
    | Datatype => true
    | Simp => true
    | Notation => true
    | Representation => true
    | Alias => true
    | Definition => false
    | Function => false
    | Constructor => false

fun is_ambient name =
  case List.find (fn (entry, _, _) => entry = name) introductions of
      SOME (_, introduction, _) => ambient introduction
    | NONE =>
        raise Feedback.mk_HOL_ERR "benchIsabelleAmbient" "is_ambient"
          ("no mined introduction for " ^ name)

end
