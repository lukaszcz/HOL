(* Copyright (c) 2010-2011 Tjark Weber. All rights reserved. *)

(* SMT-LIB 2 logics *)

structure SmtLib_Logics =
struct

local

  val ERR = Feedback.mk_HOL_ERR "SmtLib_Logics"

  fun union_dicts (x::xs) =
    List.foldl (Lib.uncurry Library.union_dict o Lib.swap) x xs
    | union_dicts [] =
    raise ERR "union_dicts" "empty list"

  fun union_metadata xs = List.concat xs

  (* because int-to-real conversions may be combined with :chainable
     and :{left,right}-assoc functions, 'one_int_to_real' converts *at
     most* (rather than exactly) one integer argument to real *)
  fun one_int_to_real (t1, t2) =
      (intrealSyntax.mk_real_of_int t1, t2)
    handle Feedback.HOL_ERR _ =>
      (t1, intrealSyntax.mk_real_of_int t2)
    handle Feedback.HOL_ERR _ =>
      (t1, t2)

  (* converts *at most* (rather than exactly) two integer arguments to
     reals (cf. 'one_int_to_real' *)
  fun two_ints_to_real (t1, t2) =
      (intrealSyntax.mk_real_of_int t1, intrealSyntax.mk_real_of_int t2)
    handle Feedback.HOL_ERR _ =>
      one_int_to_real (t1, t2)

  open SmtLib_Theories

  val BV_extension_tmentries = [
    (* bit-vector constants *)
    extension_entry "Z3" "_" (indexed_attributes ["m"])
      ["((_ bv<numeral> m) (_ BitVec m))"] (one_zero (fn token => fn n_tm =>
      if String.isPrefix "bv" token then
        let
          val decimal = String.extract (token, 2, NONE)
          val value = Library.parse_arbnum decimal
          val n = Arbint.toNat (intSyntax.int_of_term n_tm)
        in
          Lib.curry wordsSyntax.mk_word value n
        end
     else
        raise ERR "<BV_extension_dict._>" "not a bit-vector constant")),
    extension_entry "Z3" "bvand" left_assoc_attributes []
      (leftassoc wordsSyntax.mk_word_and),
    extension_entry "Z3" "bvor" left_assoc_attributes []
      (leftassoc wordsSyntax.mk_word_or),
    extension_entry "Z3" "bvadd" left_assoc_attributes []
      (leftassoc wordsSyntax.mk_word_add),
    extension_entry "Z3" "bvmul" left_assoc_attributes []
      (leftassoc wordsSyntax.mk_word_mul),
    extension_entry "Z3" "bvnand" no_attributes []
      (K_zero_two wordsSyntax.mk_word_nand),
    extension_entry "Z3" "bvnor" no_attributes []
      (K_zero_two wordsSyntax.mk_word_nor),
    extension_entry "Z3" "bvxor" left_assoc_attributes []
      (leftassoc wordsSyntax.mk_word_xor),
    extension_entry "Z3" "bvxnor" left_assoc_attributes []
      (leftassoc wordsSyntax.mk_word_xnor),
    extension_entry "Z3" "bvcomp" no_attributes []
      (K_zero_two wordsSyntax.mk_word_compare),
    extension_entry "Z3" "bvsub" no_attributes []
      (K_zero_two wordsSyntax.mk_word_sub),
    extension_entry "Z3" "bvsdiv" no_attributes []
      (K_zero_two wordsSyntax.mk_word_quot),
    extension_entry "Z3" "bvsdiv_i" no_attributes []
      (K_zero_two wordsSyntax.mk_word_quot),
    extension_entry "Z3" "bvsrem" no_attributes []
      (K_zero_two wordsSyntax.mk_word_rem),
    extension_entry "Z3" "bvsrem_i" no_attributes []
      (K_zero_two wordsSyntax.mk_word_rem),
    extension_entry "Z3" "bvsmod" no_attributes []
      (K_zero_two integer_wordSyntax.mk_word_smod),
    extension_entry "Z3" "bvashr" no_attributes []
      (K_zero_two wordsSyntax.mk_word_asr_bv),
    extension_entry "Z3" "repeat" (indexed_attributes ["n"]) []
      (K_one_one
      (Lib.curry wordsSyntax.mk_word_replicate o numSyntax.mk_numeral o
      Arbint.toNat o intSyntax.int_of_term)),
    extension_entry "Z3" "zero_extend" (indexed_attributes ["n"]) []
      (K_one_one (fn n => fn t => wordsSyntax.mk_w2w (t,
      fcpLib.index_type
        (Arbnum.+ (fcpLib.index_to_num (wordsSyntax.dim_of t),
          Arbint.toNat (intSyntax.int_of_term n)))))),
    extension_entry "Z3" "sign_extend" (indexed_attributes ["n"]) []
      (K_one_one (fn n => fn t => wordsSyntax.mk_sw2sw (t,
      fcpLib.index_type
        (Arbnum.+ (fcpLib.index_to_num (wordsSyntax.dim_of t),
          Arbint.toNat (intSyntax.int_of_term n)))))),
    extension_entry "Z3" "rotate_left" (indexed_attributes ["n"]) []
      (K_one_one
      (Lib.C (Lib.curry wordsSyntax.mk_word_rol) o numSyntax.mk_numeral o
        Arbint.toNat o intSyntax.int_of_term)),
    extension_entry "Z3" "rotate_right" (indexed_attributes ["n"]) []
      (K_one_one
      (Lib.C (Lib.curry wordsSyntax.mk_word_ror) o numSyntax.mk_numeral o
        Arbint.toNat o intSyntax.int_of_term)),
    extension_entry "Z3" "bvule" no_attributes []
      (K_zero_two wordsSyntax.mk_word_ls),
    extension_entry "Z3" "bvugt" no_attributes []
      (K_zero_two wordsSyntax.mk_word_hi),
    extension_entry "Z3" "bvuge" no_attributes []
      (K_zero_two wordsSyntax.mk_word_hs),
    extension_entry "Z3" "bvslt" no_attributes []
      (K_zero_two wordsSyntax.mk_word_lt),
    extension_entry "Z3" "bvsle" no_attributes []
      (K_zero_two wordsSyntax.mk_word_le),
    extension_entry "Z3" "bvsgt" no_attributes []
      (K_zero_two wordsSyntax.mk_word_gt),
    extension_entry "Z3" "bvsge" no_attributes []
      (K_zero_two wordsSyntax.mk_word_ge)
  ]

  val BV_extension_tmdict = dictionary_of_entries BV_extension_tmentries
  val BV_extension_metadata =
    metadata_of_entries "Fixed_Size_BitVectors" "term" BV_extension_tmentries

in

  (* In general, parsing is too liberal -- for instance, we do not
     check that the input satisfies the linearity constraints that are
     defined by various logics. Our aim is not to validate the SMT-LIB
     input, but merely to produce meaningful results for valid
     inputs. *)

  structure AUFLIA =
  struct
    val tydict = union_dicts [Core.tydict, Ints.tydict, ArraysEx.tydict]
    val tmdict = union_dicts [Core.tmdict, Ints.tmdict, ArraysEx.tmdict]
    val metadata = union_metadata [Core.metadata, Ints.metadata,
      ArraysEx.metadata]
  end

  structure AUFLIRA =
  struct
    val tydict = union_dicts [Core.tydict, Reals_Ints.tydict, ArraysEx.tydict]
    val tmdict = union_dicts [Core.tmdict, Reals_Ints.tmdict, ArraysEx.tmdict,
      (* "For every operator op with declaration (op Real Real s) for
         some sort s, and every term t1, t2 of sort Int and t of sort
         Real, the expression

         - (op t1 t) is syntactic sugar for (op (to_real t1) t)
         - (op t t1) is syntactic sugar for (op t (to_real t1))
         - (/ t1 t2) is syntactic sugar for (/ (to_real t1) (to_real t2))"

         We only implement this for the operators in
         {Core,Reals_Ints,ArraysEx}.tmdict. Implementing it in
         general, also for user-defined operators, would require a
         change to our parser architecture.

         A discussion on the SMT-LIB mailing list in October 2010
         (http://www.cs.nyu.edu/pipermail/smt-lib/2010/000403.html)
         was in favor of removing implicit conversions from the
         SMT-LIB language altogether, but this is not reflected in the
         SMT-LIB standard yet. *)

      Library.dict_from_list [
        ("=", chainable (boolSyntax.mk_eq o one_int_to_real)),
        ("-", leftassoc (realSyntax.mk_minus o one_int_to_real)),
        ("+", leftassoc (realSyntax.mk_plus o one_int_to_real)),
        ("*", leftassoc (realSyntax.mk_mult o one_int_to_real)),
        ("/", leftassoc (realSyntax.mk_div o two_ints_to_real)),
        ("<=", chainable (realSyntax.mk_leq o one_int_to_real)),
        ("<", chainable (realSyntax.mk_less o one_int_to_real)),
        (">=", chainable (realSyntax.mk_geq o one_int_to_real)),
        (">", chainable (realSyntax.mk_greater o one_int_to_real))
      ]]
    val metadata = union_metadata [Core.metadata, Reals_Ints.metadata,
      ArraysEx.metadata]
  end

  structure AUFNIRA =
  struct
    val tydict = AUFLIRA.tydict
    val tmdict = AUFLIRA.tmdict
    val metadata = AUFLIRA.metadata
  end

  structure LRA =
  struct
    val tydict = union_dicts [Core.tydict, Reals.tydict]
    val tmdict = union_dicts [Core.tmdict, Reals.tmdict]
    val metadata = union_metadata [Core.metadata, Reals.metadata]
  end

  structure QF_ABV =
  struct
    val tydict = union_dicts [Core.tydict, Fixed_Size_BitVectors.tydict,
      ArraysEx.tydict]
    val tmdict = union_dicts [Core.tmdict, Fixed_Size_BitVectors.tmdict,
      ArraysEx.tmdict, BV_extension_tmdict]
    val metadata = union_metadata [Core.metadata, Fixed_Size_BitVectors.metadata,
      ArraysEx.metadata, BV_extension_metadata]
  end

  structure QF_AUFBV =
  struct
    val tydict = QF_ABV.tydict
    val tmdict = QF_ABV.tmdict
    val metadata = QF_ABV.metadata
  end

  structure QF_AUFLIA =
  struct
    val tydict = AUFLIA.tydict
    val tmdict = AUFLIA.tmdict
    val metadata = AUFLIA.metadata
  end

  structure QF_AX =
  struct
    val tydict = union_dicts [Core.tydict, ArraysEx.tydict]
    val tmdict = union_dicts [Core.tmdict, ArraysEx.tmdict]
    val metadata = union_metadata [Core.metadata, ArraysEx.metadata]
  end

  structure QF_BV =
  struct
    val tydict = union_dicts [Core.tydict, Fixed_Size_BitVectors.tydict]
    val tmdict = union_dicts [Core.tmdict, Fixed_Size_BitVectors.tmdict,
      BV_extension_tmdict]
    val metadata = union_metadata [Core.metadata,
      Fixed_Size_BitVectors.metadata, BV_extension_metadata]
  end

  structure QF_IDL =
  struct
    val tydict = union_dicts [Core.tydict, Ints.tydict]
    val tmdict = union_dicts [Core.tmdict, Ints.tmdict]
    val metadata = union_metadata [Core.metadata, Ints.metadata]
  end

  structure QF_LIA =
  struct
    val tydict = QF_IDL.tydict
    val tmdict = QF_IDL.tmdict
    val metadata = QF_IDL.metadata
  end

  structure QF_LRA =
  struct
    val tydict = LRA.tydict
    val tmdict = LRA.tmdict
    val metadata = LRA.metadata
  end

  structure QF_NIA =
  struct
    val tydict = QF_IDL.tydict
    val tmdict = QF_IDL.tmdict
    val metadata = QF_IDL.metadata
  end

  structure QF_NRA =
  struct
    val tydict = LRA.tydict
    val tmdict = LRA.tmdict
    val metadata = LRA.metadata
  end

  structure QF_RDL =
  struct
    val tydict = LRA.tydict
    val tmdict = LRA.tmdict
    val metadata = LRA.metadata
  end

  structure QF_UF =
  struct
    val tydict = Core.tydict
    val tmdict = Core.tmdict
    val metadata = Core.metadata
  end

  structure QF_UFBV =
  struct
    val tydict = QF_BV.tydict
    val tmdict = QF_BV.tmdict
    val metadata = QF_BV.metadata
  end

  structure QF_UFIDL =
  struct
    val tydict = QF_IDL.tydict
    val tmdict = QF_IDL.tmdict
    val metadata = QF_IDL.metadata
  end

  structure QF_UFLIA =
  struct
    val tydict = QF_IDL.tydict
    val tmdict = QF_IDL.tmdict
    val metadata = QF_IDL.metadata
  end

  structure QF_UFLRA =
  struct
    val tydict = LRA.tydict
    val tmdict = LRA.tmdict
    val metadata = LRA.metadata
  end

  structure QF_UFNRA =
  struct
    val tydict = LRA.tydict
    val tmdict = LRA.tmdict
    val metadata = LRA.metadata
  end

  structure UFLRA =
  struct
    val tydict = LRA.tydict
    val tmdict = LRA.tmdict
    val metadata = LRA.metadata
  end

  structure UFNIA =
  struct
    val tydict = QF_IDL.tydict
    val tmdict = QF_IDL.tmdict
    val metadata = QF_IDL.metadata
  end

  (* returns a type dictionary and a term dictionary that can be used
     to parse types/terms of the given SMT-LIB 2 logic *)
  fun parsedicts_of_logic (logic : string) =
    case logic of
      "AUFLIA" =>
      (AUFLIA.tydict, AUFLIA.tmdict)
    | "AUFLIRA" =>
      (AUFLIRA.tydict, AUFLIRA.tmdict)
    | "AUFNIRA" =>
      (AUFNIRA.tydict, AUFNIRA.tmdict)
    | "LRA" =>
      (LRA.tydict, LRA.tmdict)
    | "QF_ABV" =>
      (QF_ABV.tydict, QF_ABV.tmdict)
    | "QF_AUFBV" =>
      (QF_AUFBV.tydict, QF_AUFBV.tmdict)
    | "QF_AUFLIA" =>
      (QF_AUFLIA.tydict, QF_AUFLIA.tmdict)
    | "QF_AX" =>
      (QF_AX.tydict, QF_AX.tmdict)
    | "QF_BV" =>
      (QF_BV.tydict, QF_BV.tmdict)
    | "QF_IDL" =>
      (QF_IDL.tydict, QF_IDL.tmdict)
    | "QF_LIA" =>
      (QF_LIA.tydict, QF_LIA.tmdict)
    | "QF_LRA" =>
      (QF_LRA.tydict, QF_LRA.tmdict)
    | "QF_NIA" =>
      (QF_NIA.tydict, QF_NIA.tmdict)
    | "QF_NRA" =>
      (QF_NRA.tydict, QF_NRA.tmdict)
    | "QF_RDL" =>
      (QF_RDL.tydict, QF_RDL.tmdict)
    | "QF_UF" =>
      (QF_UF.tydict, QF_UF.tmdict)
    | "QF_UFBV" =>
      (QF_UFBV.tydict, QF_UFBV.tmdict)
    | "QF_UFIDL" =>
      (QF_UFIDL.tydict, QF_UFIDL.tmdict)
    | "QF_UFLIA" =>
      (QF_UFLIA.tydict, QF_UFLIA.tmdict)
    | "QF_UFLRA" =>
      (QF_UFLRA.tydict, QF_UFLRA.tmdict)
    | "QF_UFNRA" =>
      (QF_UFNRA.tydict, QF_UFNRA.tmdict)
    | "UFLRA" =>
      (UFLRA.tydict, UFLRA.tmdict)
    | "UFNIA" =>
      (UFNIA.tydict, UFNIA.tmdict)
    | _ =>
      raise ERR "parsedicts_of_logic" ("unknown logic '" ^ logic ^ "'")

  (* returns the symbol metadata used to build the parse dictionaries of
     the given SMT-LIB 2 logic *)
  fun metadata_of_logic (logic : string) =
    case logic of
      "AUFLIA" => AUFLIA.metadata
    | "AUFLIRA" => AUFLIRA.metadata
    | "AUFNIRA" => AUFNIRA.metadata
    | "LRA" => LRA.metadata
    | "QF_ABV" => QF_ABV.metadata
    | "QF_AUFBV" => QF_AUFBV.metadata
    | "QF_AUFLIA" => QF_AUFLIA.metadata
    | "QF_AX" => QF_AX.metadata
    | "QF_BV" => QF_BV.metadata
    | "QF_IDL" => QF_IDL.metadata
    | "QF_LIA" => QF_LIA.metadata
    | "QF_LRA" => QF_LRA.metadata
    | "QF_NIA" => QF_NIA.metadata
    | "QF_NRA" => QF_NRA.metadata
    | "QF_RDL" => QF_RDL.metadata
    | "QF_UF" => QF_UF.metadata
    | "QF_UFBV" => QF_UFBV.metadata
    | "QF_UFIDL" => QF_UFIDL.metadata
    | "QF_UFLIA" => QF_UFLIA.metadata
    | "QF_UFLRA" => QF_UFLRA.metadata
    | "QF_UFNRA" => QF_UFNRA.metadata
    | "UFLRA" => UFLRA.metadata
    | "UFNIA" => UFNIA.metadata
    | _ =>
      raise ERR "metadata_of_logic" ("unknown logic '" ^ logic ^ "'")

end  (* local *)

end
