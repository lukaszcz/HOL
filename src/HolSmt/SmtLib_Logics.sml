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
    extension_entry "Z3" "bvudiv_i" (soundness_audit_attributes no_attributes)
      ["Z3 proof alias for bvudiv"]
      (K_zero_two wordsSyntax.mk_word_div),
    extension_entry "Z3" "bvurem_i" (soundness_audit_attributes no_attributes)
      ["Z3 proof alias for bvurem"]
      (K_zero_two wordsSyntax.mk_word_mod),
    extension_entry "Z3" "bvsdiv_i" (soundness_audit_attributes no_attributes)
      ["Z3 proof alias for bvsdiv"]
      (K_zero_two wordsSyntax.mk_word_quot),
    extension_entry "Z3" "bvsrem_i" (soundness_audit_attributes no_attributes)
      ["Z3 proof alias for bvsrem"]
      (K_zero_two wordsSyntax.mk_word_rem)
  ]

  val BV_extension_tmdict = dictionary_of_entries BV_extension_tmentries
  val BV_extension_metadata =
    metadata_of_entries "Fixed_Size_BitVectors" "term" BV_extension_tmentries

  structure Strings_Ints =
  struct
    val tydict = union_dicts [Core.tydict, Ints.tydict,
      UnicodeStrings.tydict]
    val tmdict = union_dicts [Core.tmdict, Ints.tmdict,
      UnicodeStrings.tmdict]
    val metadata = union_metadata [Core.metadata, Ints.metadata,
      UnicodeStrings.metadata]
  end

  structure FP_Core =
  struct
    val tydict = union_dicts [Core.tydict, Ints.tydict, Reals.tydict,
      Fixed_Size_BitVectors.tydict, FloatingPoint.tydict]
    val tmdict = union_dicts [Core.tmdict, Ints.tmdict, Reals.tmdict,
      Fixed_Size_BitVectors.tmdict, FloatingPoint.tmdict, BV_extension_tmdict]
    val metadata = union_metadata [Core.metadata, Ints.metadata, Reals.metadata,
      Fixed_Size_BitVectors.metadata, FloatingPoint.metadata,
      BV_extension_metadata]
  end

  structure FP_Arrays =
  struct
    val tydict = union_dicts [FP_Core.tydict, ArraysEx.tydict]
    val tmdict = union_dicts [FP_Core.tmdict, ArraysEx.tmdict]
    val metadata = union_metadata [FP_Core.metadata, ArraysEx.metadata]
  end

  structure ALL =
  struct
    val tydict = union_dicts [Core.tydict, Ints.tydict, Reals.tydict,
      Reals_Ints.tydict, HO_Core.tydict, ArraysEx.tydict,
      Fixed_Size_BitVectors.tydict, FloatingPoint.tydict,
      UnicodeStrings.tydict, Z3_Extensions.tydict]
    val tmdict = union_dicts [Core.tmdict, Ints.tmdict, Reals.tmdict,
      Reals_Ints.tmdict, HO_Core.tmdict, ArraysEx.tmdict,
      Fixed_Size_BitVectors.tmdict, FloatingPoint.tmdict,
      UnicodeStrings.tmdict, Z3_Extensions.tmdict, BV_extension_tmdict]
    val metadata = union_metadata [Core.metadata, Ints.metadata,
      Reals.metadata, Reals_Ints.metadata, HO_Core.metadata, ArraysEx.metadata,
      Fixed_Size_BitVectors.metadata, FloatingPoint.metadata,
      UnicodeStrings.metadata, Z3_Extensions.metadata, BV_extension_metadata]
  end

in

  (* A parser normally has only a logic name, so `parsedicts_of_logic` stays
     deliberately solver-neutral.  Seq/Set/Bag add non-standard dialects;
     their entries are registered against both the solver and logic, then
     selected explicitly by solver-facing parsers and proof readers. *)
  type type_parse_fn =
    string -> Term.term list -> Type.hol_type list -> Type.hol_type
  type term_parse_fn = string -> Term.term list -> Term.term list -> Term.term
  type dialect_dicts =
    (string, type_parse_fn list) Redblackmap.dict *
    (string, term_parse_fn list) Redblackmap.dict
  type dialect_dictionary_registration = {
    solver : string,
    logic : string,
    dictionaries : dialect_dicts
  }

  val dialect_dictionary_registrations =
    ref ([] : dialect_dictionary_registration list)
  val default_dialect_dictionary_registrations =
    ref ([] : dialect_dictionary_registration list)

  fun register_dialect_dictionary registration =
    dialect_dictionary_registrations :=
      registration :: !dialect_dictionary_registrations

  fun clear_dialect_dictionaries () =
    dialect_dictionary_registrations := !default_dialect_dictionary_registrations

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
    val tydict = union_dicts [Core.tydict, Ints.tydict,
      Fixed_Size_BitVectors.tydict, ArraysEx.tydict]
    val tmdict = union_dicts [Core.tmdict, Ints.tmdict,
      Fixed_Size_BitVectors.tmdict, ArraysEx.tmdict, BV_extension_tmdict]
    val metadata = union_metadata [Core.metadata, Ints.metadata,
      Fixed_Size_BitVectors.metadata, ArraysEx.metadata, BV_extension_metadata]
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
    val tydict = union_dicts [Core.tydict, Ints.tydict,
      Fixed_Size_BitVectors.tydict]
    val tmdict = union_dicts [Core.tmdict, Ints.tmdict,
      Fixed_Size_BitVectors.tmdict, BV_extension_tmdict]
    val metadata = union_metadata [Core.metadata, Ints.metadata,
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

  structure QF_S = Strings_Ints
  structure QF_SLIA = Strings_Ints
  structure QF_SNIA = Strings_Ints
  (* The FP logic packets all include the complete FloatingPoint theory.
     The names carrying an A prefix additionally include ArraysEx; UF and
     LRA only constrain the fragment and add no symbols beyond FP_Core. *)
  structure FP = FP_Core
  structure FPLRA = FP_Core
  structure BVFP = FP_Core
  structure BVFPLRA = FP_Core
  structure UFFP = FP_Core
  structure UFBVFP = FP_Core
  structure ABVFP = FP_Arrays
  structure ABVFPLRA = FP_Arrays
  structure AUFBVFP = FP_Arrays

  structure QF_FP = FP_Core
  structure QF_FPLRA = FP_Core
  structure QF_FPBV = FP_Core
  structure QF_BVFP = FP_Core
  structure QF_BVFPLRA = FP_Core
  structure QF_UFFP = FP_Core
  structure QF_UFBVFP = FP_Core
  structure QF_ABVFP = FP_Arrays
  structure QF_ABVFPLRA = FP_Arrays
  structure QF_AUFBVFP = FP_Arrays

  structure ALIA = AUFLIA
  structure ANIA = AUFLIA
  structure ALIRA = AUFLIRA
  structure ANIRA = AUFNIRA
  structure BV = QF_BV
  structure LIA = QF_IDL
  structure NIA = QF_IDL
  structure NRA = LRA
  structure UF = QF_UF
  structure UFBV = QF_UFBV
  structure UFIDL = QF_UFIDL
  structure UFLIA = QF_UFLIA
  structure UFNRA = QF_UFNRA
  structure QF_ALIA = QF_AUFLIA
  structure QF_ANIA = QF_AUFLIA
  structure QF_AUFNIA = QF_AUFLIA
  structure QF_ALRA = AUFLIRA
  structure QF_ANRA = AUFNIRA
  structure QF_AUFLIRA = AUFLIRA
  structure QF_AUFNIRA = AUFNIRA

  structure QF_LIRA =
  struct
    val tydict = union_dicts [Core.tydict, Reals_Ints.tydict]
    val tmdict = union_dicts [Core.tmdict, Reals_Ints.tmdict]
    val metadata = union_metadata [Core.metadata, Reals_Ints.metadata]
  end

  structure QF_NIRA = QF_LIRA
  structure QF_UFLIRA = QF_LIRA
  structure QF_UFNIRA = QF_LIRA

  structure QF_DT = QF_UF
  structure QF_UFDT = QF_UF
  structure QF_UFDTLIA = QF_UFLIA
  structure QF_UFDTLIRA = QF_UFLIRA
  structure QF_UFDTNIA = QF_UFLIA
  structure UFDT = UF
  structure UFDTLIA = UFLIA
  structure UFDTLIRA = QF_UFLIRA
  structure UFDTNIA = UFNIA
  structure UFDTNIRA = QF_UFNIRA
  structure AUFDTLIA = AUFLIA
  structure AUFDTLIRA = AUFLIRA
  structure AUFDTNIRA = AUFNIRA
  structure UFBVDT = UFBV
  structure AUFBVDT = QF_AUFBV
  structure AUFBVDTLIA = QF_AUFBV
  structure AUFBVDTNIA = QF_AUFBV

  structure AUFBVDTNIRA =
  struct
    val tydict = union_dicts [Core.tydict, Reals_Ints.tydict,
      Fixed_Size_BitVectors.tydict, ArraysEx.tydict]
    val tmdict = union_dicts [Core.tmdict, Reals_Ints.tmdict,
      Fixed_Size_BitVectors.tmdict, ArraysEx.tmdict, BV_extension_tmdict]
    val metadata = union_metadata [Core.metadata, Reals_Ints.metadata,
      Fixed_Size_BitVectors.metadata, ArraysEx.metadata,
      BV_extension_metadata]
  end

  (* structural term/type helpers shared via Library (see Library.sml) *)
  val type_contains = Library.type_contains
  val type_contains_int = Library.type_contains_int
  val type_contains_real = Library.type_contains_real
  val type_contains_word = Library.type_contains_word
  val type_contains_string = Library.type_contains_string
  val type_contains_native_string = Library.type_contains_native_string
  val smt_string_ty =
    Type.mk_thy_type {Thy = "smtstring", Tyop = "smtstr", Args = []}
  val reglan_ty =
    Type.mk_thy_type {Thy = "smtstring", Tyop = "reglan", Args = []}
  val same_const = Library.same_const
  val subterms = Library.subterms
  val has_quantifier = Library.has_quantifier

  fun is_numeric_literal tm =
    Lib.can intSyntax.int_of_term tm orelse
    Lib.can realSyntax.int_of_term tm

  fun is_nonlinear_product tm =
    let val (rator, rands) = boolSyntax.strip_comb tm
    in
      (same_const intSyntax.mult_tm rator orelse
       same_const realSyntax.mult_tm rator) andalso
      (case rands of
         [x, y] => not (is_numeric_literal x orelse is_numeric_literal y)
       (* 'subterms' enumerates every rator application, so a partial
          application such as (mult_tm $ x) shows up here with a single
          operand.  It is not itself a product occurrence: the saturated
          application is present separately in the 'subterms' list and is
          judged by the [x, y] branch.  Classifying partial applications
          as nonlinear would flag every multiplication, including the
          linear (2 * x) and the ground literal product (2 * 3). *)
       | _ => false)
    end
    handle Feedback.HOL_ERR _ => false

  datatype arith_fragment = NO_ARITH | LINEAR | NONLINEAR | DIFFERENCE

  type surface_flags = {
    arrow_sort_used : bool,
    lambda_used : bool,
    apply_operator_used : bool,
    partial_application_used : bool
  }

  val empty_surface_flags : surface_flags = {
    arrow_sort_used = false,
    lambda_used = false,
    apply_operator_used = false,
    partial_application_used = false
  }

  type logic_fragment = {
    quantifiers : bool,
    uninterpreted : bool,
    arrays : bool,
    arith : arith_fragment,
    ints : bool,
    reals : bool,
    bitvectors : bool,
    strings : bool,
    floatingpoint : bool,
    datatypes : bool,
    higher_order : bool
  }

  fun logic_stem logic =
    if String.isPrefix "QF_" logic then
      String.extract (logic, 3, NONE)
    else
      logic

  fun arith_fragment_of_stem stem =
    if String.isSuffix "IDL" stem orelse String.isSuffix "RDL" stem then
      DIFFERENCE
    else if String.isSuffix "LIA" stem orelse
            String.isSuffix "LRA" stem orelse
            String.isSuffix "LIRA" stem then
      LINEAR
    else if String.isSuffix "NIA" stem orelse
            String.isSuffix "NRA" stem orelse
            String.isSuffix "NIRA" stem then
      NONLINEAR
    else
      NO_ARITH

  fun logic_fragment_of_logic "ALL" = {
      quantifiers = true, uninterpreted = true, arrays = true,
      arith = NONLINEAR, ints = true, reals = true, bitvectors = true,
      strings = true, floatingpoint = true, datatypes = true,
      higher_order = true
    }
    | logic_fragment_of_logic logic =
    if String.isPrefix "HO_" logic then
      let
        val {quantifiers, uninterpreted, arrays, arith, ints, reals,
          bitvectors, strings, floatingpoint, datatypes, ...} =
          logic_fragment_of_logic (String.extract (logic, 3, NONE))
      in {
        quantifiers = quantifiers,
        uninterpreted = uninterpreted,
        arrays = arrays,
        arith = arith,
        ints = ints,
        reals = reals,
        bitvectors = bitvectors,
        strings = strings,
        floatingpoint = floatingpoint,
        datatypes = datatypes,
        higher_order = true
      } end
    else
      let
        val stem = logic_stem logic
        val arith = arith_fragment_of_stem stem
        val strings = String.isSubstring "S" stem
        val floatingpoint = String.isSubstring "FP" stem
        val datatypes = String.isSubstring "DT" stem
        val bitvectors = String.isSubstring "BV" stem orelse floatingpoint
        val ints =
          strings orelse floatingpoint orelse
          bitvectors orelse
          String.isSuffix "IDL" stem orelse
          String.isSuffix "LIA" stem orelse
          String.isSuffix "NIA" stem orelse
          String.isSuffix "LIRA" stem orelse
          String.isSuffix "NIRA" stem
        val reals =
          floatingpoint orelse
          String.isSuffix "RDL" stem orelse
          String.isSuffix "LRA" stem orelse
          String.isSuffix "NRA" stem orelse
          String.isSuffix "LIRA" stem orelse
          String.isSuffix "NIRA" stem
      in {
        quantifiers = not (String.isPrefix "QF_" logic),
        uninterpreted = String.isSubstring "UF" stem,
        arrays = String.isPrefix "A" stem,
        arith = arith,
        ints = ints,
        reals = reals,
        bitvectors = bitvectors,
        strings = strings,
        floatingpoint = floatingpoint,
        datatypes = datatypes,
        higher_order = false
      } end

  fun is_linear_arith_logic logic =
    case #arith (logic_fragment_of_logic logic) of
      LINEAR => true
    | DIFFERENCE => true
    | _ => false

  fun term_type_contains pred tm = type_contains pred (Term.type_of tm)

  fun symbol_name tm =
    let val (rator, _) = boolSyntax.strip_comb tm
    in
      if Term.is_var rator then SOME (Lib.fst (Term.dest_var rator))
      else if Term.is_const rator then
        SOME (#Name (Term.dest_thy_const rator))
      else NONE
    end
    handle Feedback.HOL_ERR _ => NONE

  fun symbol_name_is_prefix prefix tm =
    case symbol_name tm of
      SOME name => String.isPrefix prefix name
    | NONE => false

  (* String operators are genuine theory constants.  Other prefix tests below
     remain for parser encodings whose operators are intentionally variables. *)
  fun term_mentions_smtstring_theory tm =
    case Lib.total Term.dest_thy_const
      (Lib.fst (boolSyntax.strip_comb tm)) of
      SOME {Thy, ...} => Thy = "smtstring" orelse Thy = "smtstringz3"
    | NONE => false

  fun term_mentions_reglan tm =
    term_type_contains
      (type_contains (fn ty => Type.compare (ty, reglan_ty) = EQUAL)) tm
    orelse term_mentions_smtstring_theory tm

  fun term_mentions_z3_sequence_set_bag tm =
    symbol_name_is_prefix "smtlib_seq_" tm orelse
    symbol_name_is_prefix "smtlib_set_" tm orelse
    symbol_name_is_prefix "smtlib_bag_" tm

  fun type_is_smtfloat ty =
    let val {Thy, Tyop, ...} = Type.dest_thy_type ty
    in
      Thy = "smtfloat" andalso
      (Tyop = "smtfp" orelse Tyop = "smt_rounding")
    end
    handle Feedback.HOL_ERR _ => false

  fun term_mentions_smtfloat_theory tm =
    case Lib.total Term.dest_thy_const
      (Lib.fst (boolSyntax.strip_comb tm)) of
      SOME {Thy, ...} => Thy = "smtfloat"
    | NONE => false

  fun term_mentions_floatingpoint tm =
    term_type_contains type_is_smtfloat tm orelse
    term_mentions_smtfloat_theory tm

  fun free_datatype_tyinfo tyinfo =
    not (List.null (TypeBasePure.constructors_of tyinfo)) andalso
    Lib.can TypeBasePure.nchotomy_of tyinfo andalso
    Lib.can TypeBasePure.case_def_of tyinfo andalso
    Lib.can TypeBasePure.induction_of tyinfo

  fun type_is_builtin_sort ty =
    Type.compare (ty, Type.bool) = EQUAL orelse
    Type.compare (ty, numSyntax.num) = EQUAL orelse
    Type.compare (ty, intSyntax.int_ty) = EQUAL orelse
    Type.compare (ty, realSyntax.real_ty) = EQUAL orelse
    Type.compare (ty, stringSyntax.string_ty) = EQUAL orelse
    Type.compare (ty, smt_string_ty) = EQUAL orelse
    Type.compare (ty, reglan_ty) = EQUAL orelse
    type_is_smtfloat ty orelse
    Lib.can fcpSyntax.dest_numeric_type ty orelse
    (case Lib.total Type.dest_type ty of
       SOME ("itself", [_]) => true
     | _ => false) orelse
    Lib.can Type.dom_rng ty orelse
    Lib.can wordsSyntax.dest_word_type ty

  fun type_is_typebase_datatype ty =
    not (Type.is_vartype ty) andalso
    not (type_is_builtin_sort ty) andalso
    (case TypeBase.fetch ty of
       SOME tyinfo => free_datatype_tyinfo tyinfo
     | NONE => false)
    handle Feedback.HOL_ERR _ => false

  fun type_is_native_datatype_sort ty =
    Type.compare (ty, oneSyntax.one_ty) = EQUAL orelse
    (not (type_contains_native_string ty) andalso
     Lib.can listSyntax.dest_list_type ty)

  fun type_is_datatype_sort ty =
    (Type.is_vartype ty andalso
     String.isPrefix "'smtlib_dt_" (Type.dest_vartype ty)) orelse
    type_is_native_datatype_sort ty orelse
    type_is_typebase_datatype ty

  fun term_mentions_datatype_sort tm =
    term_type_contains type_is_datatype_sort tm

  (* Core.distinct is represented by HOL's ALL_DISTINCT over an internal list.
     The list is an encoding detail, not an SMT datatype sort.  Inspect the
     encoded elements, but do not classify the wrapper list itself.  Likewise,
     the payload of SmtStr is the private representation of SMT String, not a
     user-visible SMT datatype. *)
  fun assertion_mentions_datatype_sort tm =
    let
      fun is_smtstr_value tm =
        case boolSyntax.strip_comb tm of
          (rator, [_]) =>
            (case Lib.total Term.dest_thy_const rator of
               SOME {Thy, Name, ...} =>
                 Thy = "smtstring" andalso Name = "SmtStr"
             | NONE => false)
        | _ => false

      fun walk tm =
        if is_smtstr_value tm then false
        else if listSyntax.is_all_distinct tm then
          let
            val (elements, _) =
              listSyntax.dest_list (listSyntax.dest_all_distinct tm)
          in
            List.exists walk elements
          end
        else
          term_mentions_datatype_sort tm orelse
          (let val (rator, rand) = Term.dest_comb tm
           in walk rator orelse walk rand end
           handle Feedback.HOL_ERR _ =>
             (let val (_, body) = Term.dest_abs tm
              in walk body end
              handle Feedback.HOL_ERR _ => false))
    in
      walk tm
    end

  fun term_mentions_string_theory tm =
    term_type_contains type_contains_string tm
    orelse term_mentions_reglan tm
    orelse term_mentions_smtstring_theory tm

  (* Unlike the string and floating-point theories, no bitvector symbol is
     parsed into an abstract constant, so there is no bare-name rung here: the
     SMT-LIB bitvector operators all become `wordsSyntax` constants, which this
     exemption never sees.  A bare "bv" prefix would only ever match a user
     symbol that happens to be named `bvar`, `bvec`, ... *)
  fun term_mentions_bitvector_theory tm =
    term_type_contains type_contains_word tm
    orelse symbol_name_is_prefix "smtlib_bv" tm

  fun type_contains_free_sort ty =
    type_contains
      (fn ty =>
        Type.is_vartype ty andalso
        let val name = Type.dest_vartype ty
        in
          not (String.isPrefix "'smtlib_RegLan" name) andalso
          not (String.isPrefix "'smtlib_dt_" name)
        end)
      ty

  fun is_uninterpreted_operator_application tm =
    let val (rator, rands) = boolSyntax.strip_comb tm
    in Term.is_var rator andalso not (List.null rands) end
    handle Feedback.HOL_ERR _ => false

  fun is_arith_relation tm =
    let
      val (rator, rands) = boolSyntax.strip_comb tm
      fun rel r =
        same_const intSyntax.leq_tm r orelse
        same_const intSyntax.less_tm r orelse
        same_const intSyntax.geq_tm r orelse
        same_const intSyntax.greater_tm r orelse
        same_const realSyntax.leq_tm r orelse
        same_const realSyntax.less_tm r orelse
        same_const realSyntax.geq_tm r orelse
        same_const realSyntax.greater_tm r
    in
      if rel rator andalso List.length rands = 2 then
        SOME rands
      else
        let val (lhs, rhs) = boolSyntax.dest_eq tm
        in
          if term_type_contains type_contains_int lhs orelse
             term_type_contains type_contains_real lhs orelse
             term_type_contains type_contains_int rhs orelse
             term_type_contains type_contains_real rhs then
            SOME [lhs, rhs]
          else
            NONE
        end
        handle Feedback.HOL_ERR _ => NONE
    end
    handle Feedback.HOL_ERR _ => NONE

  fun is_clear_non_difference_sum tm =
    let val (rator, rands) = boolSyntax.strip_comb tm
    in
      (same_const intSyntax.plus_tm rator orelse
       same_const realSyntax.plus_tm rator) andalso
      (case rands of
         [x, y] => not (is_numeric_literal x orelse is_numeric_literal y)
       | _ => false)
    end
    handle Feedback.HOL_ERR _ => false

  fun is_clear_difference_logic_atom_violation tm =
    case is_arith_relation tm of
      SOME sides =>
        List.exists
          (fn side => List.exists is_clear_non_difference_sum (subterms side))
          sides
    | NONE => false

  fun term_has_word_subterm tm =
    List.exists (term_type_contains type_contains_word) (subterms tm)

  fun is_bv_logic_pure_int_atom tm =
    case is_arith_relation tm of
      SOME _ => not (term_has_word_subterm tm)
    | NONE => false

  fun checked_replay_gap_message logic family missing_feature case_ids =
    "checked Z3_TAC replay for " ^ family ^
    " is not implemented for logic " ^ logic ^
    "; missing feature: " ^ missing_feature ^
    "; failing case IDs: " ^ String.concatWith ", " case_ids

  fun checked_replay_unsupported_diagnostic logic assertions =
    let
      val all_subterms = List.concat (List.map subterms assertions)
      fun some_subterm p = List.exists p all_subterms
    in
      if some_subterm term_mentions_z3_sequence_set_bag then
        SOME (checked_replay_gap_message logic "Z3 sequence/set/bag extensions"
          "theory:Z3_Extensions:seq-set-bag:checked-replay"
          ["theory:Z3_Extensions:seq", "theory:Z3_Extensions:set",
           "theory:Z3_Extensions:bag", "proof-rule:th-lemma-seq"])
      else NONE
    end

  fun fragment_violation_diagnostic logic
      (surface_flags : surface_flags) assertions =
    let
      val fragment = logic_fragment_of_logic logic
      val all_subterms = List.concat (List.map subterms assertions)
      fun some_subterm p = List.exists p all_subterms
      val has_int = some_subterm (term_type_contains type_contains_int)
      val has_real = some_subterm (term_type_contains type_contains_real)
      val has_word = some_subterm (term_type_contains type_contains_word)
      val has_string = some_subterm (term_type_contains type_contains_string)
      val has_datatype =
        List.exists assertion_mentions_datatype_sort assertions
      fun qf_violation () =
        not (#quantifiers fragment) andalso List.exists has_quantifier assertions
      fun nonlinear_violation () =
        is_linear_arith_logic logic andalso some_subterm is_nonlinear_product
      fun difference_violation () =
        #arith fragment = DIFFERENCE andalso
        some_subterm is_clear_difference_logic_atom_violation
      fun uf_operator_violation () =
        not (#uninterpreted fragment) andalso not (#arrays fragment) andalso
        some_subterm
          (fn tm =>
            is_uninterpreted_operator_application tm andalso
            not (not (#floatingpoint fragment) andalso
                 (#strings fragment orelse #bitvectors fragment) andalso
                 symbol_name_is_prefix "smtlib_" tm) andalso
            not (#floatingpoint fragment andalso
                 term_mentions_floatingpoint tm) andalso
            not (#strings fragment andalso term_mentions_string_theory tm)
            andalso
            not (#bitvectors fragment andalso
                 term_mentions_bitvector_theory tm))
      fun bv_int_atom_violation () =
        logic <> "ALL" andalso #bitvectors fragment andalso
        #arith fragment = NO_ARITH andalso has_int andalso
        some_subterm is_bv_logic_pure_int_atom
      fun int_sort_violation () =
        not (#ints fragment) andalso has_int
      fun real_sort_violation () =
        not (#reals fragment) andalso has_real
      fun bitvector_sort_violation () =
        not (#bitvectors fragment) andalso has_word
      fun string_sort_violation () =
        not (#strings fragment) andalso
        (has_string orelse some_subterm term_mentions_reglan)
      fun floatingpoint_sort_violation () =
        not (#floatingpoint fragment) andalso
        some_subterm term_mentions_floatingpoint
      fun datatype_sort_violation () =
        not (#datatypes fragment) andalso has_datatype
      fun free_sort_violation () =
        not (#uninterpreted fragment) andalso not (#arrays fragment) andalso
        some_subterm (term_type_contains type_contains_free_sort)
      fun higher_order_violation () =
        if #higher_order fragment then NONE
        else if #partial_application_used surface_flags then
          SOME "partial application"
        else if #apply_operator_used surface_flags then
          SOME "apply operator"
        else if #lambda_used surface_flags then
          SOME "lambda"
        else if #arrow_sort_used surface_flags then
          SOME "arrow sort"
        else NONE
    in
      case higher_order_violation () of
        SOME kind =>
          SOME ("higher-order construct (" ^ kind ^
            ") is outside logic fragment " ^ logic)
      | NONE => if qf_violation () then
        SOME ("quantified formula is outside logic fragment " ^ logic)
      else if nonlinear_violation () then
        SOME ("nonlinear arithmetic product is outside logic fragment " ^
              logic)
      else if difference_violation () then
        SOME ("difference logic atom shape is outside logic fragment " ^
              logic)
      else if uf_operator_violation () then
        SOME ("uninterpreted function application is outside logic fragment " ^
              logic)
      else if bv_int_atom_violation () then
        SOME ("integer atom is outside bit-vector logic fragment " ^
              logic)
      else if int_sort_violation () then
        SOME ("integer term sort is outside logic fragment " ^ logic)
      else if real_sort_violation () then
        SOME ("real term sort is outside logic fragment " ^ logic)
      else if bitvector_sort_violation () then
        SOME ("bit-vector term sort is outside logic fragment " ^ logic)
      else if string_sort_violation () then
        SOME ("string term sort is outside logic fragment " ^ logic)
      else if floatingpoint_sort_violation () then
        SOME ("floating-point term sort is outside logic fragment " ^ logic)
      else if datatype_sort_violation () then
        SOME ("datatype sort is outside logic fragment " ^ logic)
      else if free_sort_violation () then
        SOME ("free sort is outside logic fragment " ^ logic)
      else
        NONE
    end

  (* returns a type dictionary and a term dictionary that can be used
     to parse types/terms of the given SMT-LIB 2 logic *)
  (* SMT-LIB defines no official higher-order logic names.  cvc5's
     non-official `HO_` prefix adds the official HO-Core theory to the
     corresponding base packet (ALL already includes HO-Core, so the union
     is idempotent there). *)
  fun parsedicts_of_logic (logic : string) =
    if String.isPrefix "HO_" logic then
      let
        val (tydict, tmdict) =
          parsedicts_of_logic (String.extract (logic, 3, NONE))
          handle Feedback.HOL_ERR _ =>
            raise ERR "parsedicts_of_logic" ("unknown logic '" ^ logic ^ "'")
      in
        (union_dicts [tydict, HO_Core.tydict],
         union_dicts [tmdict, HO_Core.tmdict])
      end
    else
    case logic of
      "ALL" =>
      (ALL.tydict, ALL.tmdict)
    | "QF_S" =>
      (QF_S.tydict, QF_S.tmdict)
    | "QF_SLIA" =>
      (QF_SLIA.tydict, QF_SLIA.tmdict)
    | "QF_SNIA" =>
      (QF_SNIA.tydict, QF_SNIA.tmdict)
    | "FP" =>
      (FP.tydict, FP.tmdict)
    | "FPLRA" =>
      (FPLRA.tydict, FPLRA.tmdict)
    | "BVFP" =>
      (BVFP.tydict, BVFP.tmdict)
    | "BVFPLRA" =>
      (BVFPLRA.tydict, BVFPLRA.tmdict)
    | "UFFP" =>
      (UFFP.tydict, UFFP.tmdict)
    | "UFBVFP" =>
      (UFBVFP.tydict, UFBVFP.tmdict)
    | "ABVFP" =>
      (ABVFP.tydict, ABVFP.tmdict)
    | "ABVFPLRA" =>
      (ABVFPLRA.tydict, ABVFPLRA.tmdict)
    | "AUFBVFP" =>
      (AUFBVFP.tydict, AUFBVFP.tmdict)
    | "QF_FP" =>
      (QF_FP.tydict, QF_FP.tmdict)
    | "QF_FPLRA" =>
      (QF_FPLRA.tydict, QF_FPLRA.tmdict)
    | "QF_FPBV" =>
      (QF_FPBV.tydict, QF_FPBV.tmdict)
    | "QF_BVFP" =>
      (QF_BVFP.tydict, QF_BVFP.tmdict)
    | "QF_BVFPLRA" =>
      (QF_BVFPLRA.tydict, QF_BVFPLRA.tmdict)
    | "QF_UFFP" =>
      (QF_UFFP.tydict, QF_UFFP.tmdict)
    | "QF_UFBVFP" =>
      (QF_UFBVFP.tydict, QF_UFBVFP.tmdict)
    | "QF_ABVFP" =>
      (QF_ABVFP.tydict, QF_ABVFP.tmdict)
    | "QF_ABVFPLRA" =>
      (QF_ABVFPLRA.tydict, QF_ABVFPLRA.tmdict)
    | "QF_AUFBVFP" =>
      (QF_AUFBVFP.tydict, QF_AUFBVFP.tmdict)
    | "ALIA" =>
      (ALIA.tydict, ALIA.tmdict)
    | "ALIRA" =>
      (ALIRA.tydict, ALIRA.tmdict)
    | "ANIA" =>
      (ANIA.tydict, ANIA.tmdict)
    | "ANIRA" =>
      (ANIRA.tydict, ANIRA.tmdict)
    | "AUFLIA" =>
      (AUFLIA.tydict, AUFLIA.tmdict)
    | "AUFLIRA" =>
      (AUFLIRA.tydict, AUFLIRA.tmdict)
    | "AUFNIRA" =>
      (AUFNIRA.tydict, AUFNIRA.tmdict)
    | "AUFDTLIA" =>
      (AUFDTLIA.tydict, AUFDTLIA.tmdict)
    | "AUFDTLIRA" =>
      (AUFDTLIRA.tydict, AUFDTLIRA.tmdict)
    | "AUFDTNIRA" =>
      (AUFDTNIRA.tydict, AUFDTNIRA.tmdict)
    | "AUFBVDT" =>
      (AUFBVDT.tydict, AUFBVDT.tmdict)
    | "AUFBVDTLIA" =>
      (AUFBVDTLIA.tydict, AUFBVDTLIA.tmdict)
    | "AUFBVDTNIA" =>
      (AUFBVDTNIA.tydict, AUFBVDTNIA.tmdict)
    | "AUFBVDTNIRA" =>
      (AUFBVDTNIRA.tydict, AUFBVDTNIRA.tmdict)
    | "BV" =>
      (BV.tydict, BV.tmdict)
    | "LIA" =>
      (LIA.tydict, LIA.tmdict)
    | "LRA" =>
      (LRA.tydict, LRA.tmdict)
    | "NIA" =>
      (NIA.tydict, NIA.tmdict)
    | "NRA" =>
      (NRA.tydict, NRA.tmdict)
    | "UF" =>
      (UF.tydict, UF.tmdict)
    | "UFBV" =>
      (UFBV.tydict, UFBV.tmdict)
    | "UFBVDT" =>
      (UFBVDT.tydict, UFBVDT.tmdict)
    | "UFIDL" =>
      (UFIDL.tydict, UFIDL.tmdict)
    | "UFDT" =>
      (UFDT.tydict, UFDT.tmdict)
    | "UFDTLIA" =>
      (UFDTLIA.tydict, UFDTLIA.tmdict)
    | "UFDTLIRA" =>
      (UFDTLIRA.tydict, UFDTLIRA.tmdict)
    | "UFDTNIA" =>
      (UFDTNIA.tydict, UFDTNIA.tmdict)
    | "UFDTNIRA" =>
      (UFDTNIRA.tydict, UFDTNIRA.tmdict)
    | "UFLIA" =>
      (UFLIA.tydict, UFLIA.tmdict)
    | "QF_ABV" =>
      (QF_ABV.tydict, QF_ABV.tmdict)
    | "QF_ALIA" =>
      (QF_ALIA.tydict, QF_ALIA.tmdict)
    | "QF_ALRA" =>
      (QF_ALRA.tydict, QF_ALRA.tmdict)
    | "QF_ANIA" =>
      (QF_ANIA.tydict, QF_ANIA.tmdict)
    | "QF_ANRA" =>
      (QF_ANRA.tydict, QF_ANRA.tmdict)
    | "QF_AUFBV" =>
      (QF_AUFBV.tydict, QF_AUFBV.tmdict)
    | "QF_AUFLIA" =>
      (QF_AUFLIA.tydict, QF_AUFLIA.tmdict)
    | "QF_AUFLIRA" =>
      (QF_AUFLIRA.tydict, QF_AUFLIRA.tmdict)
    | "QF_AUFNIA" =>
      (QF_AUFNIA.tydict, QF_AUFNIA.tmdict)
    | "QF_AUFNIRA" =>
      (QF_AUFNIRA.tydict, QF_AUFNIRA.tmdict)
    | "QF_AX" =>
      (QF_AX.tydict, QF_AX.tmdict)
    | "QF_BV" =>
      (QF_BV.tydict, QF_BV.tmdict)
    | "QF_DT" =>
      (QF_DT.tydict, QF_DT.tmdict)
    | "QF_IDL" =>
      (QF_IDL.tydict, QF_IDL.tmdict)
    | "QF_LIA" =>
      (QF_LIA.tydict, QF_LIA.tmdict)
    | "QF_LIRA" =>
      (QF_LIRA.tydict, QF_LIRA.tmdict)
    | "QF_LRA" =>
      (QF_LRA.tydict, QF_LRA.tmdict)
    | "QF_NIA" =>
      (QF_NIA.tydict, QF_NIA.tmdict)
    | "QF_NIRA" =>
      (QF_NIRA.tydict, QF_NIRA.tmdict)
    | "QF_NRA" =>
      (QF_NRA.tydict, QF_NRA.tmdict)
    | "QF_RDL" =>
      (QF_RDL.tydict, QF_RDL.tmdict)
    | "QF_UF" =>
      (QF_UF.tydict, QF_UF.tmdict)
    | "QF_UFBV" =>
      (QF_UFBV.tydict, QF_UFBV.tmdict)
    | "QF_UFDT" =>
      (QF_UFDT.tydict, QF_UFDT.tmdict)
    | "QF_UFDTLIA" =>
      (QF_UFDTLIA.tydict, QF_UFDTLIA.tmdict)
    | "QF_UFDTLIRA" =>
      (QF_UFDTLIRA.tydict, QF_UFDTLIRA.tmdict)
    | "QF_UFDTNIA" =>
      (QF_UFDTNIA.tydict, QF_UFDTNIA.tmdict)
    | "QF_UFIDL" =>
      (QF_UFIDL.tydict, QF_UFIDL.tmdict)
    | "QF_UFLIA" =>
      (QF_UFLIA.tydict, QF_UFLIA.tmdict)
    | "QF_UFLIRA" =>
      (QF_UFLIRA.tydict, QF_UFLIRA.tmdict)
    | "QF_UFLRA" =>
      (QF_UFLRA.tydict, QF_UFLRA.tmdict)
    | "QF_UFNIRA" =>
      (QF_UFNIRA.tydict, QF_UFNIRA.tmdict)
    | "QF_UFNRA" =>
      (QF_UFNRA.tydict, QF_UFNRA.tmdict)
    | "UFLRA" =>
      (UFLRA.tydict, UFLRA.tmdict)
    | "UFNIA" =>
      (UFNIA.tydict, UFNIA.tmdict)
    | "UFNRA" =>
      (UFNRA.tydict, UFNRA.tmdict)
    | _ =>
      raise ERR "parsedicts_of_logic" ("unknown logic '" ^ logic ^ "'")

  (* Extends the standard logic packet with entries for exactly one solver
     dialect.  Multiple registrations compose, so the theory tasks can add
     solver-neutral Seq, cvc5 Set/Bag, and Z3 Set entries independently. *)
  fun parsedicts_of_solver_logic solver logic =
    let
      val (base_tydict, base_tmdict) = parsedicts_of_logic logic
      val registrations = List.filter
        (fn ({solver = registered_solver, logic = registered_logic, ...}
             : dialect_dictionary_registration) =>
          solver = registered_solver andalso logic = registered_logic)
        (!dialect_dictionary_registrations)
      fun add ({dictionaries = (tydict, tmdict), ...}
               : dialect_dictionary_registration) (tys, tms) =
        (union_dicts [tys, tydict], union_dicts [tms, tmdict])
    in
      List.foldl (fn (registration, dictionaries) =>
        add registration dictionaries) (base_tydict, base_tmdict) registrations
    end

  (* The source parser is intentionally usable without a solver target for
     corpus/typecheck inspection.  Such a caller gets the union of the two
     non-conflicting dialect dictionaries; solver-facing callers must use the
     selector above and therefore retain dialect rejection. *)
  fun parsedicts_of_any_solver_logic logic =
    let
      val z3 = parsedicts_of_solver_logic "Z3" logic
      val cvc5 = parsedicts_of_solver_logic "cvc5" logic
    in
      (union_dicts [Lib.fst z3, Lib.fst cvc5],
       union_dicts [Lib.snd z3, Lib.snd cvc5])
    end

  val set_dialect_logics = ["ALL", "HO_ALL"]

  val _ = List.app (fn logic =>
    register_dialect_dictionary {
      solver = "Z3", logic = logic,
      dictionaries = (Z3_Set.tydict, Z3_Set.tmdict)}) set_dialect_logics

  val _ = List.app (fn logic =>
    register_dialect_dictionary {
      solver = "Z3", logic = logic,
      dictionaries = (Z3_Seq.tydict, Z3_Seq.tmdict)}) set_dialect_logics

  val _ = List.app (fn logic =>
    register_dialect_dictionary {
      solver = "cvc5", logic = logic,
      dictionaries = (CVC5_Seq.tydict, CVC5_Seq.tmdict)}) set_dialect_logics

  val _ = List.app (fn logic =>
    register_dialect_dictionary {
      solver = "cvc5", logic = logic,
      dictionaries = (CVC5_Set.tydict, CVC5_Set.tmdict)}) set_dialect_logics

  val _ = List.app (fn logic =>
    register_dialect_dictionary {
      solver = "cvc5", logic = logic,
      dictionaries = (CVC5_Bag.tydict, CVC5_Bag.tmdict)}) set_dialect_logics

  val _ = default_dialect_dictionary_registrations :=
    !dialect_dictionary_registrations

  (* returns the symbol metadata used to build the parse dictionaries of
     the given SMT-LIB 2 logic *)
  fun metadata_of_logic (logic : string) =
    if String.isPrefix "HO_" logic then
      let
        val metadata =
          metadata_of_logic (String.extract (logic, 3, NONE))
          handle Feedback.HOL_ERR _ =>
            raise ERR "metadata_of_logic" ("unknown logic '" ^ logic ^ "'")
      in
        union_metadata [metadata, HO_Core.metadata]
      end
    else
    case logic of
      "ALL" => ALL.metadata
    | "QF_S" => QF_S.metadata
    | "QF_SLIA" => QF_SLIA.metadata
    | "QF_SNIA" => QF_SNIA.metadata
    | "FP" => FP.metadata
    | "FPLRA" => FPLRA.metadata
    | "BVFP" => BVFP.metadata
    | "BVFPLRA" => BVFPLRA.metadata
    | "UFFP" => UFFP.metadata
    | "UFBVFP" => UFBVFP.metadata
    | "ABVFP" => ABVFP.metadata
    | "ABVFPLRA" => ABVFPLRA.metadata
    | "AUFBVFP" => AUFBVFP.metadata
    | "QF_FP" => QF_FP.metadata
    | "QF_FPLRA" => QF_FPLRA.metadata
    | "QF_FPBV" => QF_FPBV.metadata
    | "QF_BVFP" => QF_BVFP.metadata
    | "QF_BVFPLRA" => QF_BVFPLRA.metadata
    | "QF_UFFP" => QF_UFFP.metadata
    | "QF_UFBVFP" => QF_UFBVFP.metadata
    | "QF_ABVFP" => QF_ABVFP.metadata
    | "QF_ABVFPLRA" => QF_ABVFPLRA.metadata
    | "QF_AUFBVFP" => QF_AUFBVFP.metadata
    | "ALIA" => ALIA.metadata
    | "ALIRA" => ALIRA.metadata
    | "ANIA" => ANIA.metadata
    | "ANIRA" => ANIRA.metadata
    | "AUFLIA" => AUFLIA.metadata
    | "AUFLIRA" => AUFLIRA.metadata
    | "AUFNIRA" => AUFNIRA.metadata
    | "AUFDTLIA" => AUFDTLIA.metadata
    | "AUFDTLIRA" => AUFDTLIRA.metadata
    | "AUFDTNIRA" => AUFDTNIRA.metadata
    | "AUFBVDT" => AUFBVDT.metadata
    | "AUFBVDTLIA" => AUFBVDTLIA.metadata
    | "AUFBVDTNIA" => AUFBVDTNIA.metadata
    | "AUFBVDTNIRA" => AUFBVDTNIRA.metadata
    | "BV" => BV.metadata
    | "LIA" => LIA.metadata
    | "LRA" => LRA.metadata
    | "NIA" => NIA.metadata
    | "NRA" => NRA.metadata
    | "UF" => UF.metadata
    | "UFBV" => UFBV.metadata
    | "UFBVDT" => UFBVDT.metadata
    | "UFIDL" => UFIDL.metadata
    | "UFDT" => UFDT.metadata
    | "UFDTLIA" => UFDTLIA.metadata
    | "UFDTLIRA" => UFDTLIRA.metadata
    | "UFDTNIA" => UFDTNIA.metadata
    | "UFDTNIRA" => UFDTNIRA.metadata
    | "UFLIA" => UFLIA.metadata
    | "QF_ABV" => QF_ABV.metadata
    | "QF_ALIA" => QF_ALIA.metadata
    | "QF_ALRA" => QF_ALRA.metadata
    | "QF_ANIA" => QF_ANIA.metadata
    | "QF_ANRA" => QF_ANRA.metadata
    | "QF_AUFBV" => QF_AUFBV.metadata
    | "QF_AUFLIA" => QF_AUFLIA.metadata
    | "QF_AUFLIRA" => QF_AUFLIRA.metadata
    | "QF_AUFNIA" => QF_AUFNIA.metadata
    | "QF_AUFNIRA" => QF_AUFNIRA.metadata
    | "QF_AX" => QF_AX.metadata
    | "QF_BV" => QF_BV.metadata
    | "QF_DT" => QF_DT.metadata
    | "QF_IDL" => QF_IDL.metadata
    | "QF_LIA" => QF_LIA.metadata
    | "QF_LIRA" => QF_LIRA.metadata
    | "QF_LRA" => QF_LRA.metadata
    | "QF_NIA" => QF_NIA.metadata
    | "QF_NIRA" => QF_NIRA.metadata
    | "QF_NRA" => QF_NRA.metadata
    | "QF_RDL" => QF_RDL.metadata
    | "QF_UF" => QF_UF.metadata
    | "QF_UFBV" => QF_UFBV.metadata
    | "QF_UFDT" => QF_UFDT.metadata
    | "QF_UFDTLIA" => QF_UFDTLIA.metadata
    | "QF_UFDTLIRA" => QF_UFDTLIRA.metadata
    | "QF_UFDTNIA" => QF_UFDTNIA.metadata
    | "QF_UFIDL" => QF_UFIDL.metadata
    | "QF_UFLIA" => QF_UFLIA.metadata
    | "QF_UFLIRA" => QF_UFLIRA.metadata
    | "QF_UFLRA" => QF_UFLRA.metadata
    | "QF_UFNIRA" => QF_UFNIRA.metadata
    | "QF_UFNRA" => QF_UFNRA.metadata
    | "UFLRA" => UFLRA.metadata
    | "UFNIA" => UFNIA.metadata
    | "UFNRA" => UFNRA.metadata
    | _ =>
      raise ERR "metadata_of_logic" ("unknown logic '" ^ logic ^ "'")

end  (* local *)

end
