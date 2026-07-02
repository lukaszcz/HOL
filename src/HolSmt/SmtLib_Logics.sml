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

  structure ALL =
  struct
    val tydict = union_dicts [Core.tydict, Ints.tydict, Reals.tydict,
      Reals_Ints.tydict, ArraysEx.tydict, Fixed_Size_BitVectors.tydict,
      FloatingPoint.tydict, UnicodeStrings.tydict, Z3_Extensions.tydict]
    val tmdict = union_dicts [Core.tmdict, Ints.tmdict, Reals.tmdict,
      Reals_Ints.tmdict, ArraysEx.tmdict, Fixed_Size_BitVectors.tmdict,
      FloatingPoint.tmdict, UnicodeStrings.tmdict, Z3_Extensions.tmdict,
      BV_extension_tmdict]
    val metadata = union_metadata [Core.metadata, Ints.metadata,
      Reals.metadata, Reals_Ints.metadata, ArraysEx.metadata,
      Fixed_Size_BitVectors.metadata, FloatingPoint.metadata,
      UnicodeStrings.metadata, Z3_Extensions.metadata, BV_extension_metadata]
  end

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
  structure QF_FP = FP_Core
  structure QF_FPBV = FP_Core
  structure QF_BVFP = FP_Core
  structure QF_UFFP = FP_Core
  structure QF_UFBVFP = FP_Core

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

  fun type_contains pred ty =
    pred ty orelse
    (let val (dom, rng) = Type.dom_rng ty
     in type_contains pred dom orelse type_contains pred rng end
     handle _ => false)

  fun type_contains_int ty =
    type_contains (fn ty => Type.compare (ty, intSyntax.int_ty) = EQUAL) ty

  fun type_contains_real ty =
    type_contains (fn ty => Type.compare (ty, realSyntax.real_ty) = EQUAL) ty

  fun type_contains_word ty =
    type_contains (Lib.can wordsSyntax.dest_word_type) ty

  fun type_contains_string ty =
    type_contains (fn ty => Type.compare (ty, stringSyntax.string_ty) = EQUAL)
      ty

  fun same_const c tm = Term.is_const tm andalso Term.same_const tm c

  fun subterms tm =
    tm ::
    (let
       val (rator, rand) = Term.dest_comb tm
     in
       subterms rator @ subterms rand
     end
     handle _ =>
       (let val (_, body) = Term.dest_abs tm
        in subterms body end
        handle _ => []))

  fun has_quantifier tm =
    boolSyntax.is_forall tm orelse boolSyntax.is_exists tm orelse
    (let
       val (rator, rand) = Term.dest_comb tm
     in
       has_quantifier rator orelse has_quantifier rand
     end
     handle _ =>
       (let val (_, body) = Term.dest_abs tm
        in has_quantifier body end
        handle _ => false))

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
       | _ => true)
    end
    handle _ => false

  fun is_linear_arith_logic logic =
    List.exists (fn linear_logic => logic = linear_logic)
      ["ALIA", "ALIRA", "AUFLIA", "AUFLIRA", "LIA", "LRA",
       "QF_ALIA", "QF_ALRA", "QF_AUFLIA", "QF_AUFLIRA",
       "QF_IDL", "QF_LIA", "QF_LIRA", "QF_LRA", "QF_RDL",
       "QF_UFIDL", "QF_UFLIA", "QF_UFLIRA", "QF_UFLRA",
       "UFIDL", "UFLIA", "UFLRA"]

  fun is_pure_uf_logic logic =
    List.exists (fn uf_logic => logic = uf_logic) ["UF", "QF_UF"]

  fun is_pure_bv_logic logic =
    List.exists (fn bv_logic => logic = bv_logic) ["BV", "UFBV"]

  fun term_type_contains pred tm = type_contains pred (Term.type_of tm)

  fun fragment_violation_diagnostic logic assertions =
    let
      val all_subterms = List.concat (List.map subterms assertions)
      fun some_subterm p = List.exists p all_subterms
      fun qf_violation () =
        String.isPrefix "QF_" logic andalso List.exists has_quantifier assertions
      fun uf_theory_violation () =
        is_pure_uf_logic logic andalso
        some_subterm (fn tm =>
          term_type_contains type_contains_int tm orelse
          term_type_contains type_contains_real tm orelse
          term_type_contains type_contains_word tm orelse
          term_type_contains type_contains_string tm)
      fun bv_theory_violation () =
        is_pure_bv_logic logic andalso
        some_subterm (term_type_contains type_contains_int) andalso
        not (some_subterm (term_type_contains type_contains_word))
    in
      if qf_violation () then
        SOME ("quantified formula is outside logic fragment " ^ logic)
      else if is_linear_arith_logic logic andalso
              some_subterm is_nonlinear_product then
        SOME ("nonlinear arithmetic product is outside logic fragment " ^
              logic)
      else if uf_theory_violation () then
        SOME ("non-UF term sort is outside logic fragment " ^ logic)
      else if bv_theory_violation () then
        SOME ("integer-only term is outside bit-vector logic fragment " ^
              logic)
      else
        NONE
    end

  (* returns a type dictionary and a term dictionary that can be used
     to parse types/terms of the given SMT-LIB 2 logic *)
  fun parsedicts_of_logic (logic : string) =
    case logic of
      "ALL" =>
      (ALL.tydict, ALL.tmdict)
    | "QF_S" =>
      (QF_S.tydict, QF_S.tmdict)
    | "QF_SLIA" =>
      (QF_SLIA.tydict, QF_SLIA.tmdict)
    | "QF_SNIA" =>
      (QF_SNIA.tydict, QF_SNIA.tmdict)
    | "QF_FP" =>
      (QF_FP.tydict, QF_FP.tmdict)
    | "QF_FPBV" =>
      (QF_FPBV.tydict, QF_FPBV.tmdict)
    | "QF_BVFP" =>
      (QF_BVFP.tydict, QF_BVFP.tmdict)
    | "QF_UFFP" =>
      (QF_UFFP.tydict, QF_UFFP.tmdict)
    | "QF_UFBVFP" =>
      (QF_UFBVFP.tydict, QF_UFBVFP.tmdict)
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
    | "UFIDL" =>
      (UFIDL.tydict, UFIDL.tmdict)
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

  (* returns the symbol metadata used to build the parse dictionaries of
     the given SMT-LIB 2 logic *)
  fun metadata_of_logic (logic : string) =
    case logic of
      "ALL" => ALL.metadata
    | "QF_S" => QF_S.metadata
    | "QF_SLIA" => QF_SLIA.metadata
    | "QF_SNIA" => QF_SNIA.metadata
    | "QF_FP" => QF_FP.metadata
    | "QF_FPBV" => QF_FPBV.metadata
    | "QF_BVFP" => QF_BVFP.metadata
    | "QF_UFFP" => QF_UFFP.metadata
    | "QF_UFBVFP" => QF_UFBVFP.metadata
    | "ALIA" => ALIA.metadata
    | "ALIRA" => ALIRA.metadata
    | "ANIA" => ANIA.metadata
    | "ANIRA" => ANIRA.metadata
    | "AUFLIA" => AUFLIA.metadata
    | "AUFLIRA" => AUFLIRA.metadata
    | "AUFNIRA" => AUFNIRA.metadata
    | "BV" => BV.metadata
    | "LIA" => LIA.metadata
    | "LRA" => LRA.metadata
    | "NIA" => NIA.metadata
    | "NRA" => NRA.metadata
    | "UF" => UF.metadata
    | "UFBV" => UFBV.metadata
    | "UFIDL" => UFIDL.metadata
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
