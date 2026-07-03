(* Copyright (c) 2009-2011 Tjark Weber. All rights reserved. *)

(* Translation of HOL terms into SMT-LIB 2 format *)

structure SmtLib = struct

datatype logic_features = LogicFeatures of {
  quantifiers : bool,
  uninterpreted : bool,
  arrays : bool,
  bitvectors : bool,
  integers : bool,
  reals : bool,
  strings : bool,
  nonlinear : bool
}

datatype encoding_mode =
    NativeSMTLIB
  | ConservativeEmbedding
  | Preprocessing

datatype translation_record =
    LogicSelection of {logic : string, reason : string,
                       features : logic_features}
  | TypeDeclaration of {hol_type : Type.hol_type, smt_name : string,
                        declaration : string}
  | TermDeclaration of {hol_term : Term.term, arity : int,
                        smt_name : string, domain_sorts : string list,
                        range_sort : string, declaration : string}
  | DefinitionRecord of {hol_term : Term.term, smt_name : string,
                         sort : string, definition : string}
  | EncodedSymbol of {hol_term : Term.term, smt_symbol : string,
                      arity : int}
  | HOLTheoryEncoding of {feature : string, smt_theory : string,
                          mode : encoding_mode, parse : bool,
                          typecheck : bool, translate : bool,
                          replay : bool, notes : string,
                          proof_obligation : string}

type translation = {
  logic : string,
  tydict : (Type.hol_type, string) Redblackmap.dict,
  tmdict : (Term.term * int, string) Redblackmap.dict,
  records : translation_record list
}

local

  (* For successful proof reconstruction, it is important that the
     translation implemented in SmtLib_{Theories,Logics}.sml is an
     inverse of the translation implemented in this file. *)

  val ERR = Feedback.mk_HOL_ERR "SmtLib"
  val WARNING = Feedback.HOL_WARNING "SmtLib"

  (* (HOL type, a function that maps the type to its SMT-LIB sort name) *)
  val builtin_types = List.foldl
    (fn ((ty, x), net) => TypeNet.insert (net, ty, x)) TypeNet.empty [
    (Type.bool, Lib.K "Bool"),
    (intSyntax.int_ty, Lib.K "Int"),
    (realSyntax.real_ty, Lib.K "Real"),
    (stringSyntax.string_ty, Lib.K "String"),
    (* bit-vector types *)
    (wordsSyntax.mk_word_type Type.alpha, fn ty =>
      "(_ BitVec " ^ Arbnum.toString
        (fcpSyntax.dest_numeric_type (wordsSyntax.dest_word_type ty)) ^ ")")
   ]

  val apfst_K = Lib.apfst o Lib.K

  (* returns true iff 'ty' is a word type that is not fixed-width *)
  fun is_non_numeric_word_type ty =
    not (fcpSyntax.is_numeric_type (wordsSyntax.dest_word_type ty))
      handle Feedback.HOL_ERR _ => false

  (* make sure that all word types in 't' are of fixed width; return 's' *)
  fun apfst_fixed_width s =
    Lib.apfst (fn t =>
      let
        val (domtys, rngty) = boolSyntax.strip_fun (Term.type_of t)
      in
        if List.exists is_non_numeric_word_type (rngty :: domtys) then
          raise ERR ("<builtin_symbols." ^ s ^ ">")
            "not a fixed-width word type"
        else
          s
      end)

  (* (HOL term, a function that maps a pair (rator, rands) to an
     SMT-LIB symbol and a list of remaining (still-to-be-encoded)
     argument terms) *)
  val builtin_symbols = List.foldl (Lib.uncurry Net.insert) Net.empty [
    (* Core *)
    (boolSyntax.T, apfst_K "true"),
    (boolSyntax.F, apfst_K "false"),
    (boolSyntax.negation, apfst_K "not"),
    (boolSyntax.implication, apfst_K "=>"),
    (boolSyntax.conjunction, apfst_K "and"),
    (boolSyntax.disjunction, apfst_K "or"),
    (Term.prim_mk_const {Thy="HolSmt", Name="xor"}, apfst_K "xor"),
    (boolSyntax.equality, apfst_K "="),
    (* (..., "distinct"), *)
    (boolSyntax.conditional, apfst_K "ite"),
    (* UnicodeStrings.  HOL strings are char lists; the encoding is native
       SMT-LIB String syntax with a semantic obligation recorded below. *)
    (stringSyntax.strcat_tm, apfst_K "str.++"),
    (stringSyntax.isprefix_tm, apfst_K "str.prefixof"),
    (stringSyntax.string_lt_tm, apfst_K "str.<"),
    (stringSyntax.string_le_tm, apfst_K "str.<="),
    (* Reals_Ints *)
    (* numerals (excluding 'intSyntax.negate_tm') *)
    (Term.mk_var ("x", intSyntax.int_ty), Lib.apfst (fn tm =>
      if intSyntax.is_int_literal tm andalso not (intSyntax.is_negated tm) then
        let
          val i = intSyntax.int_of_term tm
          val s = Arbint.toString (Arbint.abs i)
          val s = String.substring (s, 0, String.size s - 1)
        in
          if Arbint.< (i, Arbint.zero) then
            "(- " ^ s ^ ")"
          else
            s
        end
      else
        raise ERR "<builtin_symbols.x:int>" "not a numeral (negated?)")),
    (intSyntax.negate_tm, apfst_K "-"),
    (intSyntax.minus_tm, apfst_K "-"),
    (intSyntax.plus_tm, apfst_K "+"),
    (intSyntax.mult_tm, apfst_K "*"),
    (Term.prim_mk_const {Thy="integer", Name="ediv"}, apfst_K "div"),
    (Term.prim_mk_const {Thy="integer", Name="emod"}, apfst_K "mod"),
    (intSyntax.absval_tm, apfst_K "abs"),
    (intSyntax.leq_tm, apfst_K "<="),
    (intSyntax.less_tm, apfst_K "<"),
    (intSyntax.geq_tm, apfst_K ">="),
    (intSyntax.greater_tm, apfst_K ">"),
    (* decimals (excluding 'realSyntax.negate_tm') *)
    (Term.mk_var ("x", realSyntax.real_ty), Lib.apfst (fn tm =>
      if realSyntax.is_real_literal tm andalso not (realSyntax.is_negated tm)
          then
        let
          val i = realSyntax.int_of_term tm
          val s = Arbint.toString (Arbint.abs i)
          val s = String.substring (s, 0, String.size s - 1)
          val s = s ^ ".0"
        in
          if Arbint.< (i, Arbint.zero) then
            "(- " ^ s ^ ")"
          else
            s
        end
      else
        raise ERR "<builtin_symbols.x:real>" "not a decimal (negated?)")),
    (realSyntax.negate_tm, apfst_K "-"),
    (realSyntax.minus_tm, apfst_K "-"),
    (realSyntax.plus_tm, apfst_K "+"),
    (realSyntax.mult_tm, apfst_K "*"),
    (Term.prim_mk_const {Thy="HolSmt", Name="smt_rdiv"}, apfst_K "/"),
    (realSyntax.leq_tm, apfst_K "<="),
    (realSyntax.less_tm, apfst_K "<"),
    (realSyntax.geq_tm, apfst_K ">="),
    (realSyntax.greater_tm, apfst_K ">"),
    (intrealSyntax.real_of_int_tm, apfst_K "to_real"),
    (intrealSyntax.INT_FLOOR_tm, apfst_K "to_int"),
    (intrealSyntax.is_int_tm, apfst_K "is_int"),
    (* bit-vector constants *)
    (Term.mk_var ("x", wordsSyntax.mk_word_type Type.alpha), Lib.apfst (fn tm =>
      if wordsSyntax.is_word_literal tm then
        let
          val value = wordsSyntax.dest_word_literal tm
          val width = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of tm)
        in
          "(_ bv" ^ Arbnum.toString value ^ " " ^ Arbnum.toString width ^ ")"
        end
      else
        raise ERR "<builtin_symbols.x:'a word>" "not a word literal")),
    (wordsSyntax.word_concat_tm, fn (t, ts) =>
      SmtLib_Theories.two_args (fn (w1, w2) =>
        let
          (* make sure that the result in HOL has the expected width *)
          val dim1 = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of w1)
          val dim2 = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of w2)
          val rngty = Lib.snd (boolSyntax.strip_fun (Term.type_of t))
          val rngdim = fcpSyntax.dest_numeric_type
            (wordsSyntax.dest_word_type rngty)
          val _ = if rngdim = Arbnum.+ (dim1, dim2) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term" "word_concat: wrong result type"
              else
                ();
              raise ERR "<builtin_symbols.word_concat_tm>" "wrong result type"
            )
        in
          ("concat", ts)
        end) ts),
    (wordsSyntax.word_extract_tm, fn (t, ts) =>
      SmtLib_Theories.three_args (fn (i, j, w) =>
        let
          (* make sure that j <= i < dim(w) *)
          val i = numSyntax.dest_numeral i
          val j = numSyntax.dest_numeral j
          val dim = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of w)
          val _ = if Arbnum.<= (j, i) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term"
                  "word_extract: second index larger than first"
              else
                ();
              raise ERR "<builtin_symbols.word_extract_tm>"
                "second index larger than first"
            )
          val _ = if Arbnum.< (i, dim) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term" "word_extract: first index too large"
              else
                ();
              raise ERR "<builtin_symbols.word_extract_tm>"
                "first index too large"
            )
          (* make sure that the result in HOL has the expected width *)
          val rngty = Lib.snd (boolSyntax.strip_fun (Term.type_of t))
          val rngdim = fcpSyntax.dest_numeric_type
            (wordsSyntax.dest_word_type rngty)
          val _ = if rngdim = Arbnum.+ (Arbnum.- (i, j), Arbnum.one) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term" "word_extract: wrong result type"
              else
                ();
              raise ERR "<builtin_symbols.word_extract_tm>" "wrong result type"
            )
        in
          ("(_ extract " ^ Arbnum.toString i ^ " " ^ Arbnum.toString j ^ ")",
            [w])
        end) ts),
    (wordsSyntax.word_1comp_tm, apfst_fixed_width "bvnot"),
    (wordsSyntax.word_and_tm, apfst_fixed_width "bvand"),
    (wordsSyntax.word_or_tm, apfst_fixed_width "bvor"),
    (wordsSyntax.word_nand_tm, apfst_fixed_width "bvnand"),
    (wordsSyntax.word_nor_tm, apfst_fixed_width "bvnor"),
    (wordsSyntax.word_xor_tm, apfst_fixed_width "bvxor"),
    (wordsSyntax.word_xnor_tm, apfst_fixed_width "bvxnor"),
    (wordsSyntax.word_2comp_tm, apfst_fixed_width "bvneg"),
    (wordsSyntax.word_compare_tm, apfst_fixed_width "bvcomp"),
    (wordsSyntax.word_add_tm, apfst_fixed_width "bvadd"),
    (wordsSyntax.word_sub_tm, apfst_fixed_width "bvsub"),
    (wordsSyntax.word_mul_tm, apfst_fixed_width "bvmul"),
    (wordsSyntax.word_quot_tm, apfst_fixed_width "bvsdiv"),
    (wordsSyntax.word_rem_tm, apfst_fixed_width "bvsrem"),
    (integer_wordSyntax.word_smod_tm, apfst_fixed_width "bvsmod"),
    (wordsSyntax.word_div_tm, apfst_fixed_width "bvudiv"),
    (wordsSyntax.word_mod_tm, apfst_fixed_width "bvurem"),
    (* shift operations with two bit-vector arguments; the corresponding HOL
       shift operations that take a numeral as their second argument are not
       supported in SMT-LIB *)
    (wordsSyntax.word_lsl_bv_tm, apfst_fixed_width "bvshl"),
    (wordsSyntax.word_lsr_bv_tm, apfst_fixed_width "bvlshr"),
    (wordsSyntax.word_asr_bv_tm, apfst_fixed_width "bvashr"),
    (wordsSyntax.word_replicate_tm, fn (t, ts) =>
      SmtLib_Theories.two_args (fn (n, w) =>
        let
          val n = numSyntax.dest_numeral n
          (* make sure that the result in HOL has the expected width *)
          val dim = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of w)
          val rngty = Lib.snd (boolSyntax.strip_fun (Term.type_of t))
          val rngdim = fcpSyntax.dest_numeric_type
            (wordsSyntax.dest_word_type rngty)
          val _ = if rngdim = Arbnum.* (n, dim) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term" "word_replicate: wrong result type"
              else
                ();
              raise ERR "<builtin_symbols.word_replicate_tm>"
                "wrong result type"
            )
        in
          ("(_ repeat " ^ Arbnum.toString n ^ ")", [w])
        end) ts),
    (wordsSyntax.w2w_tm, fn (t, ts) =>
      SmtLib_Theories.one_arg (fn w =>
        let
          (* make sure that the result in HOL is at least as long as 'w' *)
          val dim = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of w)
          val rngty = Lib.snd (boolSyntax.strip_fun (Term.type_of t))
          val rngdim = fcpSyntax.dest_numeric_type
            (wordsSyntax.dest_word_type rngty)
          val _ = if Arbnum.>= (rngdim, dim) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term" "w2w: result type too short"
              else
                ();
              raise ERR "<builtin_symbols.w2w_tm>" "result type too short"
            )
          val n = Arbnum.- (rngdim, dim)
        in
          ("(_ zero_extend " ^ Arbnum.toString n ^ ")", [w])
        end) ts),
    (wordsSyntax.sw2sw_tm, fn (t, ts) =>
      SmtLib_Theories.one_arg (fn w =>
        let
          (* make sure that the result in HOL is at least as long as 'w' *)
          val dim = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of w)
          val rngty = Lib.snd (boolSyntax.strip_fun (Term.type_of t))
          val rngdim = fcpSyntax.dest_numeric_type
            (wordsSyntax.dest_word_type rngty)
          val _ = if Arbnum.>= (rngdim, dim) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term" "sw2sw: result type too short"
              else
                ();
              raise ERR "<builtin_symbols.sw2sw_tm>" "result type too short"
            )
          val n = Arbnum.- (rngdim, dim)
        in
          ("(_ sign_extend " ^ Arbnum.toString n ^ ")", [w])
        end) ts),
    (* rotation by a numeral; the corresponding HOL rotation operations that
       take two bit-vector arguments are not supported in SMT-LIB *)
    (wordsSyntax.word_rol_tm, fn (t, ts) =>
      (
        apfst_fixed_width "rotate_left" (t, ());
        SmtLib_Theories.two_args (fn (w, n) =>
          ("(_ rotate_left " ^ Arbnum.toString (numSyntax.dest_numeral n)
            ^ ")", [w])) ts
      )),
    (wordsSyntax.word_ror_tm, fn (t, ts) =>
      (
        apfst_fixed_width "rotate_right" (t, ());
        SmtLib_Theories.two_args (fn (w, n) =>
          ("(_ rotate_right " ^ Arbnum.toString (numSyntax.dest_numeral n)
            ^ ")", [w])) ts
      )),
    (wordsSyntax.word_lo_tm, apfst_fixed_width "bvult"),
    (wordsSyntax.word_ls_tm, apfst_fixed_width "bvule"),
    (wordsSyntax.word_hi_tm, apfst_fixed_width "bvugt"),
    (wordsSyntax.word_hs_tm, apfst_fixed_width "bvuge"),
    (wordsSyntax.word_lt_tm, apfst_fixed_width "bvslt"),
    (wordsSyntax.word_le_tm, apfst_fixed_width "bvsle"),
    (wordsSyntax.word_gt_tm, apfst_fixed_width "bvsgt"),
    (wordsSyntax.word_ge_tm, apfst_fixed_width "bvsge")
  ]

  (* SMT-LIB type and function names are uniformly generated as "tN"
     and "vN", respectively, where N is a number. Prefixes must be
     distinct. *)

  val ty_prefix = "t"  (* for types *)
  val tm_prefix = "v"  (* for terms *)
  val bv_prefix = "b"  (* for bound variables *)

  fun first_success f [] = NONE
    | first_success f (x :: xs) =
      SOME (f x) handle _ => first_success f xs

  fun has_type_builtin ty =
    Option.isSome (first_success (fn (_, f) => f ty)
      (TypeNet.match (builtin_types, ty)))

  fun is_function_type ty = Lib.can Type.dom_rng ty

  fun smt_sort_of_type tydict ty =
    if is_function_type ty then
      let
        val (dom, rng) = Type.dom_rng ty
      in
        "(Array " ^ smt_sort_of_type tydict dom ^ " " ^
        smt_sort_of_type tydict rng ^ ")"
      end
    else
      case first_success (fn (_, f) => f ty)
          (TypeNet.match (builtin_types, ty)) of
        SOME name => name
      | NONE => Redblackmap.find (tydict, ty)

  fun type_contains pred ty =
    pred ty orelse
    (let val (dom, rng) = Type.dom_rng ty
     in type_contains pred dom orelse type_contains pred rng end
     handle _ => false)

  fun type_contains_word ty =
    type_contains (Lib.can wordsSyntax.dest_word_type) ty

  fun type_contains_int ty =
    type_contains (fn ty => Type.compare (ty, intSyntax.int_ty) = EQUAL) ty

  fun type_contains_real ty =
    type_contains (fn ty => Type.compare (ty, realSyntax.real_ty) = EQUAL) ty

  fun type_contains_string ty =
    type_contains (fn ty => Type.compare (ty, stringSyntax.string_ty) = EQUAL)
      ty

  fun type_contains_function ty =
    type_contains is_function_type ty

  fun same_const c tm = Term.is_const tm andalso Term.same_const tm c

  val smt_rdiv_tm = Term.prim_mk_const {Thy="HolSmt", Name="smt_rdiv"}
  val int_ediv_tm = Term.prim_mk_const {Thy="integer", Name="ediv"}
  val int_emod_tm = Term.prim_mk_const {Thy="integer", Name="emod"}

  fun is_int_arith_const tm =
    List.exists (fn c => same_const c tm) [
      intSyntax.negate_tm, intSyntax.minus_tm, intSyntax.plus_tm,
      intSyntax.mult_tm, int_ediv_tm, int_emod_tm, intSyntax.absval_tm,
      intSyntax.leq_tm, intSyntax.less_tm, intSyntax.geq_tm,
      intSyntax.greater_tm
    ]

  fun is_real_arith_const tm =
    List.exists (fn c => same_const c tm) [
      realSyntax.negate_tm, realSyntax.minus_tm, realSyntax.plus_tm,
      realSyntax.mult_tm, smt_rdiv_tm, realSyntax.leq_tm,
      realSyntax.less_tm, realSyntax.geq_tm, realSyntax.greater_tm,
      intrealSyntax.real_of_int_tm, intrealSyntax.INT_FLOOR_tm,
      intrealSyntax.is_int_tm
    ]

  fun is_bv_const tm =
    List.exists (fn c => same_const c tm) [
      wordsSyntax.word_concat_tm, wordsSyntax.word_extract_tm,
      wordsSyntax.word_1comp_tm, wordsSyntax.word_and_tm,
      wordsSyntax.word_or_tm, wordsSyntax.word_nand_tm,
      wordsSyntax.word_nor_tm, wordsSyntax.word_xor_tm,
      wordsSyntax.word_xnor_tm, wordsSyntax.word_2comp_tm,
      wordsSyntax.word_compare_tm, wordsSyntax.word_add_tm,
      wordsSyntax.word_sub_tm, wordsSyntax.word_mul_tm,
      wordsSyntax.word_quot_tm, wordsSyntax.word_rem_tm,
      integer_wordSyntax.word_smod_tm, wordsSyntax.word_div_tm,
      wordsSyntax.word_mod_tm, wordsSyntax.word_lsl_bv_tm,
      wordsSyntax.word_lsr_bv_tm, wordsSyntax.word_asr_bv_tm,
      wordsSyntax.word_replicate_tm, wordsSyntax.w2w_tm,
      wordsSyntax.sw2sw_tm, wordsSyntax.word_rol_tm,
      wordsSyntax.word_ror_tm, wordsSyntax.word_lo_tm,
      wordsSyntax.word_ls_tm, wordsSyntax.word_hi_tm,
      wordsSyntax.word_hs_tm, wordsSyntax.word_lt_tm,
      wordsSyntax.word_le_tm, wordsSyntax.word_gt_tm,
      wordsSyntax.word_ge_tm
    ]

  fun is_nonlinear_arith_const tm =
    same_const intSyntax.mult_tm tm orelse same_const realSyntax.mult_tm tm

  fun is_string_const tm =
    List.exists (fn c => same_const c tm) [
      stringSyntax.strcat_tm, stringSyntax.isprefix_tm,
      stringSyntax.string_lt_tm, stringSyntax.string_le_tm
    ]

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

  fun builtin_encoding tm =
    let
      val (rator, rands) = boolSyntax.strip_comb tm
      fun try_whole () =
        if not (Lib.can Type.dom_rng (Term.type_of tm)) then
          (case first_success (fn parsefn => parsefn (tm, []))
              (Net.match tm builtin_symbols) of
             SOME (symbol, _) => SOME (symbol, 0)
           | NONE => NONE)
        else
          NONE
        handle _ => NONE
    in
      case first_success (fn parsefn => parsefn (rator, rands))
          (Net.match rator builtin_symbols) of
        SOME (symbol, _) => SOME (symbol, List.length rands)
      | NONE => try_whole ()
    end

  fun insert_builtin_record (record, records) =
    if List.exists
        (fn EncodedSymbol {hol_term, smt_symbol, arity} =>
              (case record of
                 EncodedSymbol {hol_term = hol_term',
                   smt_symbol = smt_symbol', arity = arity'} =>
                   Term.compare (hol_term, hol_term') = EQUAL andalso
                   smt_symbol = smt_symbol' andalso arity = arity'
               | _ => false)
          | _ => false) records
    then records
    else record :: records

  fun encoded_symbol_records terms =
    let
      fun add (tm, records) =
        case builtin_encoding tm of
          SOME (symbol, arity) =>
            insert_builtin_record
              (EncodedSymbol {hol_term = Lib.fst (boolSyntax.strip_comb tm),
                smt_symbol = symbol, arity = arity}, records)
        | NONE => records
    in
      List.foldl add [] (List.concat (List.map subterms terms))
    end

  fun features_to_string (LogicFeatures {
      quantifiers, uninterpreted, arrays, bitvectors, integers, reals,
      strings, nonlinear}) =
    String.concatWith "," (List.map Lib.fst (List.filter Lib.snd [
      ("quantifiers", quantifiers),
      ("uninterpreted", uninterpreted),
      ("arrays", arrays),
      ("bitvectors", bitvectors),
      ("integers", integers),
      ("reals", reals),
      ("strings", strings),
      ("nonlinear", nonlinear)
    ]))

  fun infer_logic_from_features (features as LogicFeatures {
      quantifiers, uninterpreted, arrays, bitvectors, integers, reals,
      strings, nonlinear}) =
    let
      val qf = if quantifiers then "" else "QF_"
      fun arith_logic () =
        if integers andalso reals then
          if quantifiers orelse arrays orelse uninterpreted then
            "AUFNIRA"
          else if nonlinear then qf ^ "NIRA" else qf ^ "LIRA"
        else if integers then
          if arrays then
            qf ^ "AUF" ^ (if nonlinear then "NIA" else "LIA")
          else if uninterpreted then
            qf ^ "UF" ^ (if nonlinear then "NIA" else "LIA")
          else
            qf ^ (if nonlinear then "NIA" else "LIA")
        else if reals then
          if arrays then
            qf ^ "AUF" ^ (if nonlinear then "NRA" else "LRA")
          else if uninterpreted then
            qf ^ "UF" ^ (if nonlinear then "NRA" else "LRA")
          else
            qf ^ (if nonlinear then "NRA" else "LRA")
        else if arrays then
          if quantifiers then "ALL" else "QF_AX"
        else
          qf ^ "UF"
      val logic =
        if strings then
          if bitvectors orelse reals orelse quantifiers orelse arrays orelse
             uninterpreted then
            "ALL"
          else if integers then
            if nonlinear then "QF_SNIA" else "QF_SLIA"
          else
            "QF_S"
        else if bitvectors then
          if integers orelse reals orelse quantifiers then
            "ALL"
          else if arrays then
            if uninterpreted then qf ^ "AUFBV" else qf ^ "ABV"
          else if uninterpreted then
            qf ^ "UFBV"
          else
            qf ^ "BV"
        else
          arith_logic ()
      val reason =
        "deterministic feature scan: " ^
        (case features_to_string features of "" => "core" | s => s)
    in
      (logic, reason)
    end

  fun term_decl_for_tmdict tydict ((tm, arity), name) =
    let
      fun doms_rng acc 0 ty = (List.rev acc, ty)
        | doms_rng acc n ty =
          let val (dom, rng) = Type.dom_rng ty
          in doms_rng (dom :: acc) (n - 1) rng end
      val (domtys, rngty) = doms_rng [] arity (Term.type_of tm)
      val domain_sorts = List.map (smt_sort_of_type tydict) domtys
      val range_sort = smt_sort_of_type tydict rngty
      val declaration = "(declare-fun " ^ name ^ " (" ^
        String.concatWith " " domain_sorts ^ ") " ^ range_sort ^ ")\n"
    in
      TermDeclaration {hol_term = tm, arity = arity, smt_name = name,
        domain_sorts = domain_sorts, range_sort = range_sort,
        declaration = declaration}
    end

  fun type_decl_record (ty, name) =
    TypeDeclaration {hol_type = ty, smt_name = name,
      declaration = "(declare-sort " ^ name ^ " 0)\n"}

  fun infer_features terms tydict tmdict =
    let
      val all_subterms = List.concat (List.map subterms terms)
      fun subterm_types p =
        List.exists (fn tm => p (Term.type_of tm)) all_subterms
      val quantifiers = List.exists has_quantifier terms
      val bitvectors =
        subterm_types type_contains_word orelse
        List.exists (fn tm => is_bv_const (Lib.fst (boolSyntax.strip_comb tm)))
          all_subterms
      val integers =
        subterm_types type_contains_int orelse
        List.exists (fn tm => is_int_arith_const
          (Lib.fst (boolSyntax.strip_comb tm))) all_subterms
      val reals =
        subterm_types type_contains_real orelse
        List.exists (fn tm => is_real_arith_const
          (Lib.fst (boolSyntax.strip_comb tm))) all_subterms
      val strings =
        subterm_types type_contains_string orelse
        List.exists (fn tm => is_string_const
          (Lib.fst (boolSyntax.strip_comb tm))) all_subterms
      val nonlinear =
        List.exists (fn tm => is_nonlinear_arith_const
          (Lib.fst (boolSyntax.strip_comb tm))) all_subterms
      val has_uninterpreted_type = Redblackmap.numItems tydict > 0
      fun range_after 0 ty = ty
        | range_after n ty = range_after (n - 1) (Lib.snd (Type.dom_rng ty))
      fun term_needs_uf ((tm, arity), _) =
        arity > 0 orelse
        (arity = 0 andalso
         not (has_type_builtin (range_after arity (Term.type_of tm))) andalso
         not (is_function_type (range_after arity (Term.type_of tm))))
      val uninterpreted =
        has_uninterpreted_type orelse
        Redblackmap.foldl (fn (key, value, b) =>
          b orelse term_needs_uf (key, value)) false tmdict
      val arrays =
        List.exists (fn tm =>
          (Term.is_var tm andalso type_contains_function (Term.type_of tm))
          orelse combinSyntax.is_update_comb tm) all_subterms orelse
        Redblackmap.foldl (fn ((tm, arity), _, b) =>
          b orelse (arity = 0 andalso type_contains_function (Term.type_of tm)))
          false tmdict
    in
      LogicFeatures {quantifiers = quantifiers, uninterpreted = uninterpreted,
        arrays = arrays, bitvectors = bitvectors, integers = integers,
        reals = reals, strings = strings, nonlinear = nonlinear}
    end

  fun advanced_encoding_records terms =
    let
      val all_subterms = List.concat (List.map subterms terms)
      fun subterm_types p =
        List.exists (fn tm => p (Term.type_of tm)) all_subterms
      val has_strings =
        subterm_types type_contains_string orelse
        List.exists (fn tm => is_string_const
          (Lib.fst (boolSyntax.strip_comb tm))) all_subterms
      val string_record =
        HOLTheoryEncoding {
          feature = "HOL strings: string type, STRCAT, isPREFIX, string_lt, string_le",
          smt_theory = "UnicodeStrings",
          mode = NativeSMTLIB,
          parse = true,
          typecheck = true,
          translate = true,
          replay = false,
          notes = "HOL strings are char lists over HOL characters; SMT-LIB String is UnicodeStrings.",
          proof_obligation =
            "A checked soundness argument must prove or constrain the HOL char-list to SMT Unicode string correspondence before replay is claimed."
        }
      val datatype_record =
        HOLTheoryEncoding {
          feature = "HOL datatypes and recursive datatypes",
          smt_theory = "Datatypes",
          mode = ConservativeEmbedding,
          parse = true,
          typecheck = true,
          translate = false,
          replay = false,
          notes =
            "SMT-LIB datatype commands are parsed/typechecked; HOL datatype constructors/selectors are not emitted as native SMT datatypes by this translator.",
          proof_obligation =
            "A checked soundness argument must connect constructor disjointness, injectivity, selectors, testers, and recursion axioms before native replay support."
        }
      val fp_record =
        HOLTheoryEncoding {
          feature = "HOL floating point",
          smt_theory = "FloatingPoint",
          mode = ConservativeEmbedding,
          parse = true,
          typecheck = true,
          translate = false,
          replay = false,
          notes =
            "SMT-LIB floating-point symbols are parsed/typechecked; HOL binary_ieee terms are not translated to native FloatingPoint.",
          proof_obligation =
            "A checked soundness argument must audit NaN, infinities, signed zero, rounding modes, and underspecified conversions before replay support."
        }
      val z3_ext_record =
        HOLTheoryEncoding {
          feature = "sequences, sets, and bags",
          smt_theory = "Z3 sequence/set/bag extensions",
          mode = ConservativeEmbedding,
          parse = true,
          typecheck = true,
          translate = false,
          replay = false,
          notes =
            "Z3 extension symbols are parser/typechecker entries only; generic HOL lists, predicates-as-sets, and bags are not emitted as Seq/Set/Bag.",
          proof_obligation =
            "A checked soundness argument must establish list/sequence, predicate/set, and multiplicity/bag correspondences before replay support."
        }
      val regex_record =
        HOLTheoryEncoding {
          feature = "regular expressions",
          smt_theory = "UnicodeStrings RegLan",
          mode = ConservativeEmbedding,
          parse = true,
          typecheck = true,
          translate = false,
          replay = false,
          notes =
            "SMT-LIB regex terms are parsed/typechecked through RegLan; HOL regex libraries are not translated to RegLan.",
          proof_obligation =
            "A checked soundness argument must relate HOL regex languages to SMT-LIB RegLan membership and Unicode string semantics before replay support."
        }
    in
      (if has_strings then [string_record] else []) @
      [datatype_record, fp_record, z3_ext_record, regex_record]
    end

  fun build_translation_records terms logic reason features tydict tmdict =
    let
      val logic_record = LogicSelection {logic = logic, reason = reason,
        features = features}
      val type_records = Redblackmap.foldl (fn (ty, name, acc) =>
        type_decl_record (ty, name) :: acc) [] tydict
      val term_records = Redblackmap.foldl (fn (key, name, acc) =>
        term_decl_for_tmdict tydict (key, name) :: acc) [] tmdict
      val builtin_records = encoded_symbol_records terms
      val advanced_records = advanced_encoding_records terms
    in
      logic_record :: List.rev type_records @ List.rev term_records @
      List.rev builtin_records @ advanced_records
    end

  fun parser_dicts_for_translation_aux ({logic, tydict, tmdict, ...} : translation) =
    let
      val ty_dict = Redblackmap.foldl (fn (ty, s, dict) =>
        Redblackmap.insert (dict, s, [SmtLib_Theories.K_zero_zero ty]))
        (Redblackmap.mkDict String.compare) tydict
      val tm_dict = Redblackmap.foldl (fn ((tm, n), s, dict) =>
        Redblackmap.insert (dict, s, [Lib.K (SmtLib_Theories.zero_args
          (fn args =>
            if List.length args = n then
              Term.list_mk_comb (tm, args)
            else
              raise ERR ("<" ^ s ^ ">") "wrong number of arguments"))]))
        (Redblackmap.mkDict String.compare) tmdict
      val (logic_tydict, logic_tmdict) = SmtLib_Logics.parsedicts_of_logic logic
    in
      (Library.union_dict logic_tydict ty_dict,
       Library.union_dict logic_tmdict tm_dict)
    end

  (* returns an updated accumulator, a (possibly empty) list of
     SMT-LIB type declarations, and the SMT-LIB representation of the
     given type *)
  fun translate_type (tydict, ty) =
  let
    val (tydict, (decls, name)) =
      if is_function_type ty then
        let
          val (dom, rng) = Type.dom_rng ty
          val (tydict, (domdecls, domname)) = translate_type (tydict, dom)
          val (tydict, (rngdecls, rngname)) = translate_type (tydict, rng)
        in
          (tydict, (domdecls @ rngdecls, "(Array " ^ domname ^ " " ^
            rngname ^ ")"))
        end
      else
        (tydict,
          ([],
            case first_success (fn (_, f) => f ty)
                (TypeNet.match (builtin_types, ty)) of
              SOME name => name
            | NONE => Redblackmap.find (tydict, ty)))
  in
    (tydict, (decls, name))
  end
  handle Redblackmap.NotFound =>
    (* uninterpreted types *)
    let
      val name = ty_prefix ^ Int.toString (Redblackmap.numItems tydict)
      val decl = "(declare-sort " ^ name ^ " 0)\n"
    in
      if !Library.trace > 0 andalso Type.is_type ty then
        WARNING "translate_type"
          ("uninterpreted type " ^ Hol_pp.type_to_string ty)
      else
        ();
      if !Library.trace > 2 then
        Feedback.HOL_MESG ("HolSmtLib (SmtLib): inventing name '" ^ name ^
          "' for HOL type '" ^ Hol_pp.type_to_string ty ^ "'")
      else
        ();
      (Redblackmap.insert (tydict, ty, name), ([decl], name))
    end

  (* SMT-LIB is first-order.  Thus, higher-order arguments must be abstracted
     so that they are
     of (uninterpreted) base type.  We achieve this by abstracting the
     offending function type to a fresh base type, and by abstracting
     the argument's rator to an uninterpreted term that returns the
     correct (abstracted) type.  Note that the same function/operator
     may appear both with and without arguments in a HOL formula.
     'tmdict' maps terms along with the number of their actual
     arguments to an SMT-LIB representation. *)

  (* returns an updated accumulator, a (possibly empty) list of
     SMT-LIB (type and term) declarations, and the SMT-LIB
     representation of the given term *)
  fun translate_term (acc as (tydict, tmdict), (bounds, tm)) =
  let
    fun sexpr x [] = x
      | sexpr x xs = "(" ^ x ^ " " ^ String.concatWith " " xs ^ ")"
    fun builtin_symbol (rator, rands) =
      let
        val (name, rands) = Lib.tryfind (fn parsefn => parsefn (rator, rands))
          (Net.match rator builtin_symbols)  (* may fail *)
        val (acc, declnames) = Lib.foldl_map
          (fn (a, t) => translate_term (a, (bounds, t))) (acc, rands)
        val (declss, names) = Lib.split declnames
      in
        (acc, (List.concat declss, sexpr name names))
      end
    (* creates a mapping from bound variables to their SMT-LIB names; if a
       variable is already mapped, we return its existing SMT-LIB name *)
    fun create_bound_name (bounds, v) =
      (bounds, Redblackmap.find (bounds, v))
      handle Redblackmap.NotFound =>
        let
          val name = bv_prefix ^ Int.toString (Redblackmap.numItems bounds)
        in
          (Redblackmap.insert (bounds, v, name), name)
        end
    val tm_has_base_type = not (Lib.can Type.dom_rng (Term.type_of tm))
  in
    (* binders *)
    let
      (* perhaps we should use a table of binders instead *)
      val (binder, (vars, body)) = if boolSyntax.is_forall tm then
          ("forall", boolSyntax.strip_forall tm)
        else if boolSyntax.is_exists tm then
          ("exists", boolSyntax.strip_exists tm)
        else
          raise ERR "translate_term" "not a binder"  (* handled below *)
      val (bounds, smtvars) = Lib.foldl_map create_bound_name (bounds, vars)
      val (tydict, vardecltys) = Lib.foldl_map translate_type
        (tydict, List.map Term.type_of vars)
      val (vardeclss, vartys) = Lib.split vardecltys
      val vardecls = List.concat vardeclss
      val smtvars = ListPair.mapEq (fn (v, ty) => "(" ^ v ^ " " ^ ty ^ ")")
        (smtvars, vartys)
      val (acc, (bodydecls, body)) = translate_term
        ((tydict, tmdict), (bounds, body))
    in
      (acc, (vardecls @ bodydecls, "(" ^ binder ^ " (" ^
        String.concatWith " " smtvars ^ ") " ^ body ^ ")"))
    end
    handle Feedback.HOL_ERR _ =>

    (* let binder - somewhat similar to quantifiers *)
    let
      val (bindings, body) = pairSyntax.dest_anylet tm
      val (vars, bodies) = ListPair.unzip bindings
      (* we should translate the bodies without first creating the bound names *)
      val bounds_bodies = List.map (fn body => (bounds, body)) bodies
      val (acc, decls_bodies) = Lib.foldl_map translate_term (acc, bounds_bodies)
      (* now we can create the bound names *)
      val (bounds, smtvars) = Lib.foldl_map create_bound_name (bounds, vars)
      val decls_bodies_smtvars = ListPair.zipEq (decls_bodies, smtvars)
      val (decls, smtbinds) = List.foldl (fn (((d, b), v), (decls, smtbinds)) =>
        (d @ decls, "(" ^ v ^ " " ^ b ^ ")" :: smtbinds)) ([], [])
          decls_bodies_smtvars
      val bindings_str = String.concatWith " " (List.rev smtbinds)
      val (acc, (bodydecls, body)) = translate_term (acc, (bounds, body))
    in
      (acc, (decls @ bodydecls,
        "(let (" ^ bindings_str ^ ") " ^ body ^ ")"))
    end
    handle Feedback.HOL_ERR _ =>

    (* bound variables may shadow built-in symbols etc. *)
    (acc, ([], Redblackmap.find (bounds, tm)))
    handle Redblackmap.NotFound =>

    (* translate the entire term (e.g., for numerals), using the dictionary of
       built-in symbols; however, only do this if 'tm' has base type *)
    (if tm_has_base_type then
      builtin_symbol (tm, [])
    else
      raise ERR "translate_term" "not first-order")  (* handled below *)
    handle Feedback.HOL_ERR _ =>

    (* split the term into rator and rands *)
    let
      val (rator, rands) = boolSyntax.strip_comb tm
    in
      (* translate the rator as a built-in symbol (applied to its rands); only
         do this if 'tm' has base type *)
      (if tm_has_base_type then
        builtin_symbol (rator, rands)
      else
        raise ERR "translate_term" "not first-order")  (* handled below *)
    handle Feedback.HOL_ERR _ =>

      (* arrays are represented by HOL functions: function application is
         SMT-LIB select, and UPDATE application is SMT-LIB store. *)
      let
        val ((index, value), array) = combinSyntax.dest_update_comb tm
        val (acc, (arraydecls, arrayname)) =
          translate_term (acc, (bounds, array))
        val (acc, (indexdecls, indexname)) =
          translate_term (acc, (bounds, index))
        val (acc, (valuedecls, valuename)) =
          translate_term (acc, (bounds, value))
      in
        (acc, (arraydecls @ indexdecls @ valuedecls,
          sexpr "store" [arrayname, indexname, valuename]))
      end
    handle Feedback.HOL_ERR _ =>

      let
        val (function, argument) = Term.dest_comb tm
        val _ = Type.dom_rng (Term.type_of function)
        val (head, _) = boolSyntax.strip_comb tm
        val _ =
          if Term.is_const head andalso
             not (combinSyntax.is_update_comb function) then
            raise ERR "translate_term" "HOL constants are emitted as functions"
          else
            ()
        val (acc, (functiondecls, functionname)) =
          translate_term (acc, (bounds, function))
        val (acc, (argumentdecls, argumentname)) =
          translate_term (acc, (bounds, argument))
      in
        (acc, (functiondecls @ argumentdecls,
          sexpr "select" [functionname, argumentname]))
      end
    handle Feedback.HOL_ERR _ =>

      let
        val rands_count = List.length rands
        val _ =
          if Term.is_const rator orelse Term.is_var rator then ()
          else
            raise ERR "translate_term"
              ("unsupported higher-order rator expression: " ^
               Hol_pp.term_to_string rator)
        val (acc, (decls, name)) =
          (* translate the rator as a previously defined symbol *)
          (acc, ([], Redblackmap.find (tmdict, (rator, rands_count))))
          handle Redblackmap.NotFound =>

          (* translate the rator as a new (i.e., uninterpreted) symbol *)
          let
            (* translate 'rator' types required for the rator's
               SMT-LIB declaration *)
            fun doms_rng acc 0 ty =
              (List.rev acc, ty)
              | doms_rng acc n ty =
              let
                val (dom, rng) = Type.dom_rng ty
              in
                doms_rng (dom :: acc) (n - 1) rng
              end
            (* strip only 'rands_count' many 'domtys', leaving the remaining
               argument types in 'rngty' *)
            val (domtys, rngty) = doms_rng [] rands_count (Term.type_of rator)
            val (tydict, domdecltys) = Lib.foldl_map translate_type
              (tydict, domtys)
            val (domdeclss, domtys) = Lib.split domdecltys
            val domdecls = List.concat domdeclss
            val (tydict, (rngdecls, rngty)) = translate_type (tydict, rngty)
            (* invent new name for 'rator' *)
            val name = tm_prefix ^ Int.toString (Redblackmap.numItems tmdict)
            val _ = if !Library.trace > 0 andalso Term.is_const rator then
              WARNING "translate_term"
                ("uninterpreted constant " ^ Hol_pp.term_to_string rator)
              else
                ();
            val _ = if !Library.trace > 2 then
                Feedback.HOL_MESG ("HolSmtLib (SmtLib): inventing name '" ^
                  name ^ "' for HOL term '" ^ Hol_pp.term_to_string rator ^
                  "' (applied to " ^ Int.toString rands_count ^ " argument(s))")
              else
                ()
            val tmdict = Redblackmap.insert (tmdict, (rator, rands_count), name)
            val decl = "(declare-fun " ^ name ^ " (" ^
              String.concatWith " " domtys ^ ") " ^ rngty ^ ")\n"
          in
            ((tydict, tmdict), (domdecls @ rngdecls @ [decl], name))
          end
        (* translate 'rands' *)
        val (acc, declnames) = Lib.foldl_map
          (fn (a, t) => translate_term (a, (bounds, t))) (acc, rands)
        val (declss, names) = Lib.split declnames
      in
        (acc, (decls @ List.concat declss, sexpr name names))
      end
    end
  end

  (* Returns a string list representing the input goal in SMT-LIB file
     format, together with two dictionaries that map types and terms
     to identifiers used in the SMT-LIB representation.  The goal's
     conclusion is negated before translation into SMT-LIB format.
     The integer in the term dictionary gives the number of actual
     arguments to the term.  (Because SMT-LIB is first-order,
     partially applied functions are mapped to different SMT-LIB
     identifiers, depending on the number of actual arguments.) *)
  fun goal_to_SmtLib_aux logic (ts, t) : translation * string list =
  let
    val tydict = Redblackmap.mkDict Type.compare
    val tmdict = Redblackmap.mkDict
      (Lib.pair_compare (Term.compare, Int.compare))
    val bounds = Redblackmap.mkDict Term.compare
    val terms = ts @ [boolSyntax.mk_neg t]
    val (acc, smtlibs) = Lib.foldl_map
      (fn (acc, tm) => translate_term (acc, (bounds, tm)))
      ((tydict, tmdict), terms)
    val (tydict, tmdict) = acc
    val features = infer_features terms tydict tmdict
    val (inferred_logic, reason) = infer_logic_from_features features
    val (selected_logic, reason) =
      case logic of
        NONE => (inferred_logic, reason)
      | SOME l => (l, "caller override")
    val records =
      build_translation_records terms selected_logic reason features tydict tmdict
    val translation = {logic = selected_logic, tydict = tydict,
      tmdict = tmdict, records = records}
    (* we choose to intertwine declarations and assertions (for no
       particular reason; an alternative would be to emit all
       declarations before all assertions) *)
    val smtlibs = List.foldl
      (fn ((xs, s), acc) => acc @ xs @ ["(assert " ^ s ^ ")\n"]) [] smtlibs
  in
    (translation, ["(set-logic " ^ selected_logic ^ ")\n"] @ [
      "(set-info :source |Automatically generated from HOL4 by SmtLib.goal_to_SmtLib.\n",
      "Copyright (c) 2011 Tjark Weber. All rights reserved.|)\n",
      "(set-info :smt-lib-version 2.6)\n"
    ] @ smtlibs @ [
      "(check-sat)\n"
    ])
  end

  (* convert `num` literals into integer literals *)
  fun NUM_TO_INT_CONV tm =
  let
    fun conv_term tm =
      if numSyntax.is_numeral tm then
        Thm.SYM (Thm.SPEC tm integerTheory.NUM_OF_INT)
      else
        raise Conv.UNCHANGED
    fun is_builtin_num_sym tm =
    let
      val sym = Lib.fst (boolSyntax.strip_comb tm)
    in
    (* The following are symbols that take numerals as arguments but which we
       already have special handlers to convert into SMT-LIB syntax (therefore
       we don't need to convert their arguments into integer literals) *)
      List.exists (Term.same_const sym) [
        wordsSyntax.word_extract_tm, wordsSyntax.word_replicate_tm,
        wordsSyntax.word_rol_tm, wordsSyntax.word_ror_tm
      ]
    end
  in
    (* Don't descend when encountering integer, rational, real or word literals,
       otherwise we'll be inadvertently converting those as well. Also, don't
       descend when encountering symbols that take numerals as arguments and
       which we already handle specially. *)
    if intSyntax.is_int_literal tm orelse ratSyntax.is_literal tm orelse
       realSyntax.is_real_literal tm orelse wordsSyntax.is_word_literal tm orelse
       is_builtin_num_sym tm then
      raise Conv.UNCHANGED
    else
      (Conv.THENC (Conv.SUB_CONV NUM_TO_INT_CONV, conv_term)) tm
  end

  local
    structure A = arithmeticTheory
    structure I = integerTheory
    structure IR = intrealTheory
    structure R = realTheory
    structure RA = realaxTheory
  in
    fun thms_per_const const =
    let
      val { Thy, Name, Ty } = Term.dest_thy_const const
      val bool = Type.bool
      val num = numSyntax.num
      val op--> = Type.-->
      infixr 3 -->
    in
      (* NOTE: when adding a theorem to the list below, make sure that it
         doesn't have any free var -- otherwise, ASSUME_TAC will specialize
         the theorem to any free var in the goal that happens to have the same
         name, which very often is not what is desired. As an example,
         integerTheory's `INT_POW` should not be added -- instead, add
         `int_exp`. If no appropriate quantified theorem is available,
         `Drule.GEN_ALL` can be used to quantify all free vars in a theorem.

         Also, make sure the theorem is really needed -- some theorems seem to
         cause an explosion in the time needed to solve some goals, often
         making Z3 unable to solve them -- and it's not always easy to tell a
         priori which ones do. As an example, arithmeticTheory.EXP_1 doesn't
         seem to cause issues, but EXP_2 prevents Z3 from solving
         ``x DIV 42 <= x``. *)
      case (Thy, Name) of
        ("arithmetic", "*") => [ I.NUM_INT_MUL ]
      | ("arithmetic", "+") => [ I.INT_ADD ]
      | ("arithmetic", "-") => [ int_arithTheory.INT_NUM_SUB ]
      | ("arithmetic", "<=") => [ I.INT_LE ]
      | ("arithmetic", ">") => [ A.GREATER_DEF ]
      | ("arithmetic", ">=") => [ A.GREATER_EQ ]
      | ("arithmetic", "DIV") => [ I.NUM_INT_EDIV ]
      | ("arithmetic", "EXP") => [ A.EXP, A.EXP_1, A.EXP_POS ]
      | ("arithmetic", "MAX") => [ A.MAX_DEF ]
      | ("arithmetic", "MIN") => [ A.MIN_DEF ]
      | ("arithmetic", "MOD") => [ I.NUM_INT_EMOD ]
      | ("integer", "Num") => [ I.INT_OF_NUM, I.NUM_OF_INT ]
      | ("integer", "int_div") => [ I.INT_DIV_EDIV ]
      | ("integer", "int_exp") => [ I.int_exp ]
      | ("integer", "int_max") => [ I.INT_MAX ]
      | ("integer", "int_min") => [ I.INT_MIN ]
      | ("integer", "int_mod") => [ I.INT_MOD_EMOD ]
      | ("integer", "int_of_num") => [ I.INT_OF_NUM, I.INT_POS, I.NUM_OF_INT ]
      | ("integer", "int_quot") => [ I.INT_QUOT_EDIV ]
      | ("integer", "int_rem") => [ I.INT_REM_EMOD ]
      | ("intreal", "INT_CEILING") => [ HolSmtTheory.int_ceiling_floor ]
      | ("marker", "Abbrev") => [ markerTheory.Abbrev_def ]
      | ("min", "=") =>
          if Type.compare (Ty, num --> num --> bool) = EQUAL then
            [ I.INT_INJ ]
          else
            []
      | ("num", "SUC") => [ I.INT ]
      | ("prim_rec", "<") => [ I.INT_LT ]
      | ("realax", "/") => [ HolSmtTheory.real_div_smt_rdiv ]
      | ("realax", "NUM_CEILING") => [ IR.INT_NUM_CEILING, R.NUM_CEILING_BASE ]
      | ("realax", "NUM_FLOOR") => [ IR.INT_NUM_FLOOR, R.NUM_FLOOR_BASE ]
      | ("realax", "abs") => [ R.abs ]
      | ("realax", "inv") => [ R.REAL_INV_1OVER ]
      | ("realax", "max") => [ RA.real_max ]
      | ("realax", "min") => [ RA.real_min ]
      | ("realax", "pow") => [ R.POW_2, R.POW_ONE, R.REAL_POW_LT, RA.real_pow ]
      | ("realax", "real_of_num") =>
          [ Drule.GEN_ALL (Thm.SYM IR.real_of_int_num) ]
      | _ => []
    end
  end

  (* Prepends the conclusion of a theorem to the list of its hypothesis and
     returns the resulting list of terms *)
  fun thm_terms thm =
  let
    val (hyps, concl) = Thm.dest_thm thm
  in
    concl :: hyps
  end

  (* Compares two theorems *)
  fun thm_compare (thm1, thm2) =
    List.collate Term.compare (thm_terms thm1, thm_terms thm2)

  (* An empty set of theorems *)
  val empty_thmset = HOLset.empty thm_compare

  (* Computes the list of theorems to add to the goal, given a list of all the
     terms in the goal. Since the resulting list of theorems might require more
     theorems to be added (for the SMT solvers to properly solve the goal), this
     function calls itself recursively until no new theorems are needed anymore. *)
  fun get_thms ([], acc) = HOLset.listItems acc
    | get_thms (terms, acc) =
      let
        (* Create a set of all the constants used in all the provided terms *)
        val atoms = Term.all_atomsl terms Term.empty_tmset
        val consts = HOLset.filter Term.is_const atoms

        (* Generate a set of all the theorems we want to add, based on these
           constants *)
        fun const_thms (const, acc) = HOLset.addList (acc, thms_per_const const)
        val wanted_thms = HOLset.foldl const_thms empty_thmset consts

        (* Apply NUM_TO_INT_CONV to these theorems, to convert any num literals
           they might have into int literals. We do this here because this
           conversion introduces constants that might trigger new theorems to be
           added in subsequent iterations *)
        fun conv_thm (thm, acc) =
          HOLset.add (acc, Conv.CONV_RULE NUM_TO_INT_CONV thm)
        val wanted_thms = HOLset.foldl conv_thm empty_thmset wanted_thms

        (* Since some of the theorems might have already been added in a
           previous recursive call, here we compute the theorems that will
           actually be newly added in this iteration *)
        val thms_to_add = HOLset.difference (wanted_thms, acc)

        (* Now we compute the new terms that will have to be analyzed in the
           next recursive call, which correspond to the terms used in the
           theorems newly added in this iteration *)
        fun add_new_terms (thm, acc) = HOLset.addList (acc, thm_terms thm)
        val new_terms = HOLset.foldl add_new_terms Term.empty_tmset thms_to_add
      in
        get_thms (HOLset.listItems new_terms, HOLset.union (acc, thms_to_add))
      end

in

  (* Controls whether HolSmt will try to include relevant theorems when trying
     to prove the goal, including theorems necessary for solving goals that
     have terms of type `num`. Unfortunately, these theorems may also hinder
     SMT performance in some cases, hence this escape hatch. *)
  val include_theorems = ref true

  fun translation_logic ({logic, ...} : translation) = logic
  fun translation_records ({records, ...} : translation) = records
  fun translation_dicts ({tydict, tmdict, ...} : translation) = (tydict, tmdict)
  val parser_dicts_for_translation = parser_dicts_for_translation_aux

  fun goal_to_SmtLib_translation logic =
    Lib.apsnd (fn xs => xs @ ["(exit)\n"]) o (goal_to_SmtLib_aux logic)

  fun goal_to_SmtLib logic goal =
    let
      val (translation, strings) = goal_to_SmtLib_translation logic goal
    in
      (translation_dicts translation, strings)
    end

  fun goal_to_SmtLib_with_get_proof_translation logic =
    Lib.apsnd (fn xs => xs @ ["(get-proof)\n", "(exit)\n"]) o
      (goal_to_SmtLib_aux logic)

  fun goal_to_SmtLib_with_get_proof logic goal =
    let
      val (translation, strings) =
        goal_to_SmtLib_with_get_proof_translation logic goal
    in
      (translation_dicts translation, strings)
    end

  val NUM_TO_INT_CONV = NUM_TO_INT_CONV

  (* Applies NUM_TO_INT_CONV to both the assumptions and the conclusion *)
  val NUM_TO_INT_TAC =
  let
    open Tactic Tactical
  in
    RULE_ASSUM_TAC (Conv.CONV_RULE NUM_TO_INT_CONV) THEN
    CONV_TAC NUM_TO_INT_CONV
  end

  (* This tactic calls ASSUME_TAC on theorems that are deemed necessary for SMT
     solvers to solve the goal (but only if `include_theorems` is true) *)
  fun ADD_THEOREMS_TAC g =
  let
    val (asms, concl) = g
    val goal_terms = concl :: asms

    val thms_to_add =
      if !include_theorems then
        get_thms (goal_terms, empty_thmset)
      else
        []

    val tactic = Tactical.MAP_EVERY Tactic.ASSUME_TAC thms_to_add
  in
    tactic g
  end

  (* Eliminates some HOL terms that are not supported by the SMT-LIB
     translation. It also adds some useful theorems to the list of assumptions
     so that SMT solvers can reason about some symbols defined in HOL4 theories. *)
  fun SIMP_TAC simp_let =
  let
    open Tactical simpLib
  in
    REPEAT Tactic.GEN_TAC THEN
    (if simp_let then Library.LET_SIMP_TAC else ALL_TAC) THEN
    SIMP_TAC pureSimps.pure_ss [
      (* FIXME: polymorphic functions seem to be highly problematic at the
         moment because after HolSmt's translation, the symbols in these
         theorems (e.g. ``FST``, ``SND``, ``$,``, etc) won't be the same as the
         ones in the goal, apparently because they have different types (due to
         type instantiation). This means that currently, passing these theorems
         as facts/assumptions will be useless in most circumstances. We try to
         use these theorems in simplification here but this only helps solving
         the simpler goals. *)
      pairTheory.PAIR_EQ, pairTheory.FST, pairTheory.SND,
      combinTheory.UPDATE_APPLY1, combinTheory.APPLY_UPDATE_THM,
      combinTheory.UPDATE_EQ, boolTheory.REFL_CLAUSE,
      HolSmtTheory.ALL_DISTINCT_NIL, HolSmtTheory.ALL_DISTINCT_CONS,
      listTheory.MEM
    ] THEN
    SIMP_TAC pureSimps.pure_ss [
      boolTheory.FUN_EQ_THM, boolTheory.REFL_CLAUSE
    ] THEN
    Library.WORD_SIMP_TAC THEN
    Library.SET_SIMP_TAC THEN
    Tactic.BETA_TAC THEN
    NUM_TO_INT_TAC THEN
    ADD_THEOREMS_TAC
  end
end  (* local *)

end
