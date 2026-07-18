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
  datatypes : bool,
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
  | DatatypeDeclaration of {hol_types : Type.hol_type list,
                            smt_names : string list, declaration : string}
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
  (* built lazily: only the Unittest diagnostics force this, never the
     production solve path (see 'translation_records') *)
  records : unit -> translation_record list
}

type logic_selection_policy = {
  features : logic_features,
  inferred_logic : string,
  reason : string
} -> {logic : string, reason : string} option

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
  val int_emod_tm = Term.prim_mk_const {Thy="integer", Name="emod"}
  fun mk_int_emod (dividend, divisor) =
    Term.list_mk_comb (int_emod_tm, [dividend, divisor])

  fun literal_int_divides_mod_eq (divisor, dividend) =
    if intSyntax.is_int_literal divisor andalso
       Arbint.> (intSyntax.int_of_term divisor, Arbint.zero) then
      [mk_int_emod (dividend, divisor), intSyntax.term_of_int Arbint.zero]
    else
      raise ERR "<builtin_symbols.int_divides>" "not a positive literal divisor"

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
    (* The parser represents SMT-LIB Core.distinct as ALL_DISTINCT over a
       HOL list.  The list is only an internal n-ary encoding: emit its
       elements as the direct SMT-LIB arguments rather than translating the
       wrapper as a datatype value.  SMT-LIB requires at least two arguments;
       the corresponding shorter HOL lists are vacuously distinct. *)
    (listSyntax.all_distinct_tm, fn (_, ts) =>
      SmtLib_Theories.one_arg (fn list_tm =>
        case Lib.fst (listSyntax.dest_list list_tm) of
          elements as _ :: _ :: _ => ("distinct", elements)
        | _ => ("true", [])) ts),
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
    (intSyntax.divides_tm, fn (_, ts) =>
      SmtLib_Theories.two_args (fn (divisor, dividend) =>
        ("=", literal_int_divides_mod_eq (divisor, dividend))) ts),
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
    (* SMT-LIB has no ceiling operator, but HOL's integer ceiling has the
       closed-form definition ceil r = -floor (-r).  Encode that expression
       directly instead of introducing a quantified defining axiom. *)
    (intrealSyntax.INT_CEILING_tm, fn (_, ts) =>
      SmtLib_Theories.one_arg (fn r =>
        ("-", [Term.mk_comb (intrealSyntax.INT_FLOOR_tm,
          Term.mk_comb (realSyntax.negate_tm, r))])) ts),
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

  (* structural term/type helpers shared via Library (see Library.sml) *)
  val type_contains = Library.type_contains
  val type_contains_word = Library.type_contains_word
  val type_contains_int = Library.type_contains_int
  val type_contains_real = Library.type_contains_real
  val type_contains_string = Library.type_contains_string

  fun type_contains_function ty =
    type_contains is_function_type ty

  val same_const = Library.same_const

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
    same_const intSyntax.mult_tm tm orelse
    same_const realSyntax.mult_tm tm orelse
    same_const int_ediv_tm tm orelse
    same_const int_emod_tm tm

  fun is_string_const tm =
    List.exists (fn c => same_const c tm) [
      stringSyntax.strcat_tm, stringSyntax.isprefix_tm,
      stringSyntax.string_lt_tm, stringSyntax.string_le_tm
    ]

  val subterms = Library.subterms

  val has_quantifier = Library.has_quantifier

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
      strings, datatypes, nonlinear}) =
    String.concatWith "," (List.map Lib.fst (List.filter Lib.snd [
      ("quantifiers", quantifiers),
      ("uninterpreted", uninterpreted),
      ("arrays", arrays),
      ("bitvectors", bitvectors),
      ("integers", integers),
      ("reals", reals),
      ("strings", strings),
      ("datatypes", datatypes),
      ("nonlinear", nonlinear)
    ]))

  fun infer_logic_from_features (features as LogicFeatures {
      quantifiers, uninterpreted, arrays, bitvectors, integers, reals,
      strings, datatypes, nonlinear}) =
    let
      val qf = if quantifiers then "" else "QF_"
      fun datatype_arith_logic () =
        if arrays then
          if integers andalso reals then
            "AUFDT" ^ (if nonlinear then "NIRA" else "LIRA")
          else if integers then
            if nonlinear then "AUFDTNIRA" else "AUFDTLIA"
          else if reals then
            "AUFDT" ^ (if nonlinear then "NIRA" else "LIRA")
          else
            "AUFDTLIA"
        else if integers andalso reals then
          if nonlinear then "UFDTNIRA"
          else qf ^ "UFDTLIRA"
        else if integers then
          if nonlinear then qf ^ "UFDTNIA"
          else qf ^ "UFDTLIA"
        else if reals then
          if nonlinear then "UFDTNIRA"
          else qf ^ "UFDTLIRA"
        else if quantifiers orelse uninterpreted then
          qf ^ "UFDT"
        else
          "QF_DT"
      fun quantified_array_arith_logic () =
        (* Non-QF AUFNIA/AUFNRA are not in the supported logic table here;
           use the recognized A*NIRA/A*LIRA supersets when needed. *)
        if integers andalso reals then
          if uninterpreted then
            "AUF" ^ (if nonlinear then "NIRA" else "LIRA")
          else
            "A" ^ (if nonlinear then "NIRA" else "LIRA")
        else if integers then
          if uninterpreted then
            if nonlinear then "AUFNIRA" else "AUFLIA"
          else
            "A" ^ (if nonlinear then "NIA" else "LIA")
        else if reals then
          if uninterpreted then
            "AUF" ^ (if nonlinear then "NIRA" else "LIRA")
          else
            "A" ^ (if nonlinear then "NIRA" else "LIRA")
        else if uninterpreted then
          "AUFLIA"
        else
          "ALIA"
      fun arith_logic () =
        if integers andalso reals then
          if quantifiers andalso arrays then
            quantified_array_arith_logic ()
          else if quantifiers orelse arrays orelse uninterpreted then
            "AUFNIRA"
          else if nonlinear then qf ^ "NIRA" else qf ^ "LIRA"
        else if integers then
          if arrays then
            if quantifiers then
              quantified_array_arith_logic ()
            else
              qf ^ "AUF" ^ (if nonlinear then "NIA" else "LIA")
          else if uninterpreted then
            (* QF_UFNIA is not an official SMT-LIB logic; widen the
               quantifier-free nonlinear case to the recognized QF_UFNIRA
               superset (the quantified UFNIA case is already official). *)
            if nonlinear andalso not quantifiers then "QF_UFNIRA"
            else qf ^ "UF" ^ (if nonlinear then "NIA" else "LIA")
          else
            qf ^ (if nonlinear then "NIA" else "LIA")
        else if reals then
          if arrays then
            if quantifiers then
              quantified_array_arith_logic ()
            else
              (* QF_AUFNRA / QF_AUFLRA are not official SMT-LIB logics;
                 widen to the recognized QF_AUFNIRA / QF_AUFLIRA supersets. *)
              qf ^ "AUF" ^ (if nonlinear then "NIRA" else "LIRA")
          else if uninterpreted then
            qf ^ "UF" ^ (if nonlinear then "NRA" else "LRA")
          else
            qf ^ (if nonlinear then "NRA" else "LRA")
        else if arrays then
          if quantifiers then quantified_array_arith_logic () else "QF_AX"
        else
          qf ^ "UF"
      fun bitvector_datatype_logic () =
        if integers orelse reals then
          "ALL"
        else if arrays then
          "AUFBVDT"
        else
          "UFBVDT"
      val logic =
        if strings then
          (* Phase 4 will refine UnicodeStrings/RegLan combinations. *)
          if bitvectors orelse reals orelse quantifiers orelse arrays orelse
             uninterpreted orelse datatypes then
            "ALL"
          else if integers then
            if nonlinear then "QF_SNIA" else "QF_SLIA"
          else
            "QF_S"
        else if bitvectors then
          (* Phase 5 will refine FloatingPoint/BV-family combinations. *)
          if datatypes then
            bitvector_datatype_logic ()
          else if integers orelse reals orelse quantifiers then
            "ALL"
          else if arrays then
            if uninterpreted then qf ^ "AUFBV" else qf ^ "ABV"
          else if uninterpreted then
            qf ^ "UFBV"
          else
            qf ^ "BV"
        else if datatypes then
          datatype_arith_logic ()
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

  val smt_reserved_type_names = [
    "Bool", "Int", "Real", "String", "Array", "BitVec"
  ]

  val smt_reserved_term_names = [
    "true", "false", "not", "and", "or", "xor", "=>", "=", "distinct",
    "ite", "select", "store", "div", "mod", "abs", "to_real", "to_int",
    "is_int"
  ]

  fun is_smt_reserved names name = List.exists (fn s => s = name) names

  fun starts_with_alpha s =
    String.size s > 0 andalso Char.isAlpha (String.sub (s, 0))

  fun smt_simple_symbol prefix raw =
    let
      val sanitized = SmtLib_Theories.sanitize_name raw
      val base =
        if starts_with_alpha sanitized then sanitized else prefix ^ sanitized
    in
      if base = prefix then prefix ^ "x" else base
    end

  fun capitalize s =
    if s = "" then "T"
    else
      String.str (Char.toUpper (String.sub (s, 0))) ^
      String.extract (s, 1, NONE)

  fun type_name_stem ty =
    case first_success (fn (_, f) => f ty)
        (TypeNet.match (builtin_types, ty)) of
      SOME name => smt_simple_symbol "T_" name
    | NONE =>
      if Type.is_vartype ty then
        smt_simple_symbol "T_" (Type.dest_vartype ty)
      else if is_function_type ty then
        let
          val (dom, rng) = Type.dom_rng ty
        in
          "Fun_" ^ type_name_stem dom ^ "_" ^ type_name_stem rng
        end
      else
        let
          val {Tyop, Args, ...} = Type.dest_thy_type ty
          val base = smt_simple_symbol "T_" (capitalize Tyop)
        in
          case Args of
            [] => base
          | _ => base ^ "_" ^ String.concatWith "_"
              (List.map type_name_stem Args)
        end

  fun dict_type_names tydict =
    Redblackmap.foldl (fn (_, name, acc) => name :: acc) [] tydict

  fun fresh_smt_name reserved used stem =
    let
      val stem = smt_simple_symbol "S_" stem
      fun unavailable s =
        is_smt_reserved reserved s orelse List.exists (fn t => t = s) used
      fun loop n =
        let
          val candidate =
            if n = 0 then stem else stem ^ "_" ^ Int.toString n
        in
          if unavailable candidate then loop (n + 1) else candidate
        end
    in
      loop 0
    end

  fun same_type (ty1, ty2) = Type.compare (ty1, ty2) = EQUAL

  fun member_type ty tys = List.exists (fn ty' => same_type (ty, ty')) tys

  fun add_type ty tys = if member_type ty tys then tys else ty :: tys

  fun free_datatype_tyinfo tyinfo =
    not (List.null (TypeBasePure.constructors_of tyinfo)) andalso
    Lib.can TypeBasePure.nchotomy_of tyinfo andalso
    Lib.can TypeBasePure.case_def_of tyinfo andalso
    Lib.can TypeBasePure.induction_of tyinfo

  fun datatype_translation_excluded ty = same_type (ty, numSyntax.num)

  fun predicate_domain_type pred =
    let
      val (dom, rng) = Type.dom_rng (Term.type_of pred)
    in
      if same_type (rng, Type.bool) then SOME dom else NONE
    end
    handle Feedback.HOL_ERR _ => NONE

  fun datatype_family_types tyinfo ty =
    let
      val (preds, _) =
        boolSyntax.strip_forall (Thm.concl (TypeBasePure.induction_of tyinfo))
      val patterns = List.mapPartial predicate_domain_type preds
      fun instantiate pattern =
        let val theta = Type.match_type pattern ty
        in List.map (Type.type_subst theta) patterns end
    in
      case Lib.get_first (Lib.total instantiate) patterns of
        SOME family =>
          List.rev (List.foldl (fn (fam_ty, acc) => add_type fam_ty acc)
            [] family)
      | NONE => raise ERR "datatype_family_types" "no matching family member"
    end

  fun datatype_family ty =
    if datatype_translation_excluded ty then
      NONE
    else case TypeBase.fetch ty of
      NONE => NONE
    | SOME tyinfo =>
      if free_datatype_tyinfo tyinfo then
        let
          val family = datatype_family_types tyinfo ty
          val tyinfos = List.map TypeBase.fetch family
        in
          if List.all Option.isSome tyinfos andalso
             List.all (free_datatype_tyinfo o valOf) tyinfos then
            SOME family
          else
            NONE
        end
        handle Feedback.HOL_ERR _ => NONE
      else
        NONE

  fun constructor_name type_name constructor used =
    let
      val raw = #Name (Term.dest_thy_const constructor)
        handle Feedback.HOL_ERR _ => Hol_pp.term_to_string constructor
    in
      fresh_smt_name smt_reserved_term_names used
        ("ctor_" ^ type_name ^ "_" ^ raw)
    end

  fun record_selector_names tyinfo constructor_name fields used =
    let
      fun field_name (_, {accessor, ...} : TypeBasePure.rcd_fieldinfo) =
        #Name (Term.dest_thy_const accessor)
        handle Feedback.HOL_ERR _ => Hol_pp.term_to_string accessor
      fun one ((field, info), (used, acc)) =
        let
          val raw =
            case field_name (field, info) of "" => field | name => name
          val name = fresh_smt_name smt_reserved_term_names used raw
        in
          (name :: used, name :: acc)
        end
      val (_, names) = List.foldl one (used, []) fields
    in
      List.rev names
    end

  fun generated_selector_names type_name constructor_name arity used =
    let
      fun one (n, (used, acc)) =
        let
          val name = fresh_smt_name smt_reserved_term_names used
            ("sel_" ^ type_name ^ "_" ^ constructor_name ^ "_" ^
             Int.toString n)
        in
          (name :: used, name :: acc)
        end
      val (_, names) =
        List.foldl one (used, []) (List.tabulate (arity, fn n => n))
    in
      List.rev names
    end

  fun datatype_constructor_infos ty type_name =
    let
      val tyinfo =
        case TypeBase.fetch ty of
          SOME info => info
        | NONE => raise ERR "datatype_constructor_infos"
            "missing TypeBase entry"
      val fields = TypeBasePure.fields_of tyinfo
      fun one (constructor, (used, acc)) =
        let
          val constructor = TypeBasePure.cinst ty constructor
          val cname = constructor_name type_name constructor used
          val (doms, _) = boolSyntax.strip_fun (Term.type_of constructor)
          val selector_names =
            if not (List.null fields) andalso List.length doms =
               List.length fields then
              record_selector_names tyinfo cname fields (cname :: used)
            else
              generated_selector_names type_name cname (List.length doms)
                (cname :: used)
          val selectors = ListPair.zipEq (selector_names, doms)
          val used = cname :: selector_names @ used
        in
          (used, (constructor, cname, selectors) :: acc)
        end
      val (_, infos) =
        List.foldl one (smt_reserved_term_names, [])
          (TypeBasePure.constructors_of tyinfo)
    in
      List.rev infos
    end

  fun type_decl_record (ty, name) =
    TypeDeclaration {hol_type = ty, smt_name = name,
      declaration = "(declare-sort " ^ name ^ " 0)\n"}

  fun datatype_declaration_text sort_of family names =
    let
      val name_of = ListPair.zipEq (family, names)
      fun lookup_name ty =
        case List.find (fn (ty', _) => same_type (ty, ty')) name_of of
          SOME (_, name) => name
        | NONE => raise ERR "datatype_declaration_text" "missing family name"
      fun constructor_decs (ty, type_name) =
        let
          val tyinfo =
            case TypeBase.fetch ty of
              SOME info => info
            | NONE => raise ERR "datatype_declaration_text"
                "missing TypeBase entry"
          val infos = datatype_constructor_infos ty type_name
          fun one (_, cname, selectors) =
            let
              val selectors = List.map
                (fn (sel, dom) => "(" ^ sel ^ " " ^ sort_of dom ^ ")")
                selectors
            in
              "(" ^ cname ^
              (case selectors of
                [] => ""
              | _ => " " ^ String.concatWith " " selectors) ^ ")"
            end
          val cdecs = List.map one infos
        in
          "(" ^ String.concatWith " " cdecs ^ ")"
        end
      val sort_decls = List.map (fn name => "(" ^ name ^ " 0)") names
      val datatype_decls = ListPair.mapEq constructor_decs (family, names)
    in
      "(declare-datatypes (" ^ String.concatWith " " sort_decls ^ ") (" ^
      String.concatWith " " datatype_decls ^ "))\n"
    end

  fun datatype_decl_record tydict ty =
    case datatype_family ty of
      NONE => NONE
    | SOME family =>
      let
        val names = List.map (fn fam_ty => Redblackmap.find (tydict, fam_ty))
          family
        val declaration = datatype_declaration_text
          (smt_sort_of_type tydict) family names
      in
        SOME (DatatypeDeclaration {hol_types = family, smt_names = names,
          declaration = declaration}, family)
      end
      handle Redblackmap.NotFound => NONE
           | Feedback.HOL_ERR _ => NONE

  fun infer_features terms tydict tmdict =
    let
      fun encoding_subterms tm =
        let
          fun walk (tm, acc) =
            tm ::
            (if listSyntax.is_all_distinct tm then
               let
                 val (elements, _) =
                   listSyntax.dest_list (listSyntax.dest_all_distinct tm)
               in
                 List.foldl (fn (element, rest) => walk (element, rest))
                   acc elements
               end
             else
               (let val (rator, rand) = Term.dest_comb tm
                in walk (rator, walk (rand, acc)) end
                handle Feedback.HOL_ERR _ =>
                  (let val (_, body) = Term.dest_abs tm
                   in walk (body, acc) end
                   handle Feedback.HOL_ERR _ => acc)))
        in
          walk (tm, [])
        end
      val all_subterms = List.concat (List.map encoding_subterms terms)
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
      fun type_is_datatype ty =
        not (has_type_builtin ty) andalso Option.isSome (datatype_family ty)
      fun type_contains_datatype ty =
        type_contains type_is_datatype ty
      fun term_is_datatype_constructor tm =
        TypeBase.is_constructor tm
      fun term_is_datatype_record_selector tm =
        let
          val (dom, _) = Type.dom_rng (Term.type_of tm)
          val tyinfo =
            case TypeBase.fetch dom of
              SOME info => info
            | NONE => raise ERR "infer_features" "not a datatype selector"
          val fields = TypeBasePure.fields_of tyinfo
        in
          List.exists
            (fn (_, {accessor, ...} : TypeBasePure.rcd_fieldinfo) =>
               Term.same_const tm accessor)
            fields
        end
      fun term_is_datatype_native ((tm, arity), _) =
        (arity = 0 andalso type_contains_datatype (Term.type_of tm)) orelse
        term_is_datatype_constructor tm orelse
        (case Lib.total term_is_datatype_record_selector tm of
           SOME result => result
         | NONE => false)
      val datatypes =
        subterm_types type_contains_datatype orelse
        Redblackmap.foldl (fn (ty, _, b) =>
          b orelse type_contains_datatype ty) false tydict orelse
        Redblackmap.foldl (fn ((tm, _), _, b) =>
          b orelse type_contains_datatype (Term.type_of tm)) false tmdict
      val nonlinear =
        List.exists (fn tm => is_nonlinear_arith_const
          (Lib.fst (boolSyntax.strip_comb tm))) all_subterms
      val has_uninterpreted_type =
        Redblackmap.foldl (fn (ty, _, b) =>
          b orelse not (type_contains_datatype ty)) false tydict
      fun range_after 0 ty = ty
        | range_after n ty = range_after (n - 1) (Lib.snd (Type.dom_rng ty))
      fun term_needs_uf ((tm, arity), _) =
        if term_is_datatype_native ((tm, arity), "") then
          false
        else
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
        reals = reals, strings = strings, datatypes = datatypes,
        nonlinear = nonlinear}
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
          translate = true,
          replay = true,
          notes =
            "SMT-LIB datatype commands are parsed/typechecked; HOL TypeBase " ^
            "datatypes are emitted as native SMT-LIB Datatypes with checked " ^
            "constructor, selector, tester, exhaustiveness, and acyclicity replay.",
          proof_obligation =
            "Replay is checked for TypeBase-backed constructor disjointness, injectivity, selectors, testers, exhaustiveness, and acyclicity; unsupported certificate shapes remain explicit diagnostics."
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
      fun add_type_record (ty, name, (seen, acc)) =
        if member_type ty seen then
          (seen, acc)
        else
          case datatype_decl_record tydict ty of
            SOME (record, family) =>
              (List.foldl (fn (fam_ty, seen) => add_type fam_ty seen)
                seen family, record :: acc)
          | NONE =>
              (add_type ty seen, type_decl_record (ty, name) :: acc)
      val (_, type_records) = Redblackmap.foldl add_type_record ([], []) tydict
      val term_records = Redblackmap.foldl (fn (key, name, acc) =>
        term_decl_for_tmdict tydict (key, name) :: acc) [] tmdict
      val builtin_records = encoded_symbol_records terms
      val advanced_records = advanced_encoding_records terms
    in
      logic_record :: List.rev type_records @ List.rev term_records @
      List.rev builtin_records @ advanced_records
    end

  fun datatype_tester_term ty constructor arg =
    let
      val type_name = type_name_stem ty
      val infos = datatype_constructor_infos ty type_name
      fun clause (constructor', _, _) =
        let
          val (doms, _) = boolSyntax.strip_fun (Term.type_of constructor')
          val vars = List.map Term.genvar doms
          val pat = Term.list_mk_comb (constructor', vars)
          val result =
            if Term.same_const constructor constructor' then boolSyntax.T
            else boolSyntax.F
        in
          (pat, result)
        end
    in
      TypeBase.mk_case (arg, List.map clause infos)
    end

  fun datatype_selector_term ty constructor selector_index arg =
    let
      val type_name = type_name_stem ty
      val infos = datatype_constructor_infos ty type_name
      val selector_ty =
        case List.find (fn (constructor', _, _) =>
            Term.same_const constructor constructor') infos of
          SOME (_, _, selectors) => Lib.snd (List.nth (selectors, selector_index))
        | NONE => raise ERR "datatype_selector_term" "missing constructor"
      fun clause (constructor', _, _) =
        let
          val (doms, _) = boolSyntax.strip_fun (Term.type_of constructor')
          val vars = List.map Term.genvar doms
          val pat = Term.list_mk_comb (constructor', vars)
          val result =
            if Term.same_const constructor constructor' then
              List.nth (vars, selector_index)
            else
              boolSyntax.mk_arb selector_ty
        in
          (pat, result)
        end
    in
      TypeBase.mk_case (arg, List.map clause infos)
    end

  fun add_datatype_parser_entries (ty, type_name, dict) =
    let
      val infos = datatype_constructor_infos ty type_name
      fun add_constructor ((constructor, cname, selectors), dict) =
        let
          val (doms, _) = boolSyntax.strip_fun (Term.type_of constructor)
          val arity = List.length doms
          fun constructor_parse token indices args =
            if List.null indices andalso List.length args = arity then
              Term.list_mk_comb (constructor, args)
            else
              raise ERR ("<" ^ token ^ ">") "wrong number of arguments"
          fun selector_entry ((selector_index, (selector_name, _)), dict) =
            let
              fun selector_parse token indices args =
                case (indices, args) of
                  ([], [arg]) =>
                    datatype_selector_term ty constructor selector_index arg
                | _ => raise ERR ("<" ^ token ^ ">")
                    "one argument expected"
            in
              Library.extend_dict ((selector_name, selector_parse), dict)
            end
          fun tester_parse token indices args =
            case (indices, args) of
              ([index], [arg]) =>
                let
                  val index_matches_constructor =
                    Term.same_const index constructor
                    handle Feedback.HOL_ERR _ => false
                  val index_name =
                    Lib.fst (Term.dest_var index)
                    handle Feedback.HOL_ERR _ =>
                      #Name (Term.dest_thy_const index)
                in
                  if index_name = cname orelse index_matches_constructor then
                    datatype_tester_term ty constructor arg
                  else
                    raise ERR ("<" ^ token ^ " " ^ cname ^ ">")
                      "tester constructor mismatch"
                end
            | _ => raise ERR ("<" ^ token ^ " " ^ cname ^ ">")
                "one constructor index and one argument expected"
          val dict = Library.extend_dict ((cname, constructor_parse), dict)
          val dict = Library.extend_dict (("is", tester_parse), dict)
          val numbered = ListPair.zipEq
            (List.tabulate (List.length selectors, fn n => n), selectors)
        in
          List.foldl selector_entry dict numbered
        end
    in
      List.foldl add_constructor dict infos
    end

  fun parser_dicts_for_translation_aux ({logic, tydict, tmdict, ...} : translation) =
    let
      fun parsedicts_for_logic logic =
        SmtLib_Logics.parsedicts_of_logic logic
        handle e as Feedback.HOL_ERR _ =>
          if String.isSubstring "DT" logic then
            SmtLib_Logics.parsedicts_of_logic "ALL"
          else
            raise e
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
      val tm_dict = Redblackmap.foldl (fn (ty, name, dict) =>
        case datatype_family ty of
          SOME _ => add_datatype_parser_entries (ty, name, dict)
        | NONE => dict) tm_dict tydict
      val (logic_tydict, logic_tmdict) = parsedicts_for_logic logic
    in
      (Library.union_dict logic_tydict ty_dict,
       Library.union_dict logic_tmdict tm_dict)
    end

  (* returns an updated accumulator, a (possibly empty) list of
     SMT-LIB type declarations, and the SMT-LIB representation of the
     given type *)
  fun uninterpreted_type (tydict, ty) =
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
  fun translate_type (tydict, ty) =
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
      case first_success (fn (_, f) => f ty)
          (TypeNet.match (builtin_types, ty)) of
        SOME name => (tydict, ([], name))
      | NONE =>
        (case Redblackmap.peek (tydict, ty) of
          SOME name => (tydict, ([], name))
        | NONE =>
          (case translate_datatype_type (tydict, ty) of
            SOME result => result
          | NONE =>
            let
              val _ =
                case TypeBase.fetch ty of
                  SOME _ =>
                    if !Library.trace > 0 then
                      WARNING "translate_type"
                        ("datatype fallback for " ^ Hol_pp.type_to_string ty)
                    else
                      ()
                | NONE => ()
            in
              uninterpreted_type (tydict, ty)
            end))
  and translate_datatype_type (tydict, ty) =
    case datatype_family ty of
      NONE => NONE
    | SOME family =>
      let
        val used0 = dict_type_names tydict @ smt_reserved_type_names
        fun add_name (fam_ty, (used, acc)) =
          let
            val name = fresh_smt_name smt_reserved_type_names used
              (type_name_stem fam_ty)
          in
            (name :: used, name :: acc)
          end
        val (_, names_rev) = List.foldl add_name (used0, []) family
        val names = List.rev names_rev
        val tydict_with_family = ListPair.foldlEq
          (fn (fam_ty, name, dict) => Redblackmap.insert (dict, fam_ty, name))
          tydict (family, names)
        fun translate_constructor_doms (fam_ty, (dict, decls)) =
          let
            val tyinfo =
              case TypeBase.fetch fam_ty of
                SOME info => info
              | NONE => raise ERR "translate_datatype_type"
                  "missing TypeBase entry"
            fun translate_one (constructor, (dict, decls)) =
              let
                val constructor = TypeBasePure.cinst fam_ty constructor
                val (doms, _) = boolSyntax.strip_fun (Term.type_of constructor)
                fun translate_dom (dom, (dict, decls)) =
                  let val (dict, (new_decls, _)) = translate_type (dict, dom)
                  in (dict, decls @ new_decls) end
              in
                List.foldl translate_dom (dict, decls) doms
              end
          in
            List.foldl translate_one (dict, decls)
              (TypeBasePure.constructors_of tyinfo)
          end
        val (tydict, dependency_decls) =
          List.foldl translate_constructor_doms (tydict_with_family, []) family
        val declaration = datatype_declaration_text
          (smt_sort_of_type tydict) family names
        val name =
          case Redblackmap.peek (tydict, ty) of
            SOME n => n
          | NONE => raise ERR "translate_datatype_type" "unregistered type"
      in
        SOME (tydict, (dependency_decls @ [declaration], name))
      end
      handle Feedback.HOL_ERR _ => NONE
           | Redblackmap.NotFound => NONE

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
    fun beta_reduce t =
      boolSyntax.rhs (Thm.concl (Drule.LIST_BETA_CONV t))
      handle Feedback.HOL_ERR _ => t
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
    fun ensure_type ((tydict, tmdict), ty) =
      let val (tydict, (decls, name)) = translate_type (tydict, ty)
      in (((tydict, tmdict), decls), name) end
    fun constructor_info_for tydict ty constructor =
      let
        val type_name =
          case Redblackmap.peek (tydict, ty) of
            SOME name => name
          | NONE => raise ERR "translate_term" "datatype type not registered"
        val infos = datatype_constructor_infos ty type_name
      in
        case List.find (fn (constructor', _, _) =>
            Term.same_const constructor constructor') infos of
          SOME info => info
        | NONE => raise ERR "translate_term" "constructor name not found"
      end
    fun translate_constructor_application acc rator rands =
      let
        val _ = TypeBase.is_constructor rator
        val (doms, data_ty) = boolSyntax.strip_fun (Term.type_of rator)
        val arity = List.length doms
        val _ =
          if List.length rands = arity then ()
          else raise ERR "translate_term" "partial constructor application"
        val (((tydict, tmdict), typedecls), _) = ensure_type (acc, data_ty)
        val (_, cname, _) = constructor_info_for tydict data_ty rator
        val tmdict = Redblackmap.insert (tmdict, (rator, arity), cname)
        val acc = (tydict, tmdict)
        val (acc, declnames) = Lib.foldl_map
          (fn (a, t) => translate_term (a, (bounds, t))) (acc, rands)
        val (declss, names) = Lib.split declnames
      in
        (acc, (typedecls @ List.concat declss, sexpr cname names))
      end
    fun selector_case_match match_tydict elem clauses =
      let
        val data_ty = Term.type_of elem
        val type_name = Redblackmap.find (match_tydict, data_ty)
        val infos = datatype_constructor_infos data_ty type_name
        fun clause_for constructor =
          List.find (fn (pat, _) =>
            let val (pat_rator, _) = boolSyntax.strip_comb pat
            in Term.same_const constructor pat_rator end) clauses
        fun rhs_is_arb rhs = boolSyntax.is_arb rhs
        fun selector_for (constructor, _, selectors) =
          let
            val (doms, _) = boolSyntax.strip_fun (Term.type_of constructor)
            val indices = List.tabulate (List.length doms, fn n => n)
            fun try_index n =
              case clause_for constructor of
                SOME (pat, rhs) =>
                  let val (_, vars) = boolSyntax.strip_comb pat
                  in
                    if List.length vars = List.length doms andalso
                       Term.aconv rhs (List.nth (vars, n)) andalso
                       List.all (fn (constructor', _, _) =>
                         Term.same_const constructor constructor' orelse
                         (case clause_for constructor' of
                            SOME (_, rhs') => rhs_is_arb rhs'
                          | NONE => false)) infos
                    then SOME (Lib.fst (List.nth (selectors, n)))
                    else NONE
                  end
              | NONE => NONE
          in
            Lib.get_first try_index indices
          end
      in
        Lib.get_first selector_for infos
      end
    fun translate_selector_case acc =
      let
        val (_, elem, clauses) = TypeBase.dest_case tm
        val (((tydict, tmdict), typedecls), _) =
          ensure_type (acc, Term.type_of elem)
        val selector_name =
          case selector_case_match tydict elem clauses of
            SOME name => name
          | NONE => raise ERR "translate_term" "not a selector case"
        val acc = (tydict, tmdict)
        val (acc, (elemdecls, elemname)) = translate_term (acc, (bounds, elem))
      in
        (acc, (typedecls @ elemdecls, sexpr selector_name [elemname]))
      end
    fun translate_case_constant acc rator rands =
      let
        val (elem, cases) =
          case rands of
            elem :: cases => (elem, cases)
          | [] => raise ERR "translate_term" "case constant without scrutinee"
        val data_ty = Term.type_of elem
        val tyinfo =
          case TypeBase.fetch data_ty of
            SOME info => info
          | NONE => raise ERR "translate_term" "case scrutinee not datatype"
        val _ =
          if Term.same_const rator (TypeBasePure.case_const_of tyinfo) then ()
          else raise ERR "translate_term" "not datatype case constant"
        val _ =
          if List.length cases = List.length (TypeBasePure.constructors_of tyinfo)
          then ()
          else raise ERR "translate_term" "wrong number of case branches"
        val (((tydict, tmdict), typedecls), _) = ensure_type (acc, data_ty)
        val type_name = Redblackmap.find (tydict, data_ty)
        val infos = datatype_constructor_infos data_ty type_name
        fun selector_terms (constructor, _, selectors) =
          List.map (fn n => datatype_selector_term data_ty constructor n elem)
            (List.tabulate (List.length selectors, fn n => n))
        fun branch_term (casefn, info) =
          beta_reduce (Term.list_mk_comb (casefn, selector_terms info))
        val branch_terms = ListPair.mapEq branch_term (cases, infos)
        val acc = (tydict, tmdict)
        val (acc, (elemdecls, elemname)) = translate_term (acc, (bounds, elem))
        val (acc, declbranches) = Lib.foldl_map
          (fn (a, t) => translate_term (a, (bounds, t))) (acc, branch_terms)
        val (branchdeclss, branchnames) = Lib.split declbranches
        fun tester (_, cname, _) = sexpr ("(_ is " ^ cname ^ ")") [elemname]
        fun cascaded [] [] = raise ERR "translate_term" "empty datatype case"
          | cascaded [_] [branch] = branch
          | cascaded (info :: infos) (branch :: branches) =
              sexpr "ite" [tester info, branch, cascaded infos branches]
          | cascaded _ _ = raise ERR "translate_term" "case branch mismatch"
      in
        (acc, (typedecls @ elemdecls @ List.concat branchdeclss,
          cascaded infos branchnames))
      end
    fun translate_record_selector acc =
      let
        val (select, x) = Term.dest_comb tm
        val (_, select_ty) = Term.dest_const select
        val (record_ty, rng_ty) = Type.dom_rng select_ty
        val fields = TypeBase.fields_of record_ty
        val _ = if List.null fields then
            raise ERR "translate_term" "not a record selector"
          else ()
        val j = Lib.index (fn (_, {ty = field_ty, accessor, ...}) =>
            Term.same_const select accessor andalso
            Lib.can (Type.match_type field_ty) rng_ty) fields
        val (((tydict, tmdict), typedecls), _) = ensure_type (acc, record_ty)
        val type_name = Redblackmap.find (tydict, record_ty)
        val infos = datatype_constructor_infos record_ty type_name
        val (_, _, selectors) =
          case infos of
            [info] => info
          | _ => raise ERR "translate_term" "record has multiple constructors"
        val selector_name = Lib.fst (List.nth (selectors, j))
        val tmdict = Redblackmap.insert (tmdict, (select, 1), selector_name)
        val acc = (tydict, tmdict)
        val (acc, (xdecls, xname)) = translate_term (acc, (bounds, x))
      in
        (acc, (typedecls @ xdecls, sexpr selector_name [xname]))
      end
    fun translate_record_update acc =
      let
        val (update_f, x) = Term.dest_comb tm
        val (update, f) = Term.dest_comb update_f
        val new_val =
          combinSyntax.dest_K_1 f
          handle Feedback.HOL_ERR _ =>
            let
              val (var1, body) = Term.dest_abs f
              val (k_tm, var2) = Term.dest_comb body
              val _ =
                if Term.aconv var1 var2 then ()
                else raise ERR "translate_term"
                  "record update function not in eta-long form"
            in
              combinSyntax.dest_K_1 k_tm
            end
        val record_ty = Term.type_of x
        val fields = TypeBase.fields_of record_ty
        val _ = if List.null fields then
            raise ERR "translate_term" "not a record update"
          else ()
        val val_ty = Term.type_of new_val
        val j = Lib.index (fn (_, {ty = field_ty, fupd, ...}) =>
            Term.same_const update fupd andalso
            Lib.can (Type.match_type field_ty) val_ty) fields
        val (((tydict, tmdict), typedecls), _) = ensure_type (acc, record_ty)
        val type_name = Redblackmap.find (tydict, record_ty)
        val infos = datatype_constructor_infos record_ty type_name
        val (_, cname, selectors) =
          case infos of
            [info] => info
          | _ => raise ERR "translate_term" "record has multiple constructors"
        val acc = (tydict, tmdict)
        val (acc, (xdecls, xname)) = translate_term (acc, (bounds, x))
        val (acc, (newdecls, newname)) =
          translate_term (acc, (bounds, new_val))
        fun field_name (n, (selector_name, _)) =
          if n = j then newname else sexpr selector_name [xname]
        val field_names = ListPair.mapEq field_name
          (List.tabulate (List.length selectors, fn n => n), selectors)
      in
        (acc, (typedecls @ xdecls @ newdecls, sexpr cname field_names))
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

      translate_constructor_application acc rator rands
    handle Feedback.HOL_ERR _ =>

      translate_selector_case acc
    handle Feedback.HOL_ERR _ =>

      translate_case_constant acc rator rands
    handle Feedback.HOL_ERR _ =>

      translate_record_selector acc
    handle Feedback.HOL_ERR _ =>

      translate_record_update acc
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
  fun goal_to_SmtLib_aux (policy : logic_selection_policy)
      (ts, t) : translation * string list =
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
      case policy {features = features, inferred_logic = inferred_logic,
                   reason = reason} of
        NONE => (inferred_logic, reason)
      | SOME {logic, reason} => (logic, reason)
    val records = fn () =>
      build_translation_records terms selected_logic reason features tydict tmdict
    val translation = {logic = selected_logic, tydict = tydict,
      tmdict = tmdict, records = records}
    (* we choose to intertwine declarations and assertions (for no
       particular reason; an alternative would be to emit all
       declarations before all assertions) *)
    val smtlibs = List.foldl
      (fn ((xs, s), acc) => acc @ xs @ ["(assert " ^ s ^ ")\n"]) [] smtlibs
  in
    (* A `(set-logic ...)` is always emitted, including on the implicit
       (no caller override) Z3/CVC path.  Older revisions emitted none for
       `NONE`, letting the solver default to accept-anything; relying on
       that default is fragile.  Emitting unconditionally is safe because
       `infer_logic_from_features` is a sound over-approximation of the
       goal's theory needs: every theory Phase 1 can translate contributes
       a feature, any multiplication is treated as nonlinear, and any
       un-modelled feature combination falls back to `ALL`.  So the
       declared fragment never excludes a term the goal actually contains
       (a too-narrow fragment would make the solver reject a goal it could
       otherwise prove), and the emitted name is always a recognised logic
       (see `infer_logic_from_features` and `parsedicts_of_logic`).  Any
       future widening of what Phase >1 can translate must preserve this
       invariant — add the feature and its logic mapping together, or keep
       the `ALL` fallback. *)
    (translation, ["(set-logic " ^ selected_logic ^ ")\n"] @ [
      "(set-info :source |Automatically generated from HOL4 by SmtLib.goal_to_SmtLib.\n",
      "Copyright (c) 2011 Tjark Weber. All rights reserved.|)\n",
      "(set-info :smt-lib-version 2.7)\n"
    ] @ smtlibs @ [
      "(check-sat)\n"
    ])
  end

  fun num_binder_to_int_once_conv tm =
  let
    fun is_num_var v = Type.compare (Term.type_of v, numSyntax.num) = EQUAL
    val is_num_forall =
      boolSyntax.is_forall tm andalso
      is_num_var (Lib.fst (boolSyntax.dest_forall tm))
    val is_num_exists =
      boolSyntax.is_exists tm andalso
      is_num_var (Lib.fst (boolSyntax.dest_exists tm))
  in
    if is_num_forall then
      Conv.HO_REWR_CONV HolSmtTheory.NUM_FORALL_TO_INT tm
    else if is_num_exists then
      Conv.HO_REWR_CONV HolSmtTheory.NUM_EXISTS_TO_INT tm
    else
      Conv.NO_CONV tm
  end

  fun NUM_BINDERS_TO_INT_CONV tm =
    Conv.THENC
      (Conv.TOP_DEPTH_CONV num_binder_to_int_once_conv,
       Conv.TOP_DEPTH_CONV Thm.BETA_CONV) tm
    handle Conv.UNCHANGED => Thm.REFL tm

  val exp_one_rewrites =
  let
    val th = Drule.SPEC_ALL arithmeticTheory.EXP_1
  in
    List.map Drule.GEN_ALL [Thm.CONJUNCT1 th, Thm.CONJUNCT2 th]
  end

  val INT_EXP_1 =
  let
    val i = Term.mk_var ("i", intSyntax.int_ty)
    val th =
      Thm.SPEC numSyntax.zero_tm
        (Thm.SPEC i (Thm.CONJUNCT2 integerTheory.int_exp))
  in
    Drule.GEN_ALL
      (simpLib.SIMP_RULE pureSimps.pure_ss
        [Thm.CONJUNCT1 integerTheory.int_exp, integerTheory.INT_MUL_RID,
         Conv.GSYM arithmeticTheory.ONE]
        th)
  end

  val INT_EXP_BASE_1 =
  let
    val n = Term.mk_var ("n", numSyntax.num)
    val one = numSyntax.mk_numeral Arbnum.one
    val th = Thm.SPEC n (Thm.SPEC one integerTheory.INT_EXP)
  in
    Drule.GEN_ALL
      (simpLib.SIMP_RULE pureSimps.pure_ss
        [List.hd exp_one_rewrites, integerTheory.INT] th)
  end

  val INT_EXP_2 =
  let
    val i = Term.mk_var ("i", intSyntax.int_ty)
    val one = numSyntax.mk_numeral Arbnum.one
    val th =
      Thm.SPEC one (Thm.SPEC i (Thm.CONJUNCT2 integerTheory.int_exp))
  in
    Drule.GEN_ALL
      (simpLib.SIMP_RULE pureSimps.pure_ss
         [INT_EXP_1, Conv.GSYM arithmeticTheory.TWO] th)
  end

  val INT_EXP_3 =
  let
    val i = Term.mk_var ("i", intSyntax.int_ty)
    val two = numSyntax.mk_numeral (Arbnum.fromInt 2)
    val th =
      numLib.REDUCE_RULE
        (Thm.SPEC two (Thm.SPEC i (Thm.CONJUNCT2 integerTheory.int_exp)))
  in
    Drule.GEN_ALL
      (simpLib.SIMP_RULE pureSimps.pure_ss
        [INT_EXP_2, integerTheory.INT_MUL_ASSOC] th)
  end

  val REAL_POW_3 =
  let
    val x = Term.mk_var ("x", realSyntax.real_ty)
    val two = numSyntax.mk_numeral (Arbnum.fromInt 2)
    val th =
      numLib.REDUCE_RULE
        (Thm.SPEC two (Thm.SPEC x (Thm.CONJUNCT2 realTheory.pow)))
  in
    Drule.GEN_ALL
      (simpLib.SIMP_RULE pureSimps.pure_ss
        [realTheory.POW_2, realTheory.REAL_MUL_ASSOC] th)
  end

  (* Unfold a real power with an arbitrary numeral exponent.  The recursive
     equations only syntactically match zero/SUC, whereas HOL numerals are
     binary terms; specialize the step equation to the predecessor and reduce
     that numeral before descending into the remaining power. *)
  fun REAL_POW_NUMERAL_CONV tm =
  let
    val (rator, args) = boolSyntax.strip_comb tm
    val _ =
      if Term.same_const rator realSyntax.exp_tm then ()
      else raise Conv.UNCHANGED
    val (x, n) = Lib.pair_of_list args
    val n = numSyntax.dest_numeral n
    val th =
      if n = Arbnum.zero then
        Thm.SPEC x (Thm.CONJUNCT1 realTheory.pow)
      else
        numLib.REDUCE_RULE
          (Thm.SPEC (numSyntax.mk_numeral (Arbnum.- (n, Arbnum.one)))
            (Thm.SPEC x (Thm.CONJUNCT2 realTheory.pow)))
    val rhs = boolSyntax.rhs (Thm.concl th)
    val rhs_th = Conv.DEPTH_CONV REAL_POW_NUMERAL_CONV rhs
      handle Conv.UNCHANGED => Thm.REFL rhs
  in
    Thm.TRANS th rhs_th
  end

  (* Discharge a positive real power with a concrete base before its symbolic
     nat exponent reaches the serializer.  This uses the general REAL_POW_LT
     theorem; only its closed arithmetic side-goal is evaluated here. *)
  fun REAL_POW_POS_LITERAL_CONV tm =
  let
    val (rel, args) = boolSyntax.strip_comb tm
    val _ =
      if Term.same_const rel realSyntax.less_tm then ()
      else raise Conv.UNCHANGED
    val (zero, pow_tm) = Lib.pair_of_list args
    val (pow_const, pow_args) = boolSyntax.strip_comb pow_tm
    val _ =
      if Term.same_const pow_const realSyntax.exp_tm then ()
      else raise Conv.UNCHANGED
    val (base, exponent) = Lib.pair_of_list pow_args
    val positive =
      Tactical.TAC_PROOF
        (([], realSyntax.mk_less (zero, base)),
         Tactical.THEN
           (simpLib.SIMP_TAC pureSimps.pure_ss
             [Conv.GSYM intrealTheory.real_of_int_num,
              intrealTheory.real_of_int_lt],
            intLib.ARITH_TAC))
    val pow_positive =
      Thm.MP
        (Thm.SPEC exponent (Thm.SPEC base realTheory.REAL_POW_LT)) positive
    val _ =
      if Term.aconv (Thm.concl pow_positive) tm then ()
      else raise Conv.UNCHANGED
  in
    Drule.EQT_INTRO pow_positive
  end
  handle Feedback.HOL_ERR _ => raise Conv.UNCHANGED

  fun thm_rhs_is_true th =
  let
    val (_, rhs) = boolSyntax.dest_eq (Thm.concl th)
  in
    Term.aconv rhs boolSyntax.T
  end

  fun INT_DIVIDES_LITERAL_MOD_CONV tm =
  let
    val (divisor, _) = intSyntax.dest_divides tm
    val zero = intSyntax.term_of_int Arbint.zero
    val _ =
      if intSyntax.is_int_literal divisor then ()
      else raise ERR "INT_DIVIDES_LITERAL_MOD_CONV" "non-literal divisor"
    val pos_th =
      simpLib.SIMP_CONV intLib.int_ss []
        (intSyntax.mk_less (zero, divisor))
    val _ =
      if thm_rhs_is_true pos_th then ()
      else raise ERR "INT_DIVIDES_LITERAL_MOD_CONV" "non-positive divisor"
    val nz_th =
      simpLib.SIMP_CONV intLib.int_ss []
        (boolSyntax.mk_neg (boolSyntax.mk_eq (divisor, zero)))
    val z_th =
      simpLib.SIMP_CONV intLib.int_ss []
        (boolSyntax.mk_eq (divisor, zero))
  in
    Conv.THENC
      (Conv.REWR_CONV integerTheory.INT_DIVIDES_MOD0,
       simpLib.SIMP_CONV pureSimps.pure_ss [
         pos_th, nz_th, z_th, integerTheory.INT_MOD_EMOD,
         boolTheory.COND_CLAUSES, boolTheory.AND_CLAUSES,
         boolTheory.OR_CLAUSES
       ]) tm
  end

  val num_transfer_rewrites = [
    HolSmtTheory.int_num_floor_total,
    HolSmtTheory.int_num_ceiling_total,
    HolSmtTheory.num_floor_to_int_eq,
    HolSmtTheory.num_ceiling_to_int_eq,
    HolSmtTheory.num_floor_nonpos,
    HolSmtTheory.num_sub_assoc,
    integerTheory.NUM_OF_INT,
    integerTheory.Num_EQ_ABS,
    integerTheory.INT_ABS,
    (* Prefer the guarded cancellation when a transferred natural has its
       standard non-negativity hypothesis; Num_EQ_ABS remains the total
       fallback for genuinely unguarded integer-to-natural conversions. *)
    HolSmtTheory.NUM_TO_INT_GUARDED,
    intrealTheory.INT_NUM_FLOOR,
    intrealTheory.INT_NUM_CEILING,
    realTheory.NUM_CEILING_BASE,
    (* Eliminate symbolic natural exponents whenever their real base makes
       the result independent of the exponent or establishes its sign. *)
    realTheory.POW_ONE,
    realTheory.REAL_POW_LT,
    (* These definitions can be introduced by ADD_THEOREMS_TAC after the
       first transfer pass.  Keep the final pass in the SMT-LIB fragment
       rather than serializing their quantified HOL definitions. *)
    integerTheory.INT_MAX,
    integerTheory.INT_MIN,
    HolSmtTheory.real_div_smt_rdiv,
    integerTheory.INT_POS,
    Conv.GSYM integerTheory.INT_INJ,
    Conv.GSYM integerTheory.INT_LE,
    Conv.GSYM integerTheory.INT_LT,
    Conv.GSYM integerTheory.INT_ADD,
    Conv.GSYM integerTheory.INT_MUL
  ] @ exp_one_rewrites @
    (* These equations only match syntactic numerals.  Keeping both base and
       step equations lets SIMP unfold every literal exponent, rather than
       the historical 1/2/3 subset, while leaving symbolic exponents alone. *)
    [Thm.CONJUNCT1 arithmeticTheory.EXP,
     Thm.CONJUNCT2 arithmeticTheory.EXP,
     Thm.CONJUNCT1 integerTheory.int_exp,
     Thm.CONJUNCT2 integerTheory.int_exp] @ [
    arithmeticTheory.ZERO_LT_EXP,
    Conv.GSYM integerTheory.INT_EXP,
    INT_EXP_1,
    INT_EXP_BASE_1,
    INT_EXP_2,
    INT_EXP_3,
    integerTheory.INT,
    int_arithTheory.INT_NUM_SUB,
    HolSmtTheory.INT_NUM_EDIV,
    HolSmtTheory.INT_NUM_EMOD,
    Conv.GSYM int_arithTheory.INT_NUM_DIVIDES,
    int_arithTheory.INT_NUM_COND,
    arithmeticTheory.GREATER_DEF,
    arithmeticTheory.GREATER_EQ,
    arithmeticTheory.MAX_DEF,
    arithmeticTheory.MIN_DEF,
    Drule.GEN_ALL (Thm.SYM intrealTheory.real_of_int_num)
  ]

  fun NUM_TO_INT_CONV tm =
    Conv.THENC
      (NUM_BINDERS_TO_INT_CONV,
       simpLib.SIMP_CONV pureSimps.pure_ss num_transfer_rewrites) tm
    handle Conv.UNCHANGED => Thm.REFL tm

  fun num_free_concl_vars (asms, concl) =
  let
    fun is_num_var v =
      Term.is_var v andalso
      Type.compare (Term.type_of v, numSyntax.num) = EQUAL
    val asm_fvs = List.concat (List.map Term.free_vars asms)
    fun free_in_asms v = List.exists (fn w => Term.aconv v w) asm_fvs
  in
    List.filter (fn v => is_num_var v andalso not (free_in_asms v))
      (Term.free_vars concl)
  end

  fun SPEC_NUM_FREE_VARS_TAC g =
  let
    val vars = num_free_concl_vars g
  in
    Tactical.MAP_EVERY (fn v => Tactic.SPEC_TAC (v, v)) vars g
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
        ("arithmetic", "*") => []
      | ("arithmetic", "+") => []
      | ("arithmetic", "-") => []
      | ("arithmetic", "<=") => []
      | ("arithmetic", ">") => []
      | ("arithmetic", ">=") => []
      | ("arithmetic", "DIV") => []
      | ("arithmetic", "EXP") => []
      | ("arithmetic", "MAX") => []
      | ("arithmetic", "MIN") => []
      | ("arithmetic", "MOD") => []
      | ("integer", "Num") => []
      | ("integer", "int_div") => [ I.INT_DIV_EDIV ]
      | ("integer", "int_exp") => [ I.int_exp ]
      | ("integer", "int_max") => [ I.INT_MAX ]
      | ("integer", "int_min") => [ I.INT_MIN ]
      | ("integer", "int_mod") => [ I.INT_MOD_EMOD ]
      | ("integer", "int_of_num") => []
      | ("integer", "int_quot") => [ I.INT_QUOT_EDIV ]
      | ("integer", "int_rem") => [ I.INT_REM_EMOD ]
      | ("intreal", "INT_CEILING") => []
      | ("marker", "Abbrev") => [ markerTheory.Abbrev_def ]
      | ("min", "=") =>
          if Type.compare (Ty, num --> num --> bool) = EQUAL then
            []
          else
            []
      | ("num", "SUC") => []
      | ("prim_rec", "<") => []
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
          let
            val thm = Conv.CONV_RULE NUM_TO_INT_CONV thm
            val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl thm)
          in
            if Term.aconv lhs rhs then acc else HOLset.add (acc, thm)
          end
          handle Feedback.HOL_ERR _ => HOLset.add (acc, thm)
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
  fun translation_records ({records, ...} : translation) = records ()
  fun translation_dicts ({tydict, tmdict, ...} : translation) = (tydict, tmdict)
  val parser_dicts_for_translation = parser_dicts_for_translation_aux
  val infer_logic_from_features = infer_logic_from_features

  fun option_logic_policy logic
      ({features, inferred_logic, reason} : {
        features : logic_features, inferred_logic : string, reason : string}) =
    case logic of
      NONE => NONE
    | SOME selected_logic =>
        SOME {logic = selected_logic, reason = "caller override"}

  fun goal_to_SmtLib_translation_with_policy policy =
    Lib.apsnd (fn xs => xs @ ["(exit)\n"]) o (goal_to_SmtLib_aux policy)

  fun goal_to_SmtLib_translation logic =
    goal_to_SmtLib_translation_with_policy (option_logic_policy logic)

  fun goal_to_SmtLib logic goal =
    let
      val (translation, strings) = goal_to_SmtLib_translation logic goal
    in
      (translation_dicts translation, strings)
    end

  fun goal_to_SmtLib_with_get_proof_translation_with_policy policy =
    Lib.apsnd (fn xs => xs @ ["(get-proof)\n", "(exit)\n"]) o
      (goal_to_SmtLib_aux policy)

  fun goal_to_SmtLib_with_get_proof_translation logic =
    goal_to_SmtLib_with_get_proof_translation_with_policy
      (option_logic_policy logic)

  fun goal_to_SmtLib_with_get_proof logic goal =
    let
      val (translation, strings) =
        goal_to_SmtLib_with_get_proof_translation logic goal
    in
      (translation_dicts translation, strings)
    end

  val NUM_TO_INT_CONV = NUM_TO_INT_CONV
  val NUM_BINDERS_TO_INT_CONV = NUM_BINDERS_TO_INT_CONV

  fun type_mentions_num ty =
    Type.compare (ty, numSyntax.num) = EQUAL orelse
    (case Lib.total Type.dom_rng ty of
       SOME (dom, rng) => type_mentions_num dom orelse type_mentions_num rng
     | NONE => false)

  fun is_num_transfer_const tm =
    if not (Term.is_const tm) orelse not (type_mentions_num (Term.type_of tm))
    then false
    else
      case Lib.total Term.dest_thy_const tm of
        SOME {Thy = "arithmetic", Name, ...} =>
          List.exists (fn n => n = Name)
            ["*", "+", "-", "<=", ">", ">=", "DIV", "EXP", "MAX", "MIN",
             "MOD"]
      | SOME {Thy = "num", Name = "SUC", ...} => true
      | SOME {Thy = "integer", Name = "int_exp", ...} => true
      | SOME {Thy = "prim_rec", Name = "<", ...} => true
      | SOME {Thy = "integer", Name = "Num", ...} => true
      | SOME {Thy = "integer", Name = "int_of_num", ...} => true
      | SOME {Thy = "realax", Name = "NUM_FLOOR", ...} => true
      | SOME {Thy = "realax", Name = "NUM_CEILING", ...} => true
      | _ => false

  fun atom_needs_num_transfer atom =
    (Term.is_var atom andalso
     Type.compare (Term.type_of atom, numSyntax.num) = EQUAL) orelse
    is_num_transfer_const atom

  fun term_is_num tm =
    Type.compare (Term.type_of tm, numSyntax.num) = EQUAL

  (* True when a natural in `tm` meets the word theory, in either of the two
     ways the transfer cannot follow: as an argument of a word symbol, because
     `word_extract` and friends require indices that stay literal numerals
     (see `builtin_symbols`) whereas the transfer rewrites them into `Num`
     applications; or as a natural computed from a word, such as `w2n w`, for
     which there is no transferred counterpart.  Naturals and words that never
     meet -- a goal reasoning about both independently -- are unaffected, and
     their naturals still transfer. *)
  fun num_meets_word tm =
    (term_is_num tm andalso
     List.exists (fn sub => type_contains_word (Term.type_of sub))
       (subterms tm))
    orelse
    let
      val (rator, rands) = boolSyntax.strip_comb tm
    in
      type_contains_word (Term.type_of rator) andalso
      List.exists term_is_num rands
    end

  fun goal_entangles_num_and_word (asms, concl) =
    List.exists num_meets_word
      (List.concat (List.map subterms (concl :: asms)))

  fun goal_mentions_num (asms, concl) =
  let
    val atoms = Term.all_atomsl (concl :: asms) Term.empty_tmset
  in
    HOLset.foldl (fn (atom, seen) => seen orelse atom_needs_num_transfer atom)
      false atoms
  end

  (* Runs the proved num-to-int transfer on the whole goal.  Assumptions are
     first moved into the conclusion so free num variables anywhere in the
     sequent are made explicit and get a non-negativity guard. *)
  fun NUM_TO_INT_TAC g =
  let
    open Tactic Tactical
    val undisch_assums = MAP_EVERY UNDISCH_TAC (#1 g)
  in
    if goal_mentions_num g andalso not (goal_entangles_num_and_word g) then
      (undisch_assums THEN
       SPEC_NUM_FREE_VARS_TAC THEN
       CONV_TAC NUM_TO_INT_CONV THEN
       REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
       bossLib.REV_FULL_SIMP_TAC pureSimps.pure_ss num_transfer_rewrites) g
    else
      ALL_TAC g
  end

  (* Relativizes num-typed binders to guarded int-typed binders. *)
  val NUM_BINDERS_TO_INT_TAC =
  let
    open Tactic Tactical
  in
    RULE_ASSUM_TAC (Conv.CONV_RULE NUM_BINDERS_TO_INT_CONV) THEN
    CONV_TAC NUM_BINDERS_TO_INT_CONV
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

  (* ADD_THEOREMS_TAC contributes global definition theorems as assumptions.
     Simplify each one in isolation afterwards: this removes definitions that
     have become reflexive after the semantic num-to-int transfer, without
     treating the assumptions themselves as rewrite rules. *)
  fun CLEANUP_ASSUMPTIONS_TAC g =
  let
    open Tactic Tactical
    val assumptions = #1 g
    fun is_true tm =
      Term.aconv tm boolSyntax.T orelse
      (let val (_, body) = boolSyntax.dest_forall tm
       in is_true body end
       handle Feedback.HOL_ERR _ => false)
    fun cleanup thm =
    let
      val thm = simpLib.SIMP_RULE pureSimps.pure_ss
        (boolTheory.REFL_CLAUSE :: num_transfer_rewrites) thm
    in
      if is_true (Thm.concl thm) then
        ALL_TAC
      else
        ASSUME_TAC thm
    end
    val cleanup_one = POP_ASSUM cleanup
  in
    MAP_EVERY (fn _ => cleanup_one) assumptions g
  end

  (* Eliminates some HOL terms that are not supported by the SMT-LIB
     translation. It also adds some useful theorems to the list of assumptions
     so that SMT solvers can reason about some symbols defined in HOL4 theories. *)
  fun SIMP_TAC simp_let =
  let
    open Tactical simpLib
  in
    (* This must precede num transfer: the native real numeral form lets the
       closed positivity proof erase the whole pow term, including its nat
       exponent. *)
    Tactic.CONV_TAC (Conv.DEPTH_CONV REAL_POW_POS_LITERAL_CONV) THEN
    (* Close algebraic natural identities while their saturated subtraction
       is still in its native form, before lowering introduces nested ites. *)
    SIMP_TAC pureSimps.pure_ss
      [HolSmtTheory.num_sub_assoc, HolSmtTheory.num_floor_zero,
       HolSmtTheory.num_ceiling_zero, arithmeticTheory.MAX_0,
       arithmeticTheory.MIN_0, boolTheory.REFL_CLAUSE] THEN
    NUM_TO_INT_TAC THEN
    (if simp_let then Library.LET_SIMP_TAC else ALL_TAC) THEN
    Tactic.CONV_TAC (Conv.DEPTH_CONV REAL_POW_NUMERAL_CONV) THEN
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
      listTheory.MEM, realTheory.POW_1, realTheory.POW_2, REAL_POW_3,
      Thm.CONJUNCT1 realTheory.pow, Thm.CONJUNCT2 realTheory.pow,
      integerTheory.INT_MAX, integerTheory.INT_MIN,
      HolSmtTheory.real_div_smt_rdiv, HolSmtTheory.smt_rdiv_zero
    ] THEN
    SIMP_TAC realSimps.real_ss
      [HolSmtTheory.smt_rdiv_zero, HolSmtTheory.smt_rdiv_refl,
       HolSmtTheory.smt_rdiv_one, HolSmtTheory.smt_rdiv_neg_refl,
       HolSmtTheory.smt_rdiv_neg_one] THEN
    SIMP_TAC pureSimps.pure_ss [
      boolTheory.FUN_EQ_THM, boolTheory.REFL_CLAUSE
    ] THEN
    Library.WORD_SIMP_TAC THEN
    Library.SET_SIMP_TAC THEN
    Tactic.RULE_ASSUM_TAC
      (Conv.CONV_RULE (Conv.DEPTH_CONV INT_DIVIDES_LITERAL_MOD_CONV)) THEN
    Tactic.CONV_TAC (Conv.DEPTH_CONV INT_DIVIDES_LITERAL_MOD_CONV) THEN
    Tactic.BETA_TAC THEN
    NUM_TO_INT_TAC THEN
    ADD_THEOREMS_TAC THEN
    CLEANUP_ASSUMPTIONS_TAC THEN
    (* The theorem-discovery pass may expose a fresh num-valued occurrence.
       Run the semantic transfer last, then simplify its newly-added
       assumptions even when they no longer mention num themselves. *)
    NUM_TO_INT_TAC THEN
    CLEANUP_ASSUMPTIONS_TAC
  end

  (* Kept public for Unittest's outbound-scope audit. *)
  val builtin_encoding_for_test = builtin_encoding
end  (* local *)

end
