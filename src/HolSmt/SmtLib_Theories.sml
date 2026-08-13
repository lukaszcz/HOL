(* Copyright (c) 2010-2011 Tjark Weber. All rights reserved. *)

(* SMT-LIB 2 theories *)

structure SmtLib_Theories =
struct

local

  local open HolSmtTheory smtfloatTheory smtstringTheory in end

  val ERR = Feedback.mk_HOL_ERR "SmtLib_Theories"

in

  datatype symbol_source =
      Official
    | Extension of string

  type symbol_attributes = {
    overloaded: bool,
    indexed: bool,
    chainable: bool,
    pairwise: bool,
    left_associative: bool,
    right_associative: bool,
    soundness_audit: bool,
    parametric_sorts: string list
  }

  type 'a symbol_entry = {
    name: string,
    parse: string -> Term.term list -> 'a list -> 'a,
    source: symbol_source,
    attributes: symbol_attributes,
    declarations: string list
  }

  type symbol_metadata = {
    theory: string,
    kind: string,
    name: string,
    source: symbol_source,
    attributes: symbol_attributes,
    declarations: string list
  }

  val no_attributes = {
    overloaded = false,
    indexed = false,
    chainable = false,
    pairwise = false,
    left_associative = false,
    right_associative = false,
    soundness_audit = false,
    parametric_sorts = []
  }

  fun mk_attributes {
      overloaded, indexed, chainable, pairwise, left_associative,
      right_associative, soundness_audit, parametric_sorts} =
    {
      overloaded = overloaded,
      indexed = indexed,
      chainable = chainable,
      pairwise = pairwise,
      left_associative = left_associative,
      right_associative = right_associative,
      soundness_audit = soundness_audit,
      parametric_sorts = parametric_sorts
    }

  fun official_entry name attributes declarations parse = {
    name = name,
    parse = parse,
    source = Official,
    attributes = attributes,
    declarations = declarations
  }

  fun extension_entry solver name attributes declarations parse = {
    name = name,
    parse = parse,
    source = Extension solver,
    attributes = attributes,
    declarations = declarations
  }

  fun dictionary_of_entries entries =
    Library.dict_from_list (List.map
      (fn ({name, parse, ...}: 'a symbol_entry) => (name, parse)) entries)

  fun metadata_of_entries theory kind entries =
    List.map (fn ({name, source, attributes, declarations, ...}: 'a symbol_entry) =>
      {theory = theory, kind = kind, name = name, source = source,
       attributes = attributes, declarations = declarations}) entries

  fun symbol_source_name Official = "SMT-LIB 2.7"
    | symbol_source_name (Extension solver) = solver ^ " extension"

  fun is_official_metadata ({source = Official, ...}: symbol_metadata) = true
    | is_official_metadata _ = false

  fun is_extension_metadata ({source = Extension _, ...}: symbol_metadata) = true
    | is_extension_metadata _ = false

  val left_assoc_attributes = mk_attributes {
    overloaded = false,
    indexed = false,
    chainable = false,
    pairwise = false,
    left_associative = true,
    right_associative = false,
    soundness_audit = false,
    parametric_sorts = []
  }

  val right_assoc_attributes = mk_attributes {
    overloaded = false,
    indexed = false,
    chainable = false,
    pairwise = false,
    left_associative = false,
    right_associative = true,
    soundness_audit = false,
    parametric_sorts = []
  }

  val chainable_attributes = mk_attributes {
    overloaded = false,
    indexed = false,
    chainable = true,
    pairwise = false,
    left_associative = false,
    right_associative = false,
    soundness_audit = false,
    parametric_sorts = []
  }

  val pairwise_attributes = mk_attributes {
    overloaded = false,
    indexed = false,
    chainable = false,
    pairwise = true,
    left_associative = false,
    right_associative = false,
    soundness_audit = false,
    parametric_sorts = []
  }

  fun parametric_attributes params = mk_attributes {
    overloaded = false,
    indexed = false,
    chainable = false,
    pairwise = false,
    left_associative = false,
    right_associative = false,
    soundness_audit = false,
    parametric_sorts = params
  }

  fun indexed_attributes params = mk_attributes {
    overloaded = false,
    indexed = true,
    chainable = false,
    pairwise = false,
    left_associative = false,
    right_associative = false,
    soundness_audit = false,
    parametric_sorts = params
  }

  fun overloaded_attributes attrs = {
    overloaded = true,
    indexed = #indexed attrs,
    chainable = #chainable attrs,
    pairwise = #pairwise attrs,
    left_associative = #left_associative attrs,
    right_associative = #right_associative attrs,
    soundness_audit = #soundness_audit attrs,
    parametric_sorts = #parametric_sorts attrs
  }

  fun soundness_audit_attributes attrs = {
    overloaded = #overloaded attrs,
    indexed = #indexed attrs,
    chainable = #chainable attrs,
    pairwise = #pairwise attrs,
    left_associative = #left_associative attrs,
    right_associative = #right_associative attrs,
    soundness_audit = true,
    parametric_sorts = #parametric_sorts attrs
  }

  fun zero_args x xs =
    if List.null xs then
      x
    else
      raise ERR "zero_args" "no arguments expected"

  fun one_arg f xs =
    f (Lib.singleton_of_list xs handle Feedback.HOL_ERR _ =>
      raise ERR "one_arg" "one argument expected")

  fun two_args f xs =
    f (Lib.pair_of_list xs handle Feedback.HOL_ERR _ =>
      raise ERR "two_args" "two arguments expected")

  fun three_args f xs =
    f (Lib.triple_of_list xs handle Feedback.HOL_ERR _ =>
      raise ERR "three_args" "three arguments expected")

  fun list_args f xs =
    if List.null xs then
      raise ERR "list_args" "non-empty argument list expected"
    else
      f xs

  fun zero_zero f x = zero_args (zero_args (f x))
  fun zero_one f x = zero_args (one_arg (f x))
  fun zero_two f x = zero_args (two_args (f x))

  fun one_zero f x = zero_args o (one_arg (f x))
  fun one_one f x = one_arg o (one_arg (f x))

  fun list_list f x = list_args o (list_args (f x))

  fun K_zero_zero x = Lib.K (zero_args (zero_args x))
  fun K_zero_one f = Lib.K (zero_args (one_arg f))
  fun K_zero_two f = Lib.K (zero_args (two_args f))
  fun K_zero_three f = Lib.K (zero_args (three_args f))
  fun K_zero_list f = Lib.K (zero_args (list_args f))

  fun K_one_zero f = Lib.K (zero_args o one_arg f)
  fun K_one_one f = Lib.K (one_arg o one_arg f)

  fun K_two_one f = Lib.K (one_arg o two_args f)

  fun K_list_one f = Lib.K (one_arg o list_args f)

  fun chainable f =
  let
    fun aux t [] = raise Match  (* should never happen *)
      | aux t [_] = t
      | aux t (x::y::zs) = aux (boolSyntax.mk_conj (t, f (x, y))) (y::zs)
  in
    Lib.K (zero_args (list_args
      (fn x::y::zs => aux (f (x, y)) (y::zs)
        | _ => raise ERR "chainable" "at least two arguments expected")))
  end

  fun leftassoc f =
  let
    fun aux t [] = t
      | aux t (y::zs) = aux (f (t, y)) zs
  in
    Lib.K (zero_args (list_args
      (fn x::y::zs => aux x (y::zs)
        | _ => raise ERR "leftassoc" "at least two arguments expected")))
  end

  fun rightassoc f =
  let
    fun aux _ [] = raise Match  (* should never happen *)
      | aux cont [y] = cont y
      | aux cont (x::y::zs) = aux (fn t => cont (f (x, t))) (y::zs)
  in
    Lib.K (zero_args (list_args
      (fn x::y::zs => aux Lib.I (x::y::zs)
        | _ => raise ERR "rightassoc" "at least two arguments expected")))
  end

  (* A <numeral> is the digit 0 or a non-empty sequence of digits not
     starting with 0. *)
  fun is_numeral token =
  let
    val cs = String.explode token
  in
    cs = [#"0"] orelse
      (not (List.null cs) andalso List.all Char.isDigit cs andalso
        List.hd cs <> #"0")
  end

  (* A <decimal> is a token of the form <numeral>.0*<numeral>. *)
  fun real_of_decimal token =
  let
    val (left, right) = Lib.pair_of_list (String.fields (Lib.equal #".") token)
    val _ = is_numeral left orelse
      raise ERR "real_of_decimal" "not a decimal"
    val right = String.explode right
    fun is_zerostar_numeral (#"0" :: c :: cs) = is_zerostar_numeral (c :: cs)
      | is_zerostar_numeral cs                = is_numeral (String.implode cs)
    val _ = is_zerostar_numeral right orelse
      raise ERR "real_of_decimal" "not a decimal"
    (* drop trailing 0's *)
    fun drop_zeros (#"0" :: cs) = drop_zeros cs
      | drop_zeros cs           = cs
    val right = String.implode (List.rev (drop_zeros (List.rev right)))
    val numerator = Arbint.fromString (left ^ right)
    val ten = Arbint.fromInt 10
    val denominator = Lib.funpow (String.size right)
      (fn i => Arbint.* (ten, i)) Arbint.one
  in
    if denominator = Arbint.one then
      realSyntax.term_of_int numerator
    else
      realSyntax.mk_div (realSyntax.term_of_int numerator,
        realSyntax.term_of_int denominator)
  end
  handle Feedback.HOL_ERR _ =>
    raise ERR "real_of_decimal" "not a decimal"

  (* The legacy parser represents numeric indices as Int terms.  The checked
     sort elaborator may preserve decimal indices as Num terms; accept both.
     An index that is neither form is genuinely symbolic. *)
  fun natural_of_index n_tm =
    (Arbint.toNat (intSyntax.int_of_term n_tm)
     handle Feedback.HOL_ERR _ => numSyntax.dest_numeral n_tm)
    handle Feedback.HOL_ERR _ =>
      raise ERR "natural_of_index"
        ("numeric index expected, but '" ^ Hol_pp.term_to_string n_tm ^
         "' found")

  fun word_index_type n_tm =
    fcpLib.index_type (natural_of_index n_tm)

  fun bv_decimal_constant token n_tm =
    if String.isPrefix "bv" token then
      let
        val decimal = String.extract (token, 2, NONE)
        val value = Library.parse_arbnum decimal
        val n = natural_of_index n_tm
      in
        wordsSyntax.mk_word (value, n)
      end
    else
      raise ERR "bv_decimal_constant" "not a decimal bit-vector constant"

  fun mk_word_size_add n_tm t =
    fcpLib.index_type
      (Arbnum.+ (fcpLib.index_to_num (wordsSyntax.dim_of t),
        natural_of_index n_tm))

  fun mk_bbterm bits =
  let
    val width = List.length bits
    val _ =
      if width = 0 then
        raise ERR "mk_bbterm" "at least one bit expected"
      else
        ()
    val _ =
      List.all (fn bit => Term.type_of bit = Type.bool) bits orelse
      raise ERR "mk_bbterm" "Boolean bit arguments expected"
    fun dest_bit bit =
      let
        val (idx, word) = wordsSyntax.dest_word_bit bit
      in
        (Arbnum.toInt (numSyntax.dest_numeral idx), word)
      end
    fun dest_holsmt_xor tm =
      let
        val (f, r) = Term.dest_comb tm
        val (c, l) = Term.dest_comb f
        val {Thy, Name, ...} = Term.dest_thy_const c
      in
        if Thy = "HolSmt" andalso Name = "xor" then (l, r)
        else raise ERR "dest_holsmt_xor" "not xor"
      end
    fun dest_bool_xor tm =
      dest_holsmt_xor tm
      handle Feedback.HOL_ERR _ =>
        boolSyntax.dest_eq (boolSyntax.dest_neg tm)
    fun word_from_bits bs =
      case from_word_selectors bs of
        SOME word => SOME word
      | NONE =>
          (case from_bitwise_binop boolSyntax.dest_conj wordsSyntax.mk_word_and bs of
             SOME word => SOME word
           | NONE =>
               (case from_bitwise_binop boolSyntax.dest_disj wordsSyntax.mk_word_or bs of
                  SOME word => SOME word
                | NONE =>
                    (case from_bitwise_binop dest_bool_xor wordsSyntax.mk_word_xor bs of
                       SOME word => SOME word
                     | NONE =>
                         (case from_bitwise_binop boolSyntax.dest_eq wordsSyntax.mk_word_xnor bs of
                            SOME word => SOME word
                          | NONE => from_bitwise_not bs))))
    and from_word_selectors bs =
      case Lib.total (fn () => List.map dest_bit bs) () of
        NONE => NONE
      | SOME [] => NONE
      | SOME ((idx0, word) :: rest) =>
          let
            val word_width =
              Arbnum.toInt (fcpLib.index_to_num (wordsSyntax.dim_of word))
            fun check _ [] = true
              | check n ((idx, tm) :: xs) =
                  idx = n andalso Term.aconv tm word andalso check (n + 1) xs
          in
            if idx0 = 0 andalso word_width = width andalso check 1 rest then
              SOME word
            else
              NONE
          end
          handle _ => NONE
    and from_bitwise_binop dest mk bs =
      case Lib.total (fn () => List.map dest bs) () of
        SOME pairs =>
          (case (word_from_bits (List.map Lib.fst pairs),
                 word_from_bits (List.map Lib.snd pairs)) of
             (SOME l, SOME r) => SOME (mk (l, r))
           | _ => NONE)
      | NONE => NONE
    and from_bitwise_not bs =
      case Lib.total (fn () => List.map boolSyntax.dest_neg bs) () of
        SOME bs' =>
          (case word_from_bits bs' of
             SOME word => SOME (wordsSyntax.mk_word_1comp word)
           | NONE => NONE)
      | NONE => NONE
    val i = Term.mk_var ("i", numSyntax.num)
    fun numeral n = numSyntax.mk_numeral (Arbnum.fromInt n)
    fun select_bit [] = boolSyntax.F
      | select_bit ((n, bit) :: rest) =
          boolSyntax.mk_cond (boolSyntax.mk_eq (i, numeral n),
            bit, select_bit rest)
    val indexed_bits =
      ListPair.zip (List.tabulate (width, Lib.I), bits)
    val body = select_bit indexed_bits
  in
    case word_from_bits bits of
      SOME word => word
    | NONE =>
        fcpSyntax.mk_fcp (Term.mk_abs (i, body),
          fcpLib.index_type (Arbnum.fromInt width))
  end

  fun mk_bool_ne (t1, t2) =
    boolSyntax.mk_neg (boolSyntax.mk_eq (t1, t2))

  fun mk_bvnego t =
    boolSyntax.mk_eq (t, wordsSyntax.mk_word_L (wordsSyntax.dim_of t))

  fun mk_bvuaddo (t1, t2) =
    wordsSyntax.mk_word_lo (wordsSyntax.mk_word_add (t1, t2), t1)

  fun mk_bvusubo (t1, t2) =
    wordsSyntax.mk_word_lo (t1, t2)

  fun mk_bvsaddo (t1, t2) =
    let
      val msb1 = wordsSyntax.mk_word_msb t1
      val msb2 = wordsSyntax.mk_word_msb t2
      val sum_msb = wordsSyntax.mk_word_msb (wordsSyntax.mk_word_add (t1, t2))
    in
      boolSyntax.mk_conj (boolSyntax.mk_eq (msb1, msb2),
        mk_bool_ne (sum_msb, msb1))
    end

  fun mk_bvssubo (t1, t2) =
    let
      val msb1 = wordsSyntax.mk_word_msb t1
      val msb2 = wordsSyntax.mk_word_msb t2
      val diff_msb = wordsSyntax.mk_word_msb (wordsSyntax.mk_word_sub (t1, t2))
    in
      boolSyntax.mk_conj (mk_bool_ne (msb1, msb2),
        mk_bool_ne (diff_msb, msb1))
    end

  fun mk_bvumulo (t1, t2) =
    numSyntax.mk_geq (numSyntax.mk_mult
      (wordsSyntax.mk_w2n t1, wordsSyntax.mk_w2n t2),
      wordsSyntax.mk_dimword (wordsSyntax.dim_of t1))

  fun mk_bvsmulo (t1, t2) =
    let
      val product = intSyntax.mk_mult
        (integer_wordSyntax.mk_w2i t1, integer_wordSyntax.mk_w2i t2)
      val ty = wordsSyntax.dim_of t1
    in
      boolSyntax.mk_disj
        (intSyntax.mk_less (product, integer_wordSyntax.mk_int_min ty),
         intSyntax.mk_greater (product, integer_wordSyntax.mk_int_max ty))
    end

  fun mk_bvsdivo (t1, t2) =
    boolSyntax.mk_conj
      (boolSyntax.mk_eq (t1, wordsSyntax.mk_word_L (wordsSyntax.dim_of t1)),
       boolSyntax.mk_eq (t2, wordsSyntax.mk_word_T (wordsSyntax.dim_of t2)))

  fun mk_int_ediv (t1, t2) =
    Term.mk_comb (Term.mk_comb
      (Term.prim_mk_const {Thy="integer", Name="ediv"}, t1), t2)

  fun mk_int_emod (t1, t2) =
    Term.mk_comb (Term.mk_comb
      (Term.prim_mk_const {Thy="integer", Name="emod"}, t1), t2)

  fun sanitize_name name =
    String.translate
      (fn c => if Char.isAlphaNum c then String.str c else "_") name

  fun abstract_type name =
    Type.mk_vartype ("'smtlib_" ^ sanitize_name name)

  fun abstract_const name ret_ty args =
    Term.list_mk_comb
      (Term.mk_var ("smtlib_" ^ sanitize_name name,
         boolSyntax.list_mk_fun (List.map Term.type_of args, ret_ty)),
       args)

  fun abstract_const_arity name n ret_ty args =
    if List.length args = n then
      abstract_const name ret_ty args
    else
      raise ERR ("<" ^ name ^ ">")
        (Int.toString n ^ " argument(s) expected")

  fun abstract_bool name args = abstract_const name Type.bool args

  fun abstract_same name args =
    case args of
      [] => raise ERR ("<" ^ name ^ ">") "at least one argument expected"
    | x :: _ => abstract_const name (Term.type_of x) args

  fun abstract_indexed_const name indices ret_ty args =
    abstract_const
      (name ^ "_" ^
       String.concatWith "_" (List.map (sanitize_name o Hol_pp.term_to_string)
         indices))
      ret_ty args

  fun abstract_sort_entry sort_name =
    official_entry sort_name no_attributes ["(" ^ sort_name ^ " 0)"]
      (K_zero_zero (abstract_type sort_name))

  fun smtfp_type (eb, sb) =
    let
      val two = Arbnum.fromInt 2
      val _ =
        if Arbnum.compare (eb, two) = LESS then
          raise ERR "smtfp_type"
            "exponent width eb must be at least 2"
        else
          ()
      val _ =
        if Arbnum.compare (sb, two) = LESS then
          raise ERR "smtfp_type"
            "significand width sb must be at least 2; sb - 1 must be nonzero"
        else
          ()
    in
      Type.mk_thy_type {
        Thy = "smtfloat",
        Tyop = "smtfp",
        Args = [fcpLib.index_type (Arbnum.- (sb, Arbnum.one)),
          fcpLib.index_type eb]
      }
    end

  fun fp_type_from_indices [eb, sb] =
        smtfp_type (natural_of_index eb, natural_of_index sb)
    | fp_type_from_indices _ =
        raise ERR "fp_type_from_indices"
          "FloatingPoint forms expect exponent and significand indices"

  val rounding_mode_ty =
    Type.mk_thy_type {Thy = "smtfloat", Tyop = "smt_rounding", Args = []}

  fun smtfloat_const name =
    Term.prim_mk_const {Thy = "smtfloat", Name = name}

  fun apply_native_const const args =
    let
      fun apply_one (arg, rator) =
        let
          val (domain, _) = Type.dom_rng (Term.type_of rator)
          val subst = Type.match_type domain (Term.type_of arg)
        in
          Term.mk_comb (Term.inst subst rator, arg)
        end
    in
      List.foldl apply_one const args
    end

  fun smtfloat_app name args =
    apply_native_const (smtfloat_const name) args

  fun smtfloat_const_result name result_ty =
    let
      val const = smtfloat_const name
      val (_, range) = boolSyntax.strip_fun (Term.type_of const)
      val subst = Type.match_type range result_ty
    in
      Term.inst subst const
    end

  fun smtfloat_app_result name result_ty args =
    apply_native_const (smtfloat_const_result name result_ty) args

  val reglan_ty =
    Type.mk_thy_type {Thy = "smtstring", Tyop = "reglan", Args = []}

  fun smtstring_const name =
    Term.prim_mk_const {Thy = "smtstring", Name = name}

  fun smtstring_app name args =
    Term.list_mk_comb (smtstring_const name, args)

  fun smtstring_index index =
    numSyntax.mk_numeral (natural_of_index index)

  fun smtstring_char_index index =
    numSyntax.mk_numeral
      (SmtLib_String_Literal.check_code_point "character index"
        (natural_of_index index))
    handle SmtLib_String_Literal.InvalidCodePoint detail =>
      raise ERR "<UnicodeStrings.char>" detail

  fun sequence_ty elem_ty =
    Type.mk_thy_type {Thy = "list", Tyop = "list", Args = [elem_ty]}

  fun set_ty elem_ty = Type.--> (elem_ty, Type.bool)
  fun bag_ty elem_ty = Type.--> (elem_ty, numSyntax.num)

  fun function_ty tys =
    case tys of
      [] => raise ERR "<HO-Core.->>"
        "function sort '->' expects at least one domain sort and one range sort"
    | [_] => raise ERR "<HO-Core.->>"
        "function sort '->' expects at least one domain sort and one range sort"
    | _ =>
        let val (domains, range) = Lib.front_last tys
        in boolSyntax.list_mk_fun (domains, range) end

  fun apply_operator operator token indices terms =
    let
      fun apply_one (arg, rator) =
        let
          val (domain, _) = Type.dom_rng (Term.type_of rator)
          val arg =
            if Type.compare (domain, realSyntax.real_ty) = EQUAL andalso
               Type.compare (Term.type_of arg, intSyntax.int_ty) = EQUAL then
              intrealSyntax.mk_real_of_int arg
            else arg
          val subst = Type.match_type domain (Term.type_of arg)
          val rator = Term.inst subst rator
        in
          Term.mk_comb (rator, arg)
        end
    in
      if token <> operator then
        raise ERR ("<HO-Core." ^ operator ^ ">")
          "operator name mismatch"
      else if not (List.null indices) then
        raise ERR ("<HO-Core." ^ operator ^ ">")
          "no indices expected"
      else
        case terms of
          rator :: arg :: args => List.foldl apply_one rator (arg :: args)
        | _ => raise ERR ("<HO-Core." ^ operator ^ ">")
            "a map term and at least one argument expected"
    end

  fun unary_decl name dom rng =
    "(" ^ name ^ " " ^ dom ^ " " ^ rng ^ ")"

  (* FloatingPoint *)

  structure FloatingPoint =
  struct

    val tyentries = [
      official_entry "RoundingMode" no_attributes ["(RoundingMode 0)"]
        (K_zero_zero rounding_mode_ty),
      official_entry "FloatingPoint" (indexed_attributes ["eb", "sb"])
        ["((_ FloatingPoint eb sb) 0)"]
        (fn _ => fn indices => fn args =>
          if List.null args then fp_type_from_indices indices
          else raise ERR "<FloatingPoint>" "no arguments expected"),
      official_entry "Float16" no_attributes ["(Float16 0)"]
        (K_zero_zero (smtfp_type
          (Arbnum.fromInt 5, Arbnum.fromInt 11))),
      official_entry "Float32" no_attributes ["(Float32 0)"]
        (K_zero_zero (smtfp_type
          (Arbnum.fromInt 8, Arbnum.fromInt 24))),
      official_entry "Float64" no_attributes ["(Float64 0)"]
        (K_zero_zero (smtfp_type
          (Arbnum.fromInt 11, Arbnum.fromInt 53))),
      official_entry "Float128" no_attributes ["(Float128 0)"]
        (K_zero_zero (smtfp_type
          (Arbnum.fromInt 15, Arbnum.fromInt 113)))
    ]

    val rounding_modes = [
      "roundNearestTiesToEven", "RNE",
      "roundNearestTiesToAway", "RNA",
      "roundTowardPositive", "RTP",
      "roundTowardNegative", "RTN",
      "roundTowardZero", "RTZ"
    ]

    fun rounding_const name =
      case name of
        "roundNearestTiesToEven" => smtfloat_const "RNE"
      | "RNE" => smtfloat_const "RNE"
      | "roundNearestTiesToAway" => smtfloat_const "RNA"
      | "RNA" => smtfloat_const "RNA"
      | "roundTowardPositive" => smtfloat_const "RTP"
      | "RTP" => smtfloat_const "RTP"
      | "roundTowardNegative" => smtfloat_const "RTN"
      | "RTN" => smtfloat_const "RTN"
      | "roundTowardZero" => smtfloat_const "RTZ"
      | "RTZ" => smtfloat_const "RTZ"
      | _ => raise ERR "rounding_const" "unknown rounding mode"

    fun rounding_entry name =
      official_entry name no_attributes ["(" ^ name ^ " RoundingMode)"]
        (K_zero_zero (rounding_const name))

    fun special_const name =
      case name of
        "+zero" => "smtfp_pzero"
      | "-zero" => "smtfp_nzero"
      | "+oo" => "smtfp_pinf"
      | "-oo" => "smtfp_ninf"
      | "NaN" => "smtfp_nan"
      | _ => raise ERR "special_const" "unknown floating-point special"

    fun indexed_fp_constant name =
      official_entry name (indexed_attributes ["eb", "sb"])
        ["((_ " ^ name ^ " eb sb) (_ FloatingPoint eb sb))"]
        (fn _ => fn indices => fn args =>
          if List.null args then
            smtfloat_const_result (special_const name)
              (fp_type_from_indices indices)
          else
            raise ERR ("<" ^ name ^ ">") "no arguments expected")

    fun fp_unary smt_name hol_name =
      official_entry smt_name no_attributes
        [unary_decl smt_name "(_ FloatingPoint eb sb)"
          "(_ FloatingPoint eb sb)"]
        (K_zero_one (fn x => smtfloat_app hol_name [x]))

    fun fp_binary smt_name hol_name =
      official_entry smt_name no_attributes
        ["(" ^ smt_name ^
         " (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) " ^
         "(_ FloatingPoint eb sb))"]
        (K_zero_two (fn (x, y) => smtfloat_app hol_name [x, y]))

    fun fp_rounding_binary smt_name hol_name =
      official_entry smt_name no_attributes
        ["(" ^ smt_name ^ " RoundingMode (_ FloatingPoint eb sb) " ^
         "(_ FloatingPoint eb sb))"]
        (K_zero_two (fn (rm, x) => smtfloat_app hol_name [rm, x]))

    fun fp_pred smt_name hol_name =
      official_entry smt_name no_attributes
        [unary_decl smt_name "(_ FloatingPoint eb sb)" "Bool"]
        (K_zero_one (fn x => smtfloat_app hol_name [x]))

    fun is_smtfp_type ty =
      let val {Thy, Tyop, ...} = Type.dest_thy_type ty
      in Thy = "smtfloat" andalso Tyop = "smtfp" end
      handle Feedback.HOL_ERR _ => false

    fun ieee_bv_to_fp fp_ty x =
      let
        val _ = wordsSyntax.dest_word_type (Term.type_of x)
        val const = smtfloat_const_result "smtfp_from_ieee_bv" fp_ty
        val (domains, _) = boolSyntax.strip_fun (Term.type_of const)
        val domain =
          Lib.singleton_of_list domains
          handle Feedback.HOL_ERR _ =>
            raise ERR "ieee_bv_to_fp" "unexpected native constant type"
        val input_width =
          fcpLib.index_to_num (wordsSyntax.dim_of x)
        val domain_dim = wordsSyntax.dest_word_type domain
        val expected_width = fcpLib.index_to_num domain_dim
        val _ =
          if input_width = expected_width then ()
          else
            raise ERR "<to_fp>"
              ("IEEE bit-vector width " ^ Arbnum.toString input_width ^
               " does not match target floating-point width " ^
               Arbnum.toString expected_width)
        val x =
          if Type.compare (Term.type_of x, domain) = EQUAL then x
          else wordsSyntax.mk_w2w (x, domain_dim)
      in
        apply_native_const const [x]
      end

    fun to_fp indices args =
      let val fp_ty = fp_type_from_indices indices in
        case args of
          [x] => ieee_bv_to_fp fp_ty x
        | [rm, x] =>
            if is_smtfp_type (Term.type_of x) then
              smtfloat_app_result "smtfp_to_fp" fp_ty [rm, x]
            else if Type.compare
                (Term.type_of x, realSyntax.real_ty) = EQUAL then
              smtfloat_app_result "smtfp_from_real" fp_ty [rm, x]
            else if Type.compare
                (Term.type_of x, intSyntax.int_ty) = EQUAL then
              smtfloat_app_result "smtfp_from_real" fp_ty
                [rm, intrealSyntax.mk_real_of_int x]
            else if wordsSyntax.is_word_type (Term.type_of x) then
              smtfloat_app_result "smtfp_from_sbv" fp_ty [rm, x]
            else
              raise ERR "<to_fp>"
                "expected an IEEE bit-vector, FP, Real, or signed BV operand"
        | _ => raise ERR "<to_fp>" "one or two arguments expected"
      end

    fun to_fp_unsigned indices args =
      let val fp_ty = fp_type_from_indices indices in
        case args of
          [rm, x] =>
            if wordsSyntax.is_word_type (Term.type_of x) then
              smtfloat_app_result "smtfp_from_ubv" fp_ty [rm, x]
            else
              raise ERR "<to_fp_unsigned>" "bit-vector operand expected"
        | _ => raise ERR "<to_fp_unsigned>" "two arguments expected"
      end

    fun fp_to_bv smt_name hol_name indices args =
      case (indices, args) of
        ([width], [rm, x]) =>
          smtfloat_app_result hol_name
            (wordsSyntax.mk_word_type (word_index_type width)) [rm, x]
      | ([_], _) =>
          raise ERR ("<" ^ smt_name ^ ">") "two arguments expected"
      | _ => raise ERR ("<" ^ smt_name ^ ">") "one index expected"

    val tmentries =
      List.map rounding_entry rounding_modes @
      List.map indexed_fp_constant ["+zero", "-zero", "+oo", "-oo", "NaN"] @
      [
        official_entry "fp" no_attributes
          ["(fp (_ BitVec 1) (_ BitVec eb) (_ BitVec (- sb 1)) " ^
           "(_ FloatingPoint eb sb))"]
          (K_zero_three (fn (sign, exponent, significand) =>
            let
              val eb = fcpLib.index_to_num (wordsSyntax.dim_of exponent)
              val sb = Arbnum.plus1
                (fcpLib.index_to_num (wordsSyntax.dim_of significand))
              val fp_ty = smtfp_type (eb, sb)
            in
              smtfloat_app_result "smtfp_bits" fp_ty
                [sign, exponent, significand]
            end)),
        official_entry "fp.add" no_attributes
          ["(fp.add RoundingMode (_ FloatingPoint eb sb) " ^
           "(_ FloatingPoint eb sb) (_ FloatingPoint eb sb))"]
          (K_zero_three (fn (rm, x, y) =>
            smtfloat_app "smtfp_add" [rm, x, y])),
        official_entry "fp.sub" no_attributes
          ["(fp.sub RoundingMode (_ FloatingPoint eb sb) " ^
           "(_ FloatingPoint eb sb) (_ FloatingPoint eb sb))"]
          (K_zero_three (fn (rm, x, y) =>
            smtfloat_app "smtfp_sub" [rm, x, y])),
        official_entry "fp.mul" no_attributes
          ["(fp.mul RoundingMode (_ FloatingPoint eb sb) " ^
           "(_ FloatingPoint eb sb) (_ FloatingPoint eb sb))"]
          (K_zero_three (fn (rm, x, y) =>
            smtfloat_app "smtfp_mul" [rm, x, y])),
        official_entry "fp.div" no_attributes
          ["(fp.div RoundingMode (_ FloatingPoint eb sb) " ^
           "(_ FloatingPoint eb sb) (_ FloatingPoint eb sb))"]
          (K_zero_three (fn (rm, x, y) =>
            smtfloat_app "smtfp_div" [rm, x, y])),
        official_entry "fp.fma" no_attributes
          ["(fp.fma RoundingMode (_ FloatingPoint eb sb) " ^
           "(_ FloatingPoint eb sb) (_ FloatingPoint eb sb) " ^
           "(_ FloatingPoint eb sb))"]
          (Lib.K (zero_args (fn args =>
            case args of
              [rm, x, y, z] => smtfloat_app "smtfp_fma" [rm, x, y, z]
            | _ => raise ERR "<fp.fma>" "four arguments expected"))),
        fp_rounding_binary "fp.sqrt" "smtfp_sqrt",
        fp_rounding_binary "fp.roundToIntegral"
          "smtfp_round_to_integral",
        fp_binary "fp.rem" "smtfp_rem",
        fp_binary "fp.min" "smtfp_min",
        fp_binary "fp.max" "smtfp_max",
        fp_unary "fp.abs" "smtfp_abs",
        fp_unary "fp.neg" "smtfp_neg",
        official_entry "fp.leq" chainable_attributes
          ["(fp.leq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) " ^
           "Bool :chainable)"]
          (chainable (fn (x, y) => smtfloat_app "smtfp_le" [x, y])),
        official_entry "fp.lt" chainable_attributes
          ["(fp.lt (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) " ^
           "Bool :chainable)"]
          (chainable (fn (x, y) => smtfloat_app "smtfp_lt" [x, y])),
        official_entry "fp.geq" chainable_attributes
          ["(fp.geq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) " ^
           "Bool :chainable)"]
          (chainable (fn (x, y) => smtfloat_app "smtfp_ge" [x, y])),
        official_entry "fp.gt" chainable_attributes
          ["(fp.gt (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) " ^
           "Bool :chainable)"]
          (chainable (fn (x, y) => smtfloat_app "smtfp_gt" [x, y])),
        official_entry "fp.eq" no_attributes
          ["(fp.eq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool)"]
          (K_zero_two (fn (x, y) => smtfloat_app "smtfp_eq" [x, y])),
        fp_pred "fp.isNormal" "smtfp_is_normal",
        fp_pred "fp.isSubnormal" "smtfp_is_subnormal",
        fp_pred "fp.isZero" "smtfp_is_zero",
        fp_pred "fp.isInfinite" "smtfp_is_infinite",
        fp_pred "fp.isNaN" "smtfp_is_nan",
        fp_pred "fp.isNegative" "smtfp_is_negative",
        fp_pred "fp.isPositive" "smtfp_is_positive",
        official_entry "to_fp" (indexed_attributes ["eb", "sb"])
          ["((_ to_fp eb sb) ... (_ FloatingPoint eb sb))"]
          (fn _ => fn indices => fn args => to_fp indices args),
        official_entry "to_fp_unsigned" (indexed_attributes ["eb", "sb"])
          ["((_ to_fp_unsigned eb sb) ... (_ FloatingPoint eb sb))"]
          (fn _ => fn indices => fn args => to_fp_unsigned indices args),
        official_entry "fp.to_ubv" (indexed_attributes ["m"])
          ["((_ fp.to_ubv m) RoundingMode (_ FloatingPoint eb sb) " ^
           "(_ BitVec m))"]
          (fn _ => fn indices => fn args =>
            fp_to_bv "fp.to_ubv" "smtfp_to_ubv" indices args),
        official_entry "fp.to_sbv" (indexed_attributes ["m"])
          ["((_ fp.to_sbv m) RoundingMode (_ FloatingPoint eb sb) " ^
           "(_ BitVec m))"]
          (fn _ => fn indices => fn args =>
            fp_to_bv "fp.to_sbv" "smtfp_to_sbv" indices args),
        official_entry "fp.to_real" no_attributes
          ["(fp.to_real (_ FloatingPoint eb sb) Real)"]
          (K_zero_one (fn x => smtfloat_app "smtfp_to_real" [x]))
      ]

    val tydict = dictionary_of_entries tyentries
    val tmdict = dictionary_of_entries tmentries
    val metadata =
      metadata_of_entries "FloatingPoint" "sort" tyentries @
      metadata_of_entries "FloatingPoint" "term" tmentries

  end

  (* UnicodeStrings and regular expressions *)

  structure UnicodeStrings =
  struct

    val string_ty =
      Type.mk_thy_type {Thy = "smtstring", Tyop = "smtstr", Args = []}

    val tyentries = [
      official_entry "String" no_attributes ["(String 0)"]
        (K_zero_zero string_ty),
      official_entry "RegLan" (parametric_attributes ["String"])
        ["(RegLan String)"]
        (K_zero_one (fn _ => reglan_ty))
    ]

    fun str_predicate smt_name hol_name =
      official_entry smt_name no_attributes
        ["(" ^ smt_name ^ " String String Bool)"]
        (K_zero_two (fn (x, y) => smtstring_app hol_name [x, y]))

    fun str_int_binary smt_name hol_name =
      official_entry smt_name no_attributes
        ["(" ^ smt_name ^ " String Int String)"]
        (K_zero_two (fn (x, i) => smtstring_app hol_name [x, i]))

    fun re_binary smt_name hol_name =
      official_entry smt_name no_attributes
        ["(" ^ smt_name ^
         " (RegLan String) (RegLan String) (RegLan String))"]
        (K_zero_two (fn (x, y) => smtstring_app hol_name [x, y]))

    val tmentries = [
      official_entry "str.++" left_assoc_attributes
        ["(str.++ String String String :left-assoc)"]
        (leftassoc
          (fn (x, y) => smtstring_app "smtstr_concat" [x, y])),
      official_entry "str.len" no_attributes ["(str.len String Int)"]
        (K_zero_one
          (fn s => smtstring_app "smtstr_len" [s])),
      official_entry "str.<" chainable_attributes
        ["(str.< String String Bool :chainable)"]
        (chainable (fn (x, y) => smtstring_app "smtstr_lt" [x, y])),
      official_entry "str.<=" chainable_attributes
        ["(str.<= String String Bool :chainable)"]
        (chainable (fn (x, y) => smtstring_app "smtstr_le" [x, y])),
      str_int_binary "str.at" "smtstr_at",
      official_entry "str.substr" no_attributes
        ["(str.substr String Int Int String)"]
        (K_zero_three (fn (s, i, n) =>
          smtstring_app "smtstr_substr" [s, i, n])),
      str_predicate "str.prefixof" "smtstr_prefixof",
      str_predicate "str.suffixof" "smtstr_suffixof",
      str_predicate "str.contains" "smtstr_contains",
      official_entry "str.indexof" no_attributes
        ["(str.indexof String String Int Int)"]
        (K_zero_three (fn (s, sub, offset) =>
          smtstring_app "smtstr_indexof" [s, sub, offset])),
      official_entry "str.replace" no_attributes
        ["(str.replace String String String String)"]
        (K_zero_three (fn (s, src, dst) =>
          smtstring_app "smtstr_replace" [s, src, dst])),
      official_entry "str.replace_all" no_attributes
        ["(str.replace_all String String String String)"]
        (K_zero_three (fn (s, src, dst) =>
          smtstring_app "smtstr_replace_all" [s, src, dst])),
      official_entry "str.is_digit" no_attributes ["(str.is_digit String Bool)"]
        (K_zero_one (fn s => smtstring_app "smtstr_is_digit" [s])),
      official_entry "str.to_code" no_attributes ["(str.to_code String Int)"]
        (K_zero_one (fn s => smtstring_app "smtstr_to_code" [s])),
      official_entry "str.from_code" no_attributes
        ["(str.from_code Int String)"]
        (K_zero_one (fn i => smtstring_app "smtstr_from_code" [i])),
      official_entry "str.to_int" no_attributes ["(str.to_int String Int)"]
        (K_zero_one (fn s => smtstring_app "smtstr_to_int" [s])),
      official_entry "str.from_int" no_attributes ["(str.from_int Int String)"]
        (K_zero_one (fn i => smtstring_app "smtstr_from_int" [i])),
      official_entry "str.to_re" no_attributes
        ["(str.to_re String (RegLan String))"]
        (K_zero_one (fn s => smtstring_app "reglan_to_re" [s])),
      official_entry "str.in_re" no_attributes
        ["(str.in_re String (RegLan String) Bool)"]
        (K_zero_two (fn (s, re) => smtstring_app "smt_in_re" [s, re])),
      official_entry "str.replace_re" no_attributes
        ["(str.replace_re String (RegLan String) String String)"]
        (K_zero_three (fn (s, re, dst) =>
          smtstring_app "smtstr_replace_re" [s, re, dst])),
      official_entry "str.replace_re_all" no_attributes
        ["(str.replace_re_all String (RegLan String) String String)"]
        (K_zero_three (fn (s, re, dst) =>
          smtstring_app "smtstr_replace_re_all" [s, re, dst])),
      official_entry "char" (indexed_attributes ["H"])
        ["((_ char H) String)"]
        (K_one_zero
          (fn h => smtstring_app "smtstr_char" [smtstring_char_index h])),
      official_entry "re.none" no_attributes ["(re.none (RegLan String))"]
        (K_zero_zero (smtstring_const "reglan_none")),
      official_entry "re.all" no_attributes ["(re.all (RegLan String))"]
        (K_zero_zero (smtstring_const "reglan_all")),
      official_entry "re.allchar" no_attributes ["(re.allchar (RegLan String))"]
        (K_zero_zero (smtstring_const "reglan_allchar")),
      re_binary "re.++" "reglan_concat",
      official_entry "re.union" left_assoc_attributes
        ["(re.union (RegLan String) (RegLan String) " ^
         "(RegLan String) :left-assoc)"]
        (leftassoc (fn (x, y) => smtstring_app "reglan_union" [x, y])),
      official_entry "re.inter" left_assoc_attributes
        ["(re.inter (RegLan String) (RegLan String) " ^
         "(RegLan String) :left-assoc)"]
        (leftassoc (fn (x, y) => smtstring_app "reglan_inter" [x, y])),
      re_binary "re.diff" "reglan_diff",
      official_entry "re.comp" no_attributes
        ["(re.comp (RegLan String) (RegLan String))"]
        (K_zero_one (fn re => smtstring_app "reglan_comp" [re])),
      official_entry "re.*" no_attributes
        ["(re.* (RegLan String) (RegLan String))"]
        (K_zero_one (fn re => smtstring_app "reglan_star" [re])),
      official_entry "re.+" no_attributes
        ["(re.+ (RegLan String) (RegLan String))"]
        (K_zero_one (fn re => smtstring_app "reglan_plus" [re])),
      official_entry "re.opt" no_attributes
        ["(re.opt (RegLan String) (RegLan String))"]
        (K_zero_one (fn re => smtstring_app "reglan_opt" [re])),
      official_entry "re.range" no_attributes
        ["(re.range String String (RegLan String))"]
        (K_zero_two (fn (lo, hi) =>
          smtstring_app "reglan_range" [lo, hi])),
      official_entry "re.^" (indexed_attributes ["n"])
        ["((_ re.^ n) (RegLan String) (RegLan String))"]
        (K_one_one (fn n => fn re =>
          smtstring_app "reglan_power" [re, smtstring_index n])),
      official_entry "re.loop" (indexed_attributes ["lo", "hi"])
        ["((_ re.loop lo hi) (RegLan String) (RegLan String))"]
        (fn _ => fn indices => fn args =>
          case (indices, args) of
            ([lo, hi], [re]) =>
              smtstring_app "reglan_loop"
                [re, smtstring_index lo, smtstring_index hi]
          | _ => raise ERR "<re.loop>"
              "two indices and one argument expected")
    ]

    val tydict = dictionary_of_entries tyentries
    val tmdict = dictionary_of_entries tmentries
    val metadata =
      metadata_of_entries "UnicodeStrings" "sort" tyentries @
      metadata_of_entries "UnicodeStrings" "term" tmentries

  end

  (* The shared first-order sequence surface is solver-neutral.  Z3-only
     HO operations and cvc5-only operations live in their dialect packets
     below, so solver-targeted parsing rejects the other dialect. *)
  structure Seq_Extensions =
  struct

    fun shared_term name attrs decl parse =
      extension_entry "shared" name attrs decl parse

    fun holsmt_const name =
      Term.prim_mk_const {Thy = "HolSmt", Name = name}

    fun holsmt_app name args =
      apply_native_const (holsmt_const name) args

    fun rich_list_app name args =
      apply_native_const
        (Term.prim_mk_const {Thy = "rich_list", Name = name}) args

    fun mk_seq_extract (s, i, n) =
      let
        val invalid = boolSyntax.list_mk_disj [
          intSyntax.mk_less (i, intSyntax.zero_tm),
          intSyntax.mk_leq (n, intSyntax.zero_tm),
          numSyntax.mk_leq (listSyntax.mk_length s, intSyntax.mk_Num i)]
      in
        boolSyntax.mk_cond (invalid, listSyntax.mk_nil (listSyntax.eltype s),
          listSyntax.mk_take (intSyntax.mk_Num n,
            listSyntax.mk_drop (intSyntax.mk_Num i, s)))
      end

    fun mk_seq_at (s, i) =
      let
        val invalid = boolSyntax.mk_disj
          (intSyntax.mk_less (i, intSyntax.zero_tm),
           numSyntax.mk_leq (listSyntax.mk_length s, intSyntax.mk_Num i))
      in
        boolSyntax.mk_cond (invalid, listSyntax.mk_nil (listSyntax.eltype s),
          listSyntax.mk_cons (listSyntax.mk_el (intSyntax.mk_Num i, s),
            listSyntax.mk_nil (listSyntax.eltype s)))
      end

    fun mk_seq_len s =
      Term.mk_comb (intSyntax.int_injection, listSyntax.mk_length s)

    (* Strings are sequences of Unicode code points.  seq.nth is unspecified
       outside its domain, so negative indices must not be totalized to zero.
       Z3's string-internal selector has exactly the required in-range
       equation and an unspecified out-of-range result. *)
    fun mk_string_nth (s, i) =
      boolSyntax.mk_cond
        (intSyntax.mk_less (i, intSyntax.zero_tm),
         boolSyntax.mk_arb numSyntax.num,
         apply_native_const
           (Term.prim_mk_const {Thy = "smtstringz3", Name = "seq_nth_i"})
           [s, intSyntax.mk_Num i])

    fun mk_seq_unit x =
      listSyntax.mk_cons (x, listSyntax.mk_nil (Term.type_of x))

    fun is_string tm =
      Type.compare (Term.type_of tm, UnicodeStrings.string_ty) = EQUAL

    fun string_or_seq string_name seq_fun args =
      if is_string (List.hd args) then smtstring_app string_name args
      else seq_fun args

    fun string_or_seq_one string_name seq_fun sequence =
      if is_string sequence then smtstring_app string_name [sequence]
      else seq_fun sequence

    fun string_or_seq_two string_name seq_fun (left, right) =
      string_or_seq string_name (fn [x, y] => seq_fun (x, y)
                                  | _ => raise Fail "wrong arity")
        [left, right]

    fun string_or_seq_three string_name seq_fun (first, second, third) =
      string_or_seq string_name (fn [x, y, z] => seq_fun (x, y, z)
                                  | _ => raise Fail "wrong arity")
        [first, second, third]

    val tyentries = [
      extension_entry "shared" "Seq" (parametric_attributes ["Element"])
        ["(Seq Element)"] (K_zero_one sequence_ty)
    ]

    val tmentries = [
      shared_term "seq.++" left_assoc_attributes
        ["(seq.++ (Seq A) (Seq A) (Seq A) :left-assoc)"]
        (leftassoc
          (string_or_seq_two "smtstr_concat" listSyntax.mk_append)),
      shared_term "seq.len" no_attributes ["(seq.len (Seq A) Int)"]
        (K_zero_one
          (string_or_seq_one "smtstr_len" mk_seq_len)),
      shared_term "seq.unit" no_attributes ["(seq.unit A (Seq A))"]
        (K_zero_one mk_seq_unit),
      shared_term "seq.empty" no_attributes ["(seq.empty (Seq A))"]
        (K_zero_zero (listSyntax.mk_nil Type.bool)),
      shared_term "seq.extract" no_attributes
        ["(seq.extract (Seq A) Int Int (Seq A))"]
        (K_zero_three
          (fn (s, i, n) =>
            string_or_seq "smtstr_substr"
              (fn [s, i, n] => mk_seq_extract (s, i, n)
                | _ => raise Fail "wrong arity") [s, i, n])),
      shared_term "seq.at" no_attributes ["(seq.at (Seq A) Int (Seq A))"]
        (K_zero_two
          (fn (s, i) =>
            string_or_seq "smtstr_at"
              (fn [s, i] => mk_seq_at (s, i)
                | _ => raise Fail "wrong arity") [s, i])),
      shared_term "seq.nth" no_attributes ["(seq.nth (Seq A) Int A)"]
        (K_zero_two
          (fn (s, i) =>
            if is_string s then
              raise ERR "seq.nth" "String is supported only by Z3"
            else holsmt_app "smt_seq_nth" [s, i])),
      shared_term "seq.contains" no_attributes
        ["(seq.contains (Seq A) (Seq A) Bool)"]
        (K_zero_two
          (string_or_seq_two "smtstr_contains"
            (fn (s, t) => rich_list_app "IS_SUBLIST" [s, t]))),
      shared_term "seq.indexof" no_attributes
        ["(seq.indexof (Seq A) (Seq A) Int Int)"]
        (K_zero_three (fn (s, t, i) =>
          string_or_seq "smtstr_indexof"
            (fn [s, t, i] => holsmt_app "smt_seq_indexof" [s, t, i]
              | _ => raise Fail "wrong arity") [s, t, i])),
      shared_term "seq.replace" no_attributes
        ["(seq.replace (Seq A) (Seq A) (Seq A) (Seq A))"]
        (K_zero_three (fn (s, t, u) =>
          string_or_seq "smtstr_replace"
            (fn [s, t, u] => holsmt_app "smt_seq_replace" [s, t, u]
              | _ => raise Fail "wrong arity") [s, t, u])),
      shared_term "seq.prefixof" no_attributes
        ["(seq.prefixof (Seq A) (Seq A) Bool)"]
        (K_zero_two
          (string_or_seq_two "smtstr_prefixof" listSyntax.mk_isprefix)),
      shared_term "seq.suffixof" no_attributes
        ["(seq.suffixof (Seq A) (Seq A) Bool)"]
        (K_zero_two
          (string_or_seq_two "smtstr_suffixof"
            (fn (suffix, sequence) =>
              rich_list_app "IS_SUFFIX" [sequence, suffix])))
    ]

    val tydict = dictionary_of_entries tyentries
    val tmdict = dictionary_of_entries tmentries
    val metadata =
      metadata_of_entries "Seq_Extensions" "sort" tyentries @
      metadata_of_entries "Seq_Extensions" "term" tmentries

  end

  structure Z3_Extensions =
  struct
    val tyentries = [
      extension_entry "Z3" "Set" (parametric_attributes ["Element"])
        ["(Set Element)"] (K_zero_one set_ty)
    ]
    val tydict = dictionary_of_entries tyentries
    val tmdict :
      (string, (string -> Term.term list -> Term.term list -> Term.term) list)
        Redblackmap.dict = Redblackmap.mkDict String.compare
    val metadata = metadata_of_entries "Z3_Extensions" "sort" tyentries
  end

  structure CVC5_Seq =
  struct

    fun cvc_term name attrs decl parse =
      extension_entry "cvc5" name attrs decl parse

    fun holsmt_app name args =
      apply_native_const
        (Term.prim_mk_const {Thy = "HolSmt", Name = name}) args

    val tmentries = [
      cvc_term "seq.update" no_attributes
        ["(seq.update (Seq A) Int (Seq A) (Seq A))"]
        (K_zero_three (Seq_Extensions.string_or_seq_three "smtstr_update"
          (fn (s, i, t) => holsmt_app "smt_seq_update" [s, i, t]))),
      cvc_term "seq.replace_all" no_attributes
        ["(seq.replace_all (Seq A) (Seq A) (Seq A) (Seq A))"]
        (K_zero_three (Seq_Extensions.string_or_seq_three
          "smtstr_replace_all"
          (fn (s, t, u) => holsmt_app "smt_seq_replace_all" [s, t, u]))),
      (* cvc5 accepts its String-spelled alias over arbitrary sequences. *)
      cvc_term "str.replace_all" no_attributes
        ["(str.replace_all (Seq A) (Seq A) (Seq A) (Seq A))"]
        (K_zero_three (Seq_Extensions.string_or_seq_three
          "smtstr_replace_all"
          (fn (s, t, u) => holsmt_app "smt_seq_replace_all" [s, t, u]))),
      cvc_term "seq.rev" no_attributes ["(seq.rev (Seq A) (Seq A))"]
        (K_zero_one (Seq_Extensions.string_or_seq_one "smtstr_rev"
          listSyntax.mk_reverse)),
      cvc_term "str.update" no_attributes
        ["(str.update String Int String String)"]
        (K_zero_three (Seq_Extensions.string_or_seq_three "smtstr_update"
          (fn (s, i, t) => holsmt_app "smt_seq_update" [s, i, t]))),
      cvc_term "str.rev" no_attributes ["(str.rev String String)"]
        (K_zero_one (Seq_Extensions.string_or_seq_one "smtstr_rev"
          listSyntax.mk_reverse))
    ]

    val tydict :
      (string, (string -> Term.term list -> Type.hol_type list ->
        Type.hol_type) list) Redblackmap.dict =
      Redblackmap.mkDict String.compare
    val tmdict = dictionary_of_entries tmentries
    val metadata = metadata_of_entries "CVC5_Seq" "term" tmentries
  end

  structure Z3_Seq =
  struct

    fun z3_term name attrs decl parse =
      extension_entry "Z3" name attrs decl parse

    val tyentries = [
      z3_term "Unicode" no_attributes ["(Unicode 0)"]
        (K_zero_zero numSyntax.num)
    ]

    val tmentries = [
      z3_term "Char" (indexed_attributes ["code"])
        ["((_ Char code) Unicode)"]
        (K_one_zero smtstring_char_index),
      z3_term "seq.nth" no_attributes ["(seq.nth String Int Unicode)"]
        (K_zero_two Seq_Extensions.mk_string_nth),
      z3_term "seq.map" no_attributes
        ["(seq.map (-> A B) (Seq A) (Seq B))"]
        (K_zero_two listSyntax.mk_map),
      z3_term "seq.foldl" no_attributes
        ["(seq.foldl (-> B A B) B (Seq A) B)"]
        (K_zero_three listSyntax.mk_foldl),
      z3_term "seq.fold_left" no_attributes
        ["(seq.fold_left (-> B A B) B (Seq A) B)"]
        (K_zero_three listSyntax.mk_foldl)
    ]

    val tydict = dictionary_of_entries tyentries
    val tmdict = dictionary_of_entries tmentries
    val metadata =
      metadata_of_entries "Z3_Seq" "sort" tyentries @
      metadata_of_entries "Z3_Seq" "term" tmentries
  end

  (* cvc5's finite-set dialect.  These entries deliberately live outside
     Z3_Extensions: the two solvers accept disjoint operator spellings. *)
  structure CVC5_Set =
  struct

    fun cvc_term name attrs decl parse =
      extension_entry "cvc5" name attrs decl parse

    fun mk_set_filter (p, s) =
      let
        val x = Term.variant (Term.all_varsl [p, s])
          (Term.mk_var ("set_filter_x", pred_setSyntax.eltype s))
      in
        pred_setSyntax.prim_mk_set_spec
          (x, Term.list_mk_comb (boolSyntax.conjunction,
            [pred_setSyntax.mk_in (x, s), Term.mk_comb (p, x)]), [x])
      end

    fun mk_set_all (p, s) =
      let
        val x = Term.variant (Term.all_varsl [p, s])
          (Term.mk_var ("set_all_x", pred_setSyntax.eltype s))
      in
        boolSyntax.mk_forall (x, boolSyntax.mk_imp
          (pred_setSyntax.mk_in (x, s), Term.mk_comb (p, x)))
      end

    fun mk_set_some (p, s) =
      let
        val x = Term.variant (Term.all_varsl [p, s])
          (Term.mk_var ("set_some_x", pred_setSyntax.eltype s))
      in
        boolSyntax.mk_exists (x, boolSyntax.mk_conj
          (pred_setSyntax.mk_in (x, s), Term.mk_comb (p, x)))
      end

    fun mk_set_insert args =
      case List.rev args of
        s :: element :: elements =>
          List.foldr (fn (x, acc) => pred_setSyntax.mk_insert (x, acc))
            s (List.rev (element :: elements))
      | _ => raise ERR "<set.insert>" "at least two arguments expected"

    fun strip_abs tm =
      let
        fun strip tm (vars, body) =
          case Lib.total Term.dest_abs tm of
            SOME (v, tm) => strip tm (v :: vars, tm)
          | NONE => (List.rev vars, tm)
      in
        strip tm ([], tm)
      end

    fun mk_set_comprehension (predicate, value) =
      let
        val (predicate_vars, predicate_body) = strip_abs predicate
        val (value_vars, value_body) = strip_abs value
        val _ =
          if List.length predicate_vars = List.length value_vars andalso
             ListPair.allEq (Lib.uncurry Term.aconv)
               (predicate_vars, value_vars) then ()
          else raise ERR "<set.comprehension>"
            "predicate and value must bind the same variables"
        val result_var = Term.variant (Term.all_varsl [predicate, value])
          (Term.mk_var ("set_comprehension_x", Term.type_of value_body))
        fun finite_guard var =
          let val ty = Term.type_of var in
            if pred_setSyntax.is_set_type ty then SOME (pred_setSyntax.mk_finite var)
            else if bagSyntax.is_bag_ty ty then
              SOME (Term.mk_comb
                (Term.mk_thy_const {Thy = "bag", Name = "FINITE_BAG",
                  Ty = Type.--> (ty, Type.bool)}, var))
            else NONE
          end
        val guards = List.mapPartial finite_guard predicate_vars
        val predicate_body =
          case guards of
            [] => predicate_body
          | _ => boolSyntax.mk_conj (boolSyntax.list_mk_conj guards,
              predicate_body)
        val body = boolSyntax.list_mk_exists (predicate_vars,
          boolSyntax.mk_conj (predicate_body,
            boolSyntax.mk_eq (result_var, value_body)))
      in
        pred_setSyntax.prim_mk_set_spec (result_var, body, [result_var])
      end

    fun mk_set_singleton x =
      pred_setSyntax.mk_insert
        (x, pred_setSyntax.mk_empty (Term.type_of x))

    fun mk_set_is_empty s =
      boolSyntax.mk_eq (s, pred_setSyntax.mk_empty (pred_setSyntax.eltype s))

    fun mk_set_is_singleton s = pred_setSyntax.mk_sing s

    (* Match cvc5's default carrier for unqualified polymorphic literals.
       Explicitly ascribed Set literals are handled by the parser. *)
    val unqualified_empty = pred_setSyntax.mk_empty Type.bool
    val unqualified_universe = pred_setSyntax.mk_univ Type.bool

    val tyentries = [
      extension_entry "cvc5" "Set" (parametric_attributes ["Element"])
        ["(Set Element)"] (K_zero_one set_ty)
    ]

    val tmentries = [
      cvc_term "set.empty" no_attributes ["(set.empty (Set A))"]
        (K_zero_zero unqualified_empty),
      cvc_term "set.universe" no_attributes ["(set.universe (Set A))"]
        (K_zero_zero unqualified_universe),
      cvc_term "set.member" no_attributes ["(set.member A (Set A) Bool)"]
        (K_zero_two pred_setSyntax.mk_in),
      cvc_term "set.insert" no_attributes ["(set.insert A ... (Set A))"]
        (K_zero_list mk_set_insert),
      cvc_term "set.singleton" no_attributes ["(set.singleton A (Set A))"]
        (K_zero_one mk_set_singleton),
      cvc_term "set.union" left_assoc_attributes
        ["(set.union (Set A) (Set A) (Set A) :left-assoc)"]
        (leftassoc pred_setSyntax.mk_union),
      cvc_term "set.inter" left_assoc_attributes
        ["(set.inter (Set A) (Set A) (Set A) :left-assoc)"]
        (leftassoc pred_setSyntax.mk_inter),
      cvc_term "set.minus" no_attributes
        ["(set.minus (Set A) (Set A) (Set A))"]
        (K_zero_two pred_setSyntax.mk_diff),
      cvc_term "set.subset" no_attributes ["(set.subset (Set A) (Set A) Bool)"]
        (K_zero_two pred_setSyntax.mk_subset),
      cvc_term "set.choose" no_attributes ["(set.choose (Set A) A)"]
        (K_zero_one pred_setSyntax.mk_choice),
      cvc_term "set.card" no_attributes ["(set.card (Set A) Int)"]
        (K_zero_one (fn s => Term.mk_comb (intSyntax.int_injection,
          pred_setSyntax.mk_card s))),
      cvc_term "set.map" no_attributes ["(set.map (-> A B) (Set A) (Set B))"]
        (K_zero_two pred_setSyntax.mk_image),
      cvc_term "set.filter" no_attributes ["(set.filter (-> A Bool) (Set A) (Set A))"]
        (K_zero_two mk_set_filter),
      cvc_term "set.all" no_attributes ["(set.all (-> A Bool) (Set A) Bool)"]
        (K_zero_two mk_set_all),
      cvc_term "set.some" no_attributes ["(set.some (-> A Bool) (Set A) Bool)"]
        (K_zero_two mk_set_some),
      cvc_term "set.is_empty" no_attributes ["(set.is_empty (Set A) Bool)"]
        (K_zero_one mk_set_is_empty),
      cvc_term "set.is_singleton" no_attributes
        ["(set.is_singleton (Set A) Bool)"]
        (K_zero_one mk_set_is_singleton),
      cvc_term "set.comprehension" no_attributes
        ["(set.comprehension ((x A)) Bool A (Set A))"]
        (K_zero_two mk_set_comprehension)
    ]

    val tydict = dictionary_of_entries tyentries
    val tmdict = dictionary_of_entries tmentries
    val first_order_tmdict = dictionary_of_entries (List.filter
      (fn {name, ...} => not (List.exists (Lib.equal name)
        ["set.map", "set.filter", "set.all", "set.some"])) tmentries)
    val metadata =
      metadata_of_entries "CVC5_Set" "sort" tyentries @
      metadata_of_entries "CVC5_Set" "term" tmentries
  end

  (* cvc5's finite-bag dialect.  A bag is represented by its stock HOL
     multiplicity function, [A -> num].  The Int-valued cvc5 count boundary
     is made explicit with [int_of_num].  A bag literal clamps a negative
     Int count to zero, as confirmed by the matrix probe. *)
  structure CVC5_Bag =
  struct

    fun cvc_term name attrs decl parse =
      extension_entry "cvc5" name attrs decl parse

    fun bag_const name ty =
      Term.mk_thy_const {Thy = "bag", Name = name, Ty = ty}

    fun mk_bag_in (x, b) =
      let
        val element = Term.type_of x
        val bag = Type.--> (element, numSyntax.num)
      in
        Term.list_mk_comb (bag_const "BAG_IN"
          (Type.--> (element, Type.--> (bag, Type.bool))), [x, b])
      end

    fun mk_bag_count (x, b) =
      Term.mk_comb (intSyntax.int_injection, Term.mk_comb (b, x))

    fun mk_bag_binary name (b, c) =
      let val bag = Term.type_of b in
        Term.list_mk_comb (bag_const name (Type.--> (bag, Type.--> (bag, bag))),
          [b, c])
      end

    fun mk_bag_filter (p, b) =
      let val bag = Term.type_of b in
        Term.list_mk_comb (bag_const "BAG_FILTER"
          (Type.--> (Term.type_of p, Type.--> (bag, bag))), [p, b])
      end

    fun mk_set_of_bag b =
      let
        val bag = Term.type_of b
        val element = bagSyntax.base_type b
      in
        Term.mk_comb (bag_const "SET_OF_BAG"
          (Type.--> (bag, Type.--> (element, Type.bool))), b)
      end

    fun mk_bag_of_set set =
      let
        val set_ty = Term.type_of set
        val (element, _) = Type.dom_rng set_ty
      in
        Term.mk_comb (bag_const "BAG_OF_SET"
          (Type.--> (set_ty, Type.--> (element, numSyntax.num))), set)
      end

    fun mk_bag_literal (x, n) =
      let
        val z = Term.variant (Term.all_varsl [x, n])
          (Term.mk_var ("bag_literal_x", Term.type_of x))
        val count = boolSyntax.mk_cond
          (intSyntax.mk_leq (intSyntax.zero_tm, n), intSyntax.mk_Num n,
           numSyntax.zero_tm)
      in
        Term.mk_abs (z, boolSyntax.mk_cond
          (boolSyntax.mk_eq (z, x), count, numSyntax.zero_tm))
      end

    fun mk_bag_difference_remove (b, c) =
      let
        val x = Term.variant (Term.all_varsl [b, c])
          (Term.mk_var ("bag_difference_remove_x", bagSyntax.base_type b))
      in
        mk_bag_filter
          (Term.mk_abs (x, boolSyntax.mk_neg (mk_bag_in (x, c))), b)
      end

    fun mk_bag_some (p, b) =
      let
        val x = Term.variant (Term.all_varsl [p, b])
          (Term.mk_var ("bag_some_x", bagSyntax.base_type b))
      in
        boolSyntax.mk_exists (x, boolSyntax.mk_conj
          (mk_bag_in (x, b), Term.mk_comb (p, x)))
      end

    fun mk_bag_setof b =
      mk_bag_of_set (mk_set_of_bag b)

    (* cvc5's unqualified polymorphic literal defaults to [Bag Bool], just
       as its parser does when no explicit [as] qualification is present.
       HOL applications require exact types rather than SMT's bidirectional
       type inference, so retain that documented default here; explicitly
       ascribed literals are handled in the parser below. *)
    val unqualified_empty = Term.inst
      [{redex = Type.alpha, residue = Type.bool}] bagSyntax.EMPTY_BAG_tm

    val tyentries = [
      extension_entry "cvc5" "Bag" (parametric_attributes ["Element"])
        ["(Bag Element)"] (K_zero_one bag_ty)
    ]

    (* Probe-backed semantic pin: cvc5 1.3.4 with [--sets-exp] makes
       [(not (= (bag.count 0 (bag.union_max (bag 0 2) (bag 0 3))) 3))]
       and the analogous [inter_min]/2 query both unsatisfiable.  bagTheory
       defines BAG_MERGE pointwise with the greater multiplicity and
       BAG_INTER pointwise with the lesser one.  Therefore union_max and
       inter_min map respectively to those constants, rather than merely
       being guessed from their names. *)
    val tmentries = [
      cvc_term "bag" no_attributes ["(bag A Int (Bag A))"]
        (K_zero_two mk_bag_literal),
      cvc_term "bag.empty" no_attributes ["(bag.empty (Bag A))"]
        (K_zero_zero unqualified_empty),
      cvc_term "bag.count" no_attributes ["(bag.count A (Bag A) Int)"]
        (K_zero_two mk_bag_count),
      cvc_term "bag.member" no_attributes ["(bag.member A (Bag A) Bool)"]
        (K_zero_two mk_bag_in),
      cvc_term "bag.union_disjoint" left_assoc_attributes
        ["(bag.union_disjoint (Bag A) (Bag A) (Bag A) :left-assoc)"]
        (leftassoc bagSyntax.mk_union),
      cvc_term "bag.union_max" left_assoc_attributes
        ["(bag.union_max (Bag A) (Bag A) (Bag A) :left-assoc)"]
        (leftassoc (mk_bag_binary "BAG_MERGE")),
      cvc_term "bag.inter_min" left_assoc_attributes
        ["(bag.inter_min (Bag A) (Bag A) (Bag A) :left-assoc)"]
        (leftassoc (mk_bag_binary "BAG_INTER")),
      cvc_term "bag.difference_subtract" no_attributes
        ["(bag.difference_subtract (Bag A) (Bag A) (Bag A))"]
        (K_zero_two bagSyntax.mk_diff),
      cvc_term "bag.difference_remove" no_attributes
        ["(bag.difference_remove (Bag A) (Bag A) (Bag A))"]
        (K_zero_two mk_bag_difference_remove),
      cvc_term "bag.subbag" no_attributes ["(bag.subbag (Bag A) (Bag A) Bool)"]
        (K_zero_two bagSyntax.mk_sub_bag),
      cvc_term "bag.choose" no_attributes ["(bag.choose (Bag A) A)"]
        (K_zero_one (fn b =>
          Term.mk_comb (bag_const "BAG_CHOICE"
            (Type.--> (Term.type_of b, bagSyntax.base_type b)), b))),
      cvc_term "bag.card" no_attributes ["(bag.card (Bag A) Int)"]
        (K_zero_one (fn b =>
          Term.mk_comb (intSyntax.int_injection, bagSyntax.mk_card b))),
      cvc_term "bag.map" no_attributes
        ["(bag.map (-> A B) (Bag A) (Bag B))"]
        (K_zero_two bagSyntax.mk_image),
      cvc_term "bag.filter" no_attributes
        ["(bag.filter (-> A Bool) (Bag A) (Bag A))"]
        (K_zero_two mk_bag_filter),
      cvc_term "bag.all" no_attributes ["(bag.all (-> A Bool) (Bag A) Bool)"]
        (K_zero_two bagSyntax.mk_every),
      cvc_term "bag.some" no_attributes
        ["(bag.some (-> A Bool) (Bag A) Bool)"]
        (K_zero_two mk_bag_some),
      cvc_term "bag.setof" no_attributes ["(bag.setof (Bag A) (Bag A))"]
        (K_zero_one mk_bag_setof)
    ]

    val tydict = dictionary_of_entries tyentries
    val tmdict = dictionary_of_entries tmentries
    val first_order_tmdict = dictionary_of_entries (List.filter
      (fn {name, ...} => not (List.exists (Lib.equal name)
        ["bag.map", "bag.filter", "bag.all", "bag.some"])) tmentries)
    val metadata =
      metadata_of_entries "CVC5_Bag" "sort" tyentries @
      metadata_of_entries "CVC5_Bag" "term" tmentries
  end

  (* Z3 represents sets as Bool-valued arrays. *)
  structure Z3_Set =
  struct

    fun z3_term name attrs decl parse =
      extension_entry "Z3" name attrs decl parse

    val tmentries = [
      z3_term "union" left_assoc_attributes
        ["(union (Set A) (Set A) (Set A) :left-assoc)"]
        (leftassoc pred_setSyntax.mk_union),
      z3_term "intersection" left_assoc_attributes
        ["(intersection (Set A) (Set A) (Set A) :left-assoc)"]
        (leftassoc pred_setSyntax.mk_inter),
      z3_term "setminus" no_attributes ["(setminus (Set A) (Set A) (Set A))"]
        (K_zero_two pred_setSyntax.mk_diff),
      z3_term "complement" no_attributes ["(complement (Set A) (Set A))"]
        (K_zero_one pred_setSyntax.mk_compl),
      z3_term "subset" no_attributes ["(subset (Set A) (Set A) Bool)"]
        (K_zero_two pred_setSyntax.mk_subset)
    ]

    val tydict :
      (string, (string -> Term.term list -> Type.hol_type list ->
        Type.hol_type) list) Redblackmap.dict =
      Redblackmap.mkDict String.compare
    val tmdict = dictionary_of_entries tmentries
    val metadata = metadata_of_entries "Z3_Set" "term" tmentries
  end

  (* HO-Core *)

  structure HO_Core =
  struct

    val tyentries = [
      official_entry "->" (parametric_attributes ["A", "B"])
        ["(-> A B)"] (fn _ => fn indices => fn args =>
          if List.null indices then
            function_ty args
          else
            raise ERR "<HO-Core.->>" "no indices expected")
    ]

    (* The official apply spelling [_] is also the dictionary catch-all key.
       [apply_operator] checks the token itself so this entry cannot consume an
       unknown symbol routed through the catch-all path.  cvc5 spells the same
       HO-Core operation [@], so its extension entry is deliberately keyed in
       this dictionary and shares the implementation. *)
    val tmentries = [
      official_entry "_" left_assoc_attributes
        ["(par (A B) (_ (-> A B) A B :left-assoc))"]
        (apply_operator "_"),
      extension_entry "cvc5" "@" left_assoc_attributes
        ["cvc5 HO-Core apply: (@ (-> A B) A B :left-assoc)"]
        (apply_operator "@")
    ]

    val tydict = dictionary_of_entries tyentries
    val tmdict = dictionary_of_entries tmentries
    val metadata =
      metadata_of_entries "HO-Core" "sort" tyentries @
      metadata_of_entries "HO-Core" "term" tmentries

  end

  (* ArraysEx *)

  structure ArraysEx =
  struct

    val tyentries = [
      (* arrays are translated as functions *)
      official_entry "Array" (parametric_attributes ["Index", "Element"])
        ["(Array Index Element)"] (K_zero_two Type.-->)
    ]

    val tmentries = [
      (* array lookup is translated as function application *)
      official_entry "select" no_attributes
        ["(par (Index Element) (select (Array Index Element) Index Element))"]
        (K_zero_two Term.mk_comb),
      (* array update is translated as function update *)
      official_entry "store" no_attributes
        ["(par (Index Element) (store (Array Index Element) Index Element Element (Array Index Element)))"]
        (K_zero_three (fn (array, index, value) =>
          Term.mk_comb (combinSyntax.mk_update (index, value), array)))
    ]

    val tydict = dictionary_of_entries tyentries
    val tmdict = dictionary_of_entries tmentries
    val metadata =
      metadata_of_entries "ArraysEx" "sort" tyentries @
      metadata_of_entries "ArraysEx" "term" tmentries

  end

  (* Fixed_Size_BitVectors *)

  structure Fixed_Size_BitVectors =
  struct

    val tyentries = [
      official_entry "BitVec" (indexed_attributes ["m"])
        ["((_ BitVec m) 0)"] (K_one_zero
          (wordsSyntax.mk_word_type o fcpLib.index_type o
            numSyntax.dest_numeral))
    ]

    val tmentries = [
      (* bit-vector constants *)
      official_entry "_" (indexed_attributes ["m"])
        ["#b<binary>", "#x<hexadecimal>"] (zero_zero (fn token =>
        if String.isPrefix "#b" token then
          let
            val binary = String.extract (token, 2, NONE)
            val value = Arbnum.fromBinString binary
            val size = Arbnum.fromInt (String.size binary)
          in
            wordsSyntax.mk_word (value, size)
          end
        else if String.isPrefix "#x" token then
          let
            val hex = String.extract (token, 2, NONE)
            val value = Arbnum.fromHexString hex
            val size = Arbnum.times2 (Arbnum.times2 (Arbnum.fromInt
              (String.size hex)))
          in
            wordsSyntax.mk_word (value, size)
          end
        else
          raise ERR "<Fixed_Size_BitVectors.tmdict._>"
            "not a bit-vector constant")),
      official_entry "_" (indexed_attributes ["m"])
        ["((_ bv<numeral> m) (_ BitVec m))"]
        (one_zero bv_decimal_constant),
      official_entry "concat" no_attributes
        ["(par (m n) (concat (_ BitVec m) (_ BitVec n) (_ BitVec (+ m n))))"]
        (K_zero_two wordsSyntax.mk_word_concat),
      official_entry "extract" (indexed_attributes ["i", "j"])
        ["((_ extract i j) (_ BitVec m) (_ BitVec (- i j -1)))"]
        (K_two_one (fn (m_tm, n_tm) =>
        let
          val (m, n) = Lib.pair_map (Arbint.toNat o intSyntax.int_of_term)
            (m_tm, n_tm)
          val index_type = fcpLib.index_type (Arbnum.plus1 (Arbnum.- (m, n)))
          val (m, n) = Lib.pair_map numSyntax.mk_numeral (m, n)
        in
          fn t => wordsSyntax.mk_word_extract (m, n, t, index_type)
        end)),
      extension_entry "cvc5" "@bit_of" (indexed_attributes ["i"])
        ["cvc5 proof term: ((_ @bit_of i) (_ BitVec m) Bool)"]
        (K_one_one (fn n => fn t =>
          wordsSyntax.mk_word_bit (numSyntax.mk_numeral (natural_of_index n),
            t))),
      extension_entry "cvc5" "@bbterm" no_attributes
        ["cvc5 proof term: (@bbterm Bool... (_ BitVec m))"]
        (K_zero_list mk_bbterm),
      official_entry "bvnot" no_attributes ["(bvnot (_ BitVec m) (_ BitVec m))"]
        (K_zero_one wordsSyntax.mk_word_1comp),
      official_entry "bvneg" no_attributes ["(bvneg (_ BitVec m) (_ BitVec m))"]
        (K_zero_one wordsSyntax.mk_word_2comp),
      official_entry "bvand" left_assoc_attributes
        ["(bvand (_ BitVec m) (_ BitVec m) (_ BitVec m) :left-assoc)"]
        (leftassoc wordsSyntax.mk_word_and),
      official_entry "bvor" left_assoc_attributes
        ["(bvor (_ BitVec m) (_ BitVec m) (_ BitVec m) :left-assoc)"]
        (leftassoc wordsSyntax.mk_word_or),
      official_entry "bvxor" left_assoc_attributes
        ["(bvxor (_ BitVec m) (_ BitVec m) (_ BitVec m) :left-assoc)"]
        (leftassoc wordsSyntax.mk_word_xor),
      official_entry "bvxnor" no_attributes
        ["(bvxnor (_ BitVec m) (_ BitVec m) (_ BitVec m))"]
        (K_zero_two wordsSyntax.mk_word_xnor),
      official_entry "bvadd" left_assoc_attributes
        ["(bvadd (_ BitVec m) (_ BitVec m) (_ BitVec m) :left-assoc)"]
        (leftassoc wordsSyntax.mk_word_add),
      official_entry "bvmul" left_assoc_attributes
        ["(bvmul (_ BitVec m) (_ BitVec m) (_ BitVec m) :left-assoc)"]
        (leftassoc wordsSyntax.mk_word_mul),
      official_entry "bvudiv" (soundness_audit_attributes no_attributes)
        ["(bvudiv (_ BitVec m) (_ BitVec m) (_ BitVec m)); division-by-zero semantics require soundness audit"]
        (K_zero_two wordsSyntax.mk_word_div),
      official_entry "bvurem" (soundness_audit_attributes no_attributes)
        ["(bvurem (_ BitVec m) (_ BitVec m) (_ BitVec m)); division-by-zero semantics require soundness audit"]
        (K_zero_two wordsSyntax.mk_word_mod),
      official_entry "bvsub" no_attributes
        ["(bvsub (_ BitVec m) (_ BitVec m) (_ BitVec m))"]
        (K_zero_two wordsSyntax.mk_word_sub),
      official_entry "bvnand" no_attributes
        ["(bvnand (_ BitVec m) (_ BitVec m) (_ BitVec m))"]
        (K_zero_two wordsSyntax.mk_word_nand),
      official_entry "bvnor" no_attributes
        ["(bvnor (_ BitVec m) (_ BitVec m) (_ BitVec m))"]
        (K_zero_two wordsSyntax.mk_word_nor),
      official_entry "bvcomp" no_attributes
        ["(bvcomp (_ BitVec m) (_ BitVec m) (_ BitVec 1))"]
        (K_zero_two wordsSyntax.mk_word_compare),
      official_entry "bvsdiv" (soundness_audit_attributes no_attributes)
        ["(bvsdiv (_ BitVec m) (_ BitVec m) (_ BitVec m)); division-by-zero semantics require soundness audit"]
        (K_zero_two wordsSyntax.mk_word_quot),
      official_entry "bvsrem" (soundness_audit_attributes no_attributes)
        ["(bvsrem (_ BitVec m) (_ BitVec m) (_ BitVec m)); division-by-zero semantics require soundness audit"]
        (K_zero_two wordsSyntax.mk_word_rem),
      official_entry "bvsmod" (soundness_audit_attributes no_attributes)
        ["(bvsmod (_ BitVec m) (_ BitVec m) (_ BitVec m)); division-by-zero semantics require soundness audit"]
        (K_zero_two integer_wordSyntax.mk_word_smod),
      official_entry "bvshl" no_attributes
        ["(bvshl (_ BitVec m) (_ BitVec m) (_ BitVec m))"]
        (K_zero_two wordsSyntax.mk_word_lsl_bv),
      official_entry "bvlshr" no_attributes
        ["(bvlshr (_ BitVec m) (_ BitVec m) (_ BitVec m))"]
        (K_zero_two wordsSyntax.mk_word_lsr_bv),
      official_entry "bvashr" no_attributes
        ["(bvashr (_ BitVec m) (_ BitVec m) (_ BitVec m))"]
        (K_zero_two wordsSyntax.mk_word_asr_bv),
      official_entry "repeat" (indexed_attributes ["i"])
        ["((_ repeat i) (_ BitVec m) (_ BitVec (* i m)))"]
        (K_one_one
          (Lib.curry wordsSyntax.mk_word_replicate o numSyntax.mk_numeral o
            natural_of_index)),
      official_entry "zero_extend" (indexed_attributes ["i"])
        ["((_ zero_extend i) (_ BitVec m) (_ BitVec (+ m i)))"]
        (K_one_one (fn n => fn t =>
          wordsSyntax.mk_w2w (t, mk_word_size_add n t))),
      official_entry "sign_extend" (indexed_attributes ["i"])
        ["((_ sign_extend i) (_ BitVec m) (_ BitVec (+ m i)))"]
        (K_one_one (fn n => fn t =>
          wordsSyntax.mk_sw2sw (t, mk_word_size_add n t))),
      official_entry "rotate_left" (indexed_attributes ["i"])
        ["((_ rotate_left i) (_ BitVec m) (_ BitVec m))"]
        (K_one_one
          (Lib.C (Lib.curry wordsSyntax.mk_word_rol) o
            numSyntax.mk_numeral o natural_of_index)),
      official_entry "rotate_right" (indexed_attributes ["i"])
        ["((_ rotate_right i) (_ BitVec m) (_ BitVec m))"]
        (K_one_one
          (Lib.C (Lib.curry wordsSyntax.mk_word_ror) o
            numSyntax.mk_numeral o natural_of_index)),
      official_entry "bvult" no_attributes
        ["(bvult (_ BitVec m) (_ BitVec m) Bool)"]
        (K_zero_two wordsSyntax.mk_word_lo),
      official_entry "bvule" no_attributes
        ["(bvule (_ BitVec m) (_ BitVec m) Bool)"]
        (K_zero_two wordsSyntax.mk_word_ls),
      official_entry "bvugt" no_attributes
        ["(bvugt (_ BitVec m) (_ BitVec m) Bool)"]
        (K_zero_two wordsSyntax.mk_word_hi),
      official_entry "bvuge" no_attributes
        ["(bvuge (_ BitVec m) (_ BitVec m) Bool)"]
        (K_zero_two wordsSyntax.mk_word_hs),
      official_entry "bvslt" no_attributes
        ["(bvslt (_ BitVec m) (_ BitVec m) Bool)"]
        (K_zero_two wordsSyntax.mk_word_lt),
      official_entry "bvsle" no_attributes
        ["(bvsle (_ BitVec m) (_ BitVec m) Bool)"]
        (K_zero_two wordsSyntax.mk_word_le),
      official_entry "bvsgt" no_attributes
        ["(bvsgt (_ BitVec m) (_ BitVec m) Bool)"]
        (K_zero_two wordsSyntax.mk_word_gt),
      official_entry "bvsge" no_attributes
        ["(bvsge (_ BitVec m) (_ BitVec m) Bool)"]
        (K_zero_two wordsSyntax.mk_word_ge),
      official_entry "ubv_to_int" no_attributes
        ["(ubv_to_int (_ BitVec m) Int)"]
        (K_zero_one (intSyntax.mk_injected o wordsSyntax.mk_w2n)),
      official_entry "sbv_to_int" no_attributes
        ["(sbv_to_int (_ BitVec m) Int)"]
        (K_zero_one integer_wordSyntax.mk_w2i),
      official_entry "int_to_bv" (indexed_attributes ["m"])
        ["((_ int_to_bv m) Int (_ BitVec m))"]
        (K_one_one (fn n => fn t =>
          integer_wordSyntax.mk_i2w (t, word_index_type n))),
      official_entry "bvnego" no_attributes
        ["(bvnego (_ BitVec m) Bool)"] (K_zero_one mk_bvnego),
      official_entry "bvuaddo" no_attributes
        ["(bvuaddo (_ BitVec m) (_ BitVec m) Bool)"]
        (K_zero_two mk_bvuaddo),
      official_entry "bvsaddo" no_attributes
        ["(bvsaddo (_ BitVec m) (_ BitVec m) Bool)"]
        (K_zero_two mk_bvsaddo),
      official_entry "bvumulo" no_attributes
        ["(bvumulo (_ BitVec m) (_ BitVec m) Bool)"]
        (K_zero_two mk_bvumulo),
      official_entry "bvsmulo" no_attributes
        ["(bvsmulo (_ BitVec m) (_ BitVec m) Bool)"]
        (K_zero_two mk_bvsmulo),
      official_entry "bvusubo" no_attributes
        ["(bvusubo (_ BitVec m) (_ BitVec m) Bool)"]
        (K_zero_two mk_bvusubo),
      official_entry "bvssubo" no_attributes
        ["(bvssubo (_ BitVec m) (_ BitVec m) Bool)"]
        (K_zero_two mk_bvssubo),
      official_entry "bvsdivo" no_attributes
        ["(bvsdivo (_ BitVec m) (_ BitVec m) Bool)"]
        (K_zero_two mk_bvsdivo)
    ]

    val tydict = dictionary_of_entries tyentries
    val tmdict = dictionary_of_entries tmentries
    val metadata =
      metadata_of_entries "Fixed_Size_BitVectors" "sort" tyentries @
      metadata_of_entries "Fixed_Size_BitVectors" "term" tmentries

  end

  (* Core *)

  structure Core =
  struct

    val tyentries = [
      official_entry "Bool" no_attributes ["(Bool 0)"]
        (K_zero_zero Type.bool)
    ]

    val tmentries = [
      official_entry "true" no_attributes ["(true Bool)"]
        (K_zero_zero boolSyntax.T),
      official_entry "false" no_attributes ["(false Bool)"]
        (K_zero_zero boolSyntax.F),
      official_entry "not" no_attributes ["(not Bool Bool)"]
        (K_zero_one boolSyntax.mk_neg),
      official_entry "=>" right_assoc_attributes
        ["(=> Bool Bool Bool :right-assoc)"] (rightassoc boolSyntax.mk_imp),
      (* TASK_19/F5 decision, PLAN_phase_1.md §7 F5 / P1.1: keep the
         SMT-LIB-visible :left-assoc metadata for "and" and "or", but
         build right-associated HOL terms.  HOL4's Boolean syntax and
         proof replay depend on the right-associated shape; conjunction
         and disjunction are associative, so the meaning is unchanged. *)
      official_entry "and" left_assoc_attributes
        ["(and Bool Bool Bool :left-assoc)"]
        (rightassoc boolSyntax.mk_conj),
      official_entry "or" left_assoc_attributes
        ["(or Bool Bool Bool :left-assoc)"]
        (rightassoc boolSyntax.mk_disj),
      official_entry "xor" left_assoc_attributes
        ["(xor Bool Bool Bool :left-assoc)"]
        (leftassoc (fn (t1, t2) => Term.mk_comb (Term.mk_comb
          (Term.prim_mk_const {Thy="HolSmt", Name="xor"}, t1), t2))),
      official_entry "=" (overloaded_attributes chainable_attributes)
        ["(par (A) (= A A Bool :chainable))"]
        (chainable boolSyntax.mk_eq),
      (* "distinct" is declared as :pairwise in SMT-LIB, but rather
         than unfolding the definition of :pairwise, we use
         'mk_all_distinct' *)
      official_entry "distinct" (overloaded_attributes pairwise_attributes)
        ["(par (A) (distinct A A Bool :pairwise))"]
        (K_zero_list (fn ts => listSyntax.mk_all_distinct
          (listSyntax.mk_list (ts, Term.type_of (List.hd ts))))),
      official_entry "ite" (overloaded_attributes (parametric_attributes ["A"]))
        ["(par (A) (ite Bool A A A))"] (K_zero_three boolSyntax.mk_cond)
    ]

    val tydict = dictionary_of_entries tyentries
    val tmdict = dictionary_of_entries tmentries
    val metadata =
      metadata_of_entries "Core" "sort" tyentries @
      metadata_of_entries "Core" "term" tmentries

  end

  (* Ints *)

  structure Ints =
  struct

    val tyentries = [
      official_entry "Int" no_attributes ["(Int 0)"]
        (K_zero_zero intSyntax.int_ty)
    ]

    val tmentries = [
      (* numerals *)
      official_entry "_" no_attributes ["<numeral>"] (zero_zero (fn token =>
        if is_numeral token then
          intSyntax.term_of_int (Arbint.fromString token)
        else
          raise ERR "<Ints.tmdict._>" "not a numeral")),
      official_entry "-" no_attributes ["(- Int Int)"]
        (K_zero_one intSyntax.mk_negated),
      official_entry "-" left_assoc_attributes ["(- Int Int Int)"]
        (leftassoc intSyntax.mk_minus),
      official_entry "+" left_assoc_attributes ["(+ Int Int Int :left-assoc)"]
        (leftassoc intSyntax.mk_plus),
      official_entry "*" left_assoc_attributes ["(* Int Int Int :left-assoc)"]
        (leftassoc intSyntax.mk_mult),
      official_entry "**" no_attributes ["(** Int Int Int)"]
        (K_zero_two (fn (base, exponent) =>
          intSyntax.mk_exp (base, intSyntax.mk_Num exponent))),
      official_entry "div" left_assoc_attributes ["(div Int Int Int :left-assoc)"]
        (leftassoc mk_int_ediv),
      extension_entry "Z3" "div0" left_assoc_attributes
        ["(div0 Int Int Int :left-assoc)"]
        (leftassoc mk_int_ediv),
      official_entry "mod" left_assoc_attributes ["(mod Int Int Int :left-assoc)"]
        (leftassoc mk_int_emod),
      extension_entry "Z3" "mod0" left_assoc_attributes
        ["(mod0 Int Int Int :left-assoc)"]
        (leftassoc mk_int_emod),
      official_entry "abs" no_attributes ["(abs Int Int)"]
        (K_zero_one intSyntax.mk_absval),
      official_entry "divisible" (indexed_attributes ["n"])
        ["((_ divisible n) Int Bool)"]
        (K_one_one (fn n => fn t => intSyntax.mk_divides (n, t))),
      official_entry "<=" chainable_attributes ["(<= Int Int Bool :chainable)"]
        (chainable intSyntax.mk_leq),
      official_entry "<" chainable_attributes ["(< Int Int Bool :chainable)"]
        (chainable intSyntax.mk_less),
      official_entry ">=" chainable_attributes ["(>= Int Int Bool :chainable)"]
        (chainable intSyntax.mk_geq),
      official_entry ">" chainable_attributes ["(> Int Int Bool :chainable)"]
        (chainable intSyntax.mk_greater)
    ]

    val tydict = dictionary_of_entries tyentries
    val tmdict = dictionary_of_entries tmentries
    val metadata =
      metadata_of_entries "Ints" "sort" tyentries @
      metadata_of_entries "Ints" "term" tmentries

  end

  (* Reals *)

  structure Reals =
  struct

    val tyentries = [
      official_entry "Real" no_attributes ["(Real 0)"]
        (K_zero_zero realSyntax.real_ty)
    ]

    val tmentries = [
      (* numerals *)
      official_entry "_" no_attributes ["<numeral>"] (zero_zero (fn token =>
        if is_numeral token then
          realSyntax.term_of_int (Arbint.fromString token)
        else
          raise ERR "<Reals.tmdict._>" "not a numeral")),
      (* decimals *)
      official_entry "_" no_attributes ["<decimal>"] (zero_zero real_of_decimal),
      official_entry "-" no_attributes ["(- Real Real)"]
        (K_zero_one realSyntax.mk_negated),
      official_entry "-" left_assoc_attributes ["(- Real Real Real)"]
        (leftassoc realSyntax.mk_minus),
      official_entry "+" left_assoc_attributes ["(+ Real Real Real :left-assoc)"]
        (leftassoc realSyntax.mk_plus),
      official_entry "*" left_assoc_attributes ["(* Real Real Real :left-assoc)"]
        (leftassoc realSyntax.mk_mult),
      official_entry "/" left_assoc_attributes ["(/ Real Real Real :left-assoc)"]
        (leftassoc (fn (t1, t2) => Term.mk_comb (Term.mk_comb
          (Term.prim_mk_const {Thy="HolSmt", Name="smt_rdiv"}, t1), t2))),
      official_entry "<=" chainable_attributes ["(<= Real Real Bool :chainable)"]
        (chainable realSyntax.mk_leq),
      official_entry "<" chainable_attributes ["(< Real Real Bool :chainable)"]
        (chainable realSyntax.mk_less),
      official_entry ">=" chainable_attributes ["(>= Real Real Bool :chainable)"]
        (chainable realSyntax.mk_geq),
      official_entry ">" chainable_attributes ["(> Real Real Bool :chainable)"]
        (chainable realSyntax.mk_greater)
    ]

    val tydict = dictionary_of_entries tyentries
    val tmdict = dictionary_of_entries tmentries
    val metadata =
      metadata_of_entries "Reals" "sort" tyentries @
      metadata_of_entries "Reals" "term" tmentries

  end

  (* Reals_Ints *)

  structure Reals_Ints =
  struct

    val tydict = Library.dict_from_list [
      ("Int", K_zero_zero intSyntax.int_ty),
      ("Real", K_zero_zero realSyntax.real_ty)
    ]

    val tmdict = Library.dict_from_list [
      (* numerals *)
      ("_", zero_zero (fn token =>
        if is_numeral token then
          intSyntax.term_of_int (Arbint.fromString token)
        else
          raise ERR "<Reals_Ints.tmdict._>" "not a numeral")),
      ("-", K_zero_one intSyntax.mk_negated),
      ("-", leftassoc intSyntax.mk_minus),
      ("+", leftassoc intSyntax.mk_plus),
      ("*", leftassoc intSyntax.mk_mult),
      ("**", K_zero_two (fn (base, exponent) =>
        intSyntax.mk_exp (base, intSyntax.mk_Num exponent))),
      ("div", leftassoc mk_int_ediv),
      ("div0", leftassoc mk_int_ediv),
      ("mod", leftassoc mk_int_emod),
      ("mod0", leftassoc mk_int_emod),
      ("abs", K_zero_one intSyntax.mk_absval),
      ("divisible", K_one_one (fn n => fn t => intSyntax.mk_divides (n, t))),
      ("<=", chainable intSyntax.mk_leq),
      ("<", chainable intSyntax.mk_less),
      (">=", chainable intSyntax.mk_geq),
      (">", chainable intSyntax.mk_greater),
      (* decimals *)
      ("_", zero_zero real_of_decimal),
      ("-", K_zero_one realSyntax.mk_negated),
      ("-", leftassoc realSyntax.mk_minus),
      ("+", leftassoc realSyntax.mk_plus),
      ("*", leftassoc realSyntax.mk_mult),
      ("/", leftassoc (fn (t1, t2) => Term.mk_comb (Term.mk_comb
          (Term.prim_mk_const {Thy="HolSmt", Name="smt_rdiv"}, t1), t2))),
      ("<=", chainable realSyntax.mk_leq),
      ("<", chainable realSyntax.mk_less),
      (">=", chainable realSyntax.mk_geq),
      (">", chainable realSyntax.mk_greater),
      ("to_real", K_zero_one intrealSyntax.mk_real_of_int),
      ("to_int", K_zero_one intrealSyntax.mk_INT_FLOOR),
      ("is_int", K_zero_one intrealSyntax.mk_is_int)
    ]

    val metadata = Ints.metadata @ Reals.metadata @
      metadata_of_entries "Reals_Ints" "term" [
        official_entry "to_real" no_attributes ["(to_real Int Real)"]
          (K_zero_one intrealSyntax.mk_real_of_int),
        official_entry "to_int" no_attributes ["(to_int Real Int)"]
          (K_zero_one intrealSyntax.mk_INT_FLOOR),
        official_entry "is_int" no_attributes ["(is_int Real Bool)"]
          (K_zero_one intrealSyntax.mk_is_int)
      ]

  end

end  (* local *)

end
