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
  floating_point : bool,
  strings : bool,
  sequences : bool,
  sets : bool,
  bags : bool,
  datatypes : bool,
  nonlinear : bool,
  higher_order : bool
}

datatype encoding_mode =
    NativeSMTLIB
  | ConservativeEmbedding
  | Preprocessing

datatype ho_dialect = Standard27 | Z3LambdaArray

datatype standard27_apply_operator = ApplyUnderscore | ApplyAt

datatype regime = FirstOrder | HigherOrder of ho_dialect

datatype translation_record =
    RegimeSelection of {regime : regime, reason : string}
  | LogicSelection of {logic : string, reason : string,
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

(* A proved HOL definition attached to the exact EncodedSymbol record that
   caused the corresponding SMT operator to be emitted in one translation.
   Replay consumers must obtain these through [translation_definitions], not
   from a constant-name inventory: the record is the per-run provenance key. *)
datatype emitted_definition = EmittedDefinition of {
  emitted_symbol : translation_record,
  replay_head : Term.term,
  unfolding : Thm.thm
}

type translation = {
  logic : string,
  regime : regime,
  tydict : (Type.hol_type, string) Redblackmap.dict,
  tmdict : (Term.term * int, string) Redblackmap.dict,
  (* Built lazily.  Diagnostics and checked replay force this through
     [translation_records] and [translation_definitions], respectively. *)
  records : unit -> translation_record list
}

type logic_selection_policy = {
  features : logic_features,
  inferred_logic : string,
  reason : string
} -> {logic : string, reason : string} option

(* The per-theory emitters register the exact stock HOL head that implements
   an SMT operator, together with every solver/version that accepts it.  The
   check deliberately ignores unregistered heads: this infrastructure lands
   before the Seq/Set/Bag emitters, and ordinary pre-existing translations
   must retain their behaviour. *)
type operator_availability = {
  hol_head : Term.term,
  operator : string,
  solver : string,
  versions : string list
}

val operator_availabilities = ref ([] : operator_availability list)

fun register_operator_availability availability =
  operator_availabilities := availability :: !operator_availabilities

fun clear_operator_availabilities () = operator_availabilities := []

fun term_heads tm =
  let
    fun walk tm acc =
      if Term.is_abs tm then
        walk (Lib.snd (Term.dest_abs tm)) acc
      else if Term.is_comb tm then
        let val (rator, rand) = Term.dest_comb tm in
          walk rand (walk rator acc)
        end
      else tm :: acc
  in
    walk tm []
  end

fun check_operator_availability_unless ignore occurs {solver, version} =
  let
    fun available ({solver = registered_solver, versions, ...}
                   : operator_availability) =
      solver = registered_solver andalso
      (case version of NONE => false
       | SOME target_version =>
           (case Library.version_series target_version of
              NONE => false
            | SOME target_series =>
                List.exists (fn registered =>
                  Library.version_series registered = SOME target_series)
                  versions))
    fun check ({hol_head, operator, ...} : operator_availability) =
      if not (ignore hol_head) andalso occurs hol_head andalso
         not (List.exists available (List.filter
           (fn ({hol_head = candidate, operator = candidate_name, ...}
                : operator_availability) =>
             Term.same_const hol_head candidate andalso
             operator = candidate_name)
           (!operator_availabilities))) then
        raise Feedback.mk_HOL_ERR "SmtLib" "check_goal_operator_availability"
          ("SMT-LIB operator '" ^ operator ^ "' is unavailable for solver '" ^
           solver ^ "'" ^
           (case version of NONE => "" | SOME v => " at version '" ^ v ^ "'"))
      else
        ()
  in
    List.app check (!operator_availabilities)
  end

fun check_goal_operator_availability_unless ignore target
    (assumptions, conclusion) =
  let
    val heads = List.concat (List.map term_heads (conclusion :: assumptions))
    fun occurs head = List.exists (fn tm =>
      Term.same_const tm head handle Feedback.HOL_ERR _ => false) heads
  in check_operator_availability_unless ignore occurs target end

fun check_goal_operator_availability target =
  check_goal_operator_availability_unless (Lib.K false) target

local

  (* For successful proof reconstruction, it is important that the
     translation implemented in SmtLib_{Theories,Logics}.sml is an
     inverse of the translation implemented in this file. *)

  val ERR = Feedback.mk_HOL_ERR "SmtLib"
  val WARNING = Feedback.HOL_WARNING "SmtLib"

  val reglan_ty =
    Type.mk_thy_type {Thy = "smtstring", Tyop = "reglan", Args = []}
  val smtstr_ty =
    Type.mk_thy_type {Thy = "smtstring", Tyop = "smtstr", Args = []}
  val smtfp_ty =
    Type.mk_thy_type {
      Thy = "smtfloat", Tyop = "smtfp", Args = [Type.alpha, Type.beta]}
  val smt_rounding_ty =
    Type.mk_thy_type {
      Thy = "smtfloat", Tyop = "smt_rounding", Args = []}

  fun smtstring_const name =
    Term.prim_mk_const {Thy = "smtstring", Name = name}

  fun numeric_type_width ty = fcpSyntax.dest_numeric_type ty

  fun smtfp_format ty =
    let
      val {Thy, Tyop, Args, ...} = Type.dest_thy_type ty
      val (significand_ty, exponent_ty) =
        case Args of
          [significand_ty, exponent_ty] =>
            (significand_ty, exponent_ty)
        | _ => raise ERR "smtfp_format" "smtfp must have two type arguments"
      val _ =
        if Thy = "smtfloat" andalso Tyop = "smtfp" then ()
        else raise ERR "smtfp_format" "not an smtfp type"
      val eb = numeric_type_width exponent_ty
      val sb = Arbnum.plus1 (numeric_type_width significand_ty)
      val two = Arbnum.fromInt 2
      val _ =
        if Arbnum.compare (eb, two) = LESS then
          raise ERR "smtfp_format"
            "exponent width eb must be at least 2"
        else
          ()
      val _ =
        if Arbnum.compare (sb, two) = LESS then
          raise ERR "smtfp_format"
            "significand width sb must be at least 2"
        else
          ()
    in
      (eb, sb)
    end

  fun smtfp_sort ty =
    let val (eb, sb) = smtfp_format ty in
      "(_ FloatingPoint " ^ Arbnum.toString eb ^ " " ^
      Arbnum.toString sb ^ ")"
    end

  (* (HOL type, a function that maps the type to its SMT-LIB sort name) *)
  val builtin_types = List.foldl
    (fn ((ty, x), net) => TypeNet.insert (net, ty, x)) TypeNet.empty [
    (Type.bool, Lib.K "Bool"),
    (intSyntax.int_ty, Lib.K "Int"),
    (realSyntax.real_ty, Lib.K "Real"),
    (* HOL's own :string (a char list) is deliberately absent: string content
       reaches SMT-LIB only through the str_inj images that
       HOL_STRING_TO_SMT_CONV produces, and those have type smtstr. *)
    (smtstr_ty, Lib.K "String"),
    (reglan_ty, Lib.K "(RegLan String)"),
    (* The canonical-NaN subtype has exactly the SMT FloatingPoint universe.
       Raw binary_ieee float records deliberately have no entry here. *)
    (smtfp_ty, smtfp_sort),
    (smt_rounding_ty, Lib.K "RoundingMode"),
    (* bit-vector types *)
    (wordsSyntax.mk_word_type Type.alpha, fn ty =>
      "(_ BitVec " ^ Arbnum.toString
        (fcpSyntax.dest_numeric_type (wordsSyntax.dest_word_type ty)) ^ ")")
   ]

  fun apfst_K value input = Lib.apfst (Lib.K value) input
  val int_emod_tm = Term.prim_mk_const {Thy="integer", Name="emod"}
  val str_inj_tm = smtstring_const "str_inj"
  val smtfp_intro_tm =
    Term.prim_mk_const {Thy = "smtfloat", Name = "smtfp_intro"}
  val smtstr_char_tm = smtstring_const "smtstr_char"
  val smtstr_concat_tm = smtstring_const "smtstr_concat"
  val smtstr_prefixof_tm = smtstring_const "smtstr_prefixof"
  val smtstr_lt_tm = smtstring_const "smtstr_lt"
  val smtstr_le_tm = smtstring_const "smtstr_le"

  fun smtfloat_const name =
    Term.prim_mk_const {Thy = "smtfloat", Name = name}

  type native_fp_info = {
    hol_name : string,
    smt_name : string
  }

  val native_fp_infos : native_fp_info list = [
    {hol_name = "RNE", smt_name = "roundNearestTiesToEven"},
    {hol_name = "RNA", smt_name = "roundNearestTiesToAway"},
    {hol_name = "RTP", smt_name = "roundTowardPositive"},
    {hol_name = "RTN", smt_name = "roundTowardNegative"},
    {hol_name = "RTZ", smt_name = "roundTowardZero"},
    {hol_name = "smtfp_bits", smt_name = "fp"},
    {hol_name = "smtfp_add", smt_name = "fp.add"},
    {hol_name = "smtfp_sub", smt_name = "fp.sub"},
    {hol_name = "smtfp_mul", smt_name = "fp.mul"},
    {hol_name = "smtfp_div", smt_name = "fp.div"},
    {hol_name = "smtfp_fma", smt_name = "fp.fma"},
    {hol_name = "smtfp_sqrt", smt_name = "fp.sqrt"},
    {hol_name = "smtfp_round_to_integral",
     smt_name = "fp.roundToIntegral"},
    {hol_name = "smtfp_rem", smt_name = "fp.rem"},
    {hol_name = "smtfp_min", smt_name = "fp.min"},
    {hol_name = "smtfp_max", smt_name = "fp.max"},
    {hol_name = "smtfp_abs", smt_name = "fp.abs"},
    {hol_name = "smtfp_neg", smt_name = "fp.neg"},
    {hol_name = "smtfp_le", smt_name = "fp.leq"},
    {hol_name = "smtfp_lt", smt_name = "fp.lt"},
    {hol_name = "smtfp_ge", smt_name = "fp.geq"},
    {hol_name = "smtfp_gt", smt_name = "fp.gt"},
    {hol_name = "smtfp_eq", smt_name = "fp.eq"},
    {hol_name = "smtfp_is_normal", smt_name = "fp.isNormal"},
    {hol_name = "smtfp_is_subnormal", smt_name = "fp.isSubnormal"},
    {hol_name = "smtfp_is_zero", smt_name = "fp.isZero"},
    {hol_name = "smtfp_is_infinite", smt_name = "fp.isInfinite"},
    {hol_name = "smtfp_is_nan", smt_name = "fp.isNaN"},
    {hol_name = "smtfp_is_negative", smt_name = "fp.isNegative"},
    {hol_name = "smtfp_is_positive", smt_name = "fp.isPositive"},
    {hol_name = "smtfp_to_real", smt_name = "fp.to_real"}
  ]

  val native_fp_special_infos : native_fp_info list = [
    {hol_name = "smtfp_pzero", smt_name = "+zero"},
    {hol_name = "smtfp_nzero", smt_name = "-zero"},
    {hol_name = "smtfp_pinf", smt_name = "+oo"},
    {hol_name = "smtfp_ninf", smt_name = "-oo"},
    {hol_name = "smtfp_nan", smt_name = "NaN"}
  ]

  val native_fp_conversion_names = [
    "smtfp_from_ieee_bv", "smtfp_to_fp", "smtfp_from_real",
    "smtfp_from_sbv", "smtfp_from_ubv", "smtfp_to_ubv",
    "smtfp_to_sbv"
  ]

  val native_fp_names =
    List.map #hol_name (native_fp_infos @ native_fp_special_infos) @
    native_fp_conversion_names

  type native_string_info = {
    hol_name : string,
    smt_name : string
  }

  val native_string_infos : native_string_info list = [
    {hol_name = "smtstr_concat", smt_name = "str.++"},
    {hol_name = "smtstr_len", smt_name = "str.len"},
    {hol_name = "smtstr_substr", smt_name = "str.substr"},
    {hol_name = "smtstr_update", smt_name = "str.update"},
    {hol_name = "smtstr_rev", smt_name = "str.rev"},
    {hol_name = "smtstr_at", smt_name = "str.at"},
    {hol_name = "smtstr_prefixof", smt_name = "str.prefixof"},
    {hol_name = "smtstr_suffixof", smt_name = "str.suffixof"},
    {hol_name = "smtstr_contains", smt_name = "str.contains"},
    {hol_name = "smtstr_indexof", smt_name = "str.indexof"},
    {hol_name = "smtstr_lt", smt_name = "str.<"},
    {hol_name = "smtstr_le", smt_name = "str.<="},
    {hol_name = "smtstr_char", smt_name = "char"},
    {hol_name = "smtstr_replace", smt_name = "str.replace"},
    {hol_name = "smtstr_replace_all", smt_name = "str.replace_all"},
    {hol_name = "smtstr_replace_re", smt_name = "str.replace_re"},
    {hol_name = "smtstr_replace_re_all", smt_name = "str.replace_re_all"},
    {hol_name = "smtstr_is_digit", smt_name = "str.is_digit"},
    {hol_name = "smtstr_to_code", smt_name = "str.to_code"},
    {hol_name = "smtstr_from_code", smt_name = "str.from_code"},
    {hol_name = "smtstr_to_int", smt_name = "str.to_int"},
    {hol_name = "smtstr_from_int", smt_name = "str.from_int"},
    {hol_name = "reglan_to_re", smt_name = "str.to_re"},
    {hol_name = "smt_in_re", smt_name = "str.in_re"},
    {hol_name = "reglan_none", smt_name = "re.none"},
    {hol_name = "reglan_all", smt_name = "re.all"},
    {hol_name = "reglan_allchar", smt_name = "re.allchar"},
    {hol_name = "reglan_concat", smt_name = "re.++"},
    {hol_name = "reglan_union", smt_name = "re.union"},
    {hol_name = "reglan_inter", smt_name = "re.inter"},
    {hol_name = "reglan_diff", smt_name = "re.diff"},
    {hol_name = "reglan_comp", smt_name = "re.comp"},
    {hol_name = "reglan_star", smt_name = "re.*"},
    {hol_name = "reglan_plus", smt_name = "re.+"},
    {hol_name = "reglan_opt", smt_name = "re.opt"},
    {hol_name = "reglan_range", smt_name = "re.range"},
    {hol_name = "reglan_power", smt_name = "re.^"},
    {hol_name = "reglan_loop", smt_name = "re.loop"}
  ]

  fun native_string_info tm =
    if Term.is_const tm then
      let
        val {Thy, Name, ...} = Term.dest_thy_const tm
      in
        if Thy = "smtstring" then
          List.find
            (fn {hol_name, ...} : native_string_info =>
              hol_name = Name)
            native_string_infos
        else
          NONE
      end
    else
      NONE

  fun is_native_string_const tm = Option.isSome (native_string_info tm)

  (* Recursive failures must bypass the recognizer exception cascade: once a
     term's shape is known, an error in its body is the real diagnostic. *)
  exception NestedTranslation of exn

  type 'term builtin_operations =
    {type_of : 'term -> Type.hol_type,
     dest_list : 'term -> 'term list * Type.hol_type,
     dest_numeral : 'term -> Arbnum.num,
     is_int_literal : 'term -> bool,
     is_int_negated : 'term -> bool,
     int_of_term : 'term -> Arbint.int,
     is_real_literal : 'term -> bool,
     is_real_negated : 'term -> bool,
     real_int_of_term : 'term -> Arbint.int,
     is_word_literal : 'term -> bool,
     dest_word_literal : 'term -> Arbnum.num,
     dim_of : 'term -> Type.hol_type,
     constant : Term.term -> 'term,
     mk_comb : 'term * 'term -> 'term,
     list_mk_comb : 'term * 'term list -> 'term,
     mk_integer : Arbint.int -> 'term,
     is_syntax_error : exn -> bool,
     syntax_error : string -> string -> exn,
     library_syntax_error : exn -> exn}

  val term_builtin_operations : Term.term builtin_operations =
    {type_of=Term.type_of,dest_list=listSyntax.dest_list,
     dest_numeral=numSyntax.dest_numeral,
     is_int_literal=intSyntax.is_int_literal,
     is_int_negated=intSyntax.is_negated,int_of_term=intSyntax.int_of_term,
     is_real_literal=realSyntax.is_real_literal,
     is_real_negated=realSyntax.is_negated,
     real_int_of_term=realSyntax.int_of_term,
     is_word_literal=wordsSyntax.is_word_literal,
     dest_word_literal=wordsSyntax.dest_word_literal,dim_of=wordsSyntax.dim_of,
     constant=fn term => term,mk_comb=Term.mk_comb,
     list_mk_comb=Term.list_mk_comb,
     mk_integer=intSyntax.term_of_int,
     is_syntax_error=fn Feedback.HOL_ERR _ => true | _ => false,
     syntax_error=ERR,library_syntax_error=fn primary => primary}

  (* Adapt only the known helper-generated wrong-arity decline. The callback
     runs on the successful shape branch, outside this exception handler. *)
  fun builtin_one_arg_with (operations : 'term builtin_operations) f values =
    case values of [argument] => f argument
    | _ => (SmtLib_Theories.one_arg f values
        handle primary as SmtLib_Theories.ParseDecline _ =>
          raise (#library_syntax_error operations) primary)
  fun builtin_two_args_with (operations : 'term builtin_operations) f values =
    case values of [left,right] => f (left,right)
    | _ => (SmtLib_Theories.two_args f values
        handle primary as SmtLib_Theories.ParseDecline _ =>
          raise (#library_syntax_error operations) primary)
  fun builtin_three_args_with (operations : 'term builtin_operations)
      f values =
    case values of [first,second,third] => f (first,second,third)
    | _ => (SmtLib_Theories.three_args f values
        handle primary as SmtLib_Theories.ParseDecline _ =>
          raise (#library_syntax_error operations) primary)

  (* The carrier observation returns before this pure Type inspection.
     A carrier's own admission or lifetime error is never caught. *)
  fun builtin_type_with (operations : 'term builtin_operations) inspect
      (ty : Type.hol_type) =
    inspect ty handle primary as Feedback.HOL_ERR _ =>
      raise (#library_syntax_error operations) primary

  fun numeral_string_with (operations : 'term builtin_operations)
      function_name tm =
    Arbnum.toString ((#dest_numeral operations) tm)
    handle primary =>
      if (#is_syntax_error operations) primary then
        raise (#syntax_error operations) function_name
          "expected a numeral index"
      else raise primary

  fun hexadecimal_string_with (operations : 'term builtin_operations)
      function_name tm =
    let
      val value =
        (#dest_numeral operations) tm
        handle primary =>
          if (#is_syntax_error operations) primary then
            raise (#syntax_error operations) function_name
              "expected a numeral character index"
          else raise primary
    in
      SmtLib_String_Literal.hex_num
        (SmtLib_String_Literal.check_code_point "character index" value)
      handle SmtLib_String_Literal.InvalidCodePoint detail =>
        raise (#syntax_error operations) function_name detail
    end

  val numeral_string = numeral_string_with term_builtin_operations

  fun indexed_char_encoding_with (operations : 'term builtin_operations)
      (_, args) =
    builtin_one_arg_with operations
       (fn code =>
         ("(_ char #x" ^
          hexadecimal_string_with operations
            "<builtin_symbols.smtstr_char>" code ^ ")", [])
         handle primary =>
           if (#is_syntax_error operations) primary then
             raise NestedTranslation primary
           else raise primary)
       args

  fun indexed_power_encoding_with (operations : 'term builtin_operations)
      (_, args) =
    builtin_two_args_with operations
      (fn (regex, power) =>
        ("(_ re.^ " ^
         numeral_string_with operations "<builtin_symbols.reglan_power>"
           power ^ ")", [regex])) args

  fun indexed_loop_encoding_with (operations : 'term builtin_operations)
      (_, args) =
    builtin_three_args_with operations
      (fn (regex, lower, upper) =>
        ("(_ re.loop " ^
         numeral_string_with operations "<builtin_symbols.reglan_loop>"
           lower ^ " " ^
         numeral_string_with operations "<builtin_symbols.reglan_loop>"
           upper ^ ")", [regex])) args

  (* One literal grammar serves the Term and graph carriers. Optional
     probes classify only the caller's expected mismatch exceptions.
     memo_string_expression owns no state here: a graph callback must guard
     its exact scoped node and fixed borrow context before cache hits and
     after the thunk, and publish only a returned boolean (including false).
     Exceptions must never be cached. The Term callback calls the thunk. *)
  type 'term literal_recognition_operations = {
    builtin : 'term builtin_operations,
    dest_comb : 'term -> 'term * 'term,
    dest_abs : 'term -> 'term * 'term,
    strip_comb : 'term -> 'term * 'term list,
    term_same_const : 'term -> Term.term -> bool,
    same_const : 'term -> Term.term -> bool,
    known_same_const : Term.term -> 'term -> bool,
    aconv : 'term -> 'term -> bool,
    aconv_known : 'term -> Term.term -> bool,
    free_in : 'term -> 'term -> bool,
    is_Num : 'term -> bool,
    dest_Num : 'term -> 'term,
    dest_leq : 'term -> 'term * 'term,
    is_numeral : 'term -> bool,
    apply_constant : Term.term * 'term -> 'term,
    optional_error : exn -> bool,
    memo_string_expression : 'term -> (unit -> bool) -> bool
  }

  type 'term literal_recognizers = {
    dest_injected_string : 'term -> 'term,
    is_injected_string : 'term -> bool,
    dest_injected_float : 'term -> 'term,
    is_injected_float : 'term -> bool,
    injected_string_operator : 'term -> string,
    dest_injected_string_operation : 'term -> string * 'term list,
    is_injected_string_expression : 'term -> bool,
    is_injected_string_operation : 'term -> bool,
    dest_parsed_bag_literal : 'term -> 'term * 'term,
    is_parsed_bag_literal : 'term -> bool,
    native_string_literal : 'term -> string,
    hexadecimal_string : string -> 'term -> string
  }

  fun carrier_literal_recognizers_with
      (operations : 'term literal_recognition_operations)
      : 'term literal_recognizers =
  let
    val {builtin, dest_comb, dest_abs, strip_comb, term_same_const,
         same_const, known_same_const, aconv, aconv_known, free_in,
         is_Num, dest_Num, dest_leq, is_numeral, apply_constant,
         optional_error, memo_string_expression} = operations
    val ERR = #syntax_error builtin
    fun total f x =
      SOME (f x) handle primary =>
        if optional_error primary then NONE else raise primary
    fun can f x = Option.isSome (total f x)
    fun dest_injected_string tm =
      let
        val (inject, string) = dest_comb tm
        val _ =
          if term_same_const inject str_inj_tm then ()
          else raise ERR "dest_injected_string" "not str_inj"
      in
        string
      end

    fun is_injected_string tm = can dest_injected_string tm

    fun dest_injected_float tm =
      let
        val (inject, float) = dest_comb tm
        val _ =
          if term_same_const inject smtfp_intro_tm then ()
          else raise ERR "dest_injected_float" "not smtfp_intro"
      in
        float
      end

    fun is_injected_float tm = can dest_injected_float tm

    fun injected_string_operator tm =
      if term_same_const tm smtstr_concat_tm then "str.++"
      else if term_same_const tm smtstr_prefixof_tm then "str.prefixof"
      else if term_same_const tm smtstr_lt_tm then "str.<"
      else if term_same_const tm smtstr_le_tm then "str.<="
      else raise ERR "injected_string_operator" "not an injection operator"

    fun dest_injected_string_operation tm =
      let
        val (rator, rands) = strip_comb tm
        val name = injected_string_operator rator
        val _ =
          if List.length rands = 2 then ()
          else raise ERR "dest_injected_string_operation" "wrong arity"
      in
        (name, rands)
      end

    fun is_injected_string_expression tm =
      memo_string_expression tm (fn () =>
        is_injected_string tm orelse
        (case total dest_injected_string_operation tm of
           SOME ("str.++", rands) =>
             List.all is_injected_string_expression rands
         | _ => false))

    fun is_injected_string_operation tm =
      case total dest_injected_string_operation tm of
        SOME (_, rands) => List.all is_injected_string_expression rands
      | NONE => false

    fun dest_parsed_bag_literal tm =
      let
        val (bound, body) = dest_abs tm
        val (cond_head, cond_args) = strip_comb body
        val (test, count, otherwise) =
          if same_const cond_head boolSyntax.conditional then
            case cond_args of
              [test, count, otherwise] => (test, count, otherwise)
            | _ => raise ERR "dest_parsed_bag_literal"
              "wrong conditional arity"
          else
            raise ERR "dest_parsed_bag_literal" "not a conditional"
        val (eq_head, eq_args) = strip_comb test
        val (left, element) =
          if same_const eq_head boolSyntax.equality then
            case eq_args of [left, element] => (left, element)
            | _ => raise ERR "dest_parsed_bag_literal" "wrong equality arity"
          else
            raise ERR "dest_parsed_bag_literal" "not an equality"
        val _ = if aconv bound left then ()
                else raise ERR "dest_parsed_bag_literal" "wrong binder"
        val (count_head, count_args) = strip_comb count
        val integer_count =
          if same_const count_head boolSyntax.conditional then
            (case count_args of
               [nonnegative, nat_count, zero] =>
                 let
                   val _ = if is_Num nat_count then ()
                           else raise ERR "dest_parsed_bag_literal"
                             "not an integer count"
                   val integer_count = dest_Num nat_count
                   val (lower, upper) = dest_leq nonnegative
                   val _ =
                     if aconv_known lower intSyntax.zero_tm andalso
                        aconv upper integer_count andalso
                        aconv_known zero numSyntax.zero_tm then ()
                     else raise ERR "dest_parsed_bag_literal"
                       "wrong count clamp"
                 in integer_count end
             | _ => raise ERR "dest_parsed_bag_literal" "wrong count arity")
          else if is_numeral count then
            apply_constant (intSyntax.int_injection, count)
          else
            raise ERR "dest_parsed_bag_literal" "not a count"
        val _ =
          if free_in bound element orelse
             free_in bound integer_count orelse
             not (aconv_known otherwise numSyntax.zero_tm) then
            raise ERR "dest_parsed_bag_literal"
              "literal element or count depends on binder"
          else ()
      in
        (element, integer_count)
      end

    fun is_parsed_bag_literal tm =
      can dest_parsed_bag_literal tm

    fun native_string_literal tm =
      let
        val (constructor, representation) = dest_comb tm
        val _ =
          if known_same_const
              (smtstring_const "SmtStr") constructor then ()
          else raise ERR "native_string_literal" "not an SMT String"
        val (elements, element_ty) = (#dest_list builtin) representation
        val _ =
          if Type.compare (element_ty, numSyntax.num) = EQUAL then ()
          else raise ERR "native_string_literal"
            "String representation is not a num list"
        fun code_point element =
          let val numeral = (#dest_numeral builtin) element in
            Arbnum.toInt
              (SmtLib_String_Literal.check_code_point "code point" numeral)
            handle SmtLib_String_Literal.InvalidCodePoint detail =>
              raise ERR "native_string_literal" detail
          end
        val code_points = List.map code_point elements
      in
        "\"" ^ SmtLib_String_Literal.encode_string_literal code_points ^ "\""
      end
  in
    {dest_injected_string = dest_injected_string,
     is_injected_string = is_injected_string,
     dest_injected_float = dest_injected_float,
     is_injected_float = is_injected_float,
     injected_string_operator = injected_string_operator,
     dest_injected_string_operation = dest_injected_string_operation,
     is_injected_string_expression = is_injected_string_expression,
     is_injected_string_operation = is_injected_string_operation,
     dest_parsed_bag_literal = dest_parsed_bag_literal,
     is_parsed_bag_literal = is_parsed_bag_literal,
     native_string_literal = native_string_literal,
     hexadecimal_string = hexadecimal_string_with builtin}
  end

  val term_literal_recognition_operations :
      Term.term literal_recognition_operations = {
    builtin = (term_builtin_operations),
    dest_comb = (Term.dest_comb),
    dest_abs = (Term.dest_abs),
    strip_comb = (boolSyntax.strip_comb),
    term_same_const = (Term.same_const),
    same_const = (Library.same_const),
    known_same_const = (Library.same_const),
    aconv = (Term.aconv),
    aconv_known = (Term.aconv),
    free_in = (Term.free_in),
    is_Num = (intSyntax.is_Num),
    dest_Num = (intSyntax.dest_Num),
    dest_leq = (intSyntax.dest_leq),
    is_numeral = (numSyntax.is_numeral),
    apply_constant = (Term.mk_comb),
    optional_error = (fn Portable.Interrupt => false | _ => true),
    memo_string_expression = (fn _ => fn thunk => thunk ())
  }

  val term_literal_recognizers =
    carrier_literal_recognizers_with term_literal_recognition_operations

  val dest_injected_string = #dest_injected_string term_literal_recognizers
  val is_injected_string = #is_injected_string term_literal_recognizers
  val dest_injected_float = #dest_injected_float term_literal_recognizers
  val is_injected_float = #is_injected_float term_literal_recognizers
  val injected_string_operator = #injected_string_operator
    term_literal_recognizers
  val dest_injected_string_operation = #dest_injected_string_operation
    term_literal_recognizers
  val is_injected_string_expression = #is_injected_string_expression
    term_literal_recognizers
  val is_injected_string_operation = #is_injected_string_operation
    term_literal_recognizers
  val hexadecimal_string = #hexadecimal_string term_literal_recognizers

  fun mk_int_emod_with (operations : 'term builtin_operations)
      (dividend, divisor) =
    (#list_mk_comb operations)
      ((#constant operations) int_emod_tm, [dividend, divisor])

  fun literal_int_divides_mod_eq_with (operations : 'term builtin_operations)
      (divisor, dividend) =
    if (#is_int_literal operations) divisor andalso
       Arbint.> ((#int_of_term operations) divisor, Arbint.zero) then
      [mk_int_emod_with operations (dividend, divisor),
       (#mk_integer operations) Arbint.zero]
    else
      raise (#syntax_error operations) "<builtin_symbols.int_divides>"
        "not a positive literal divisor"

  (* returns true iff 'ty' is a word type that is not fixed-width *)
  fun is_non_numeric_word_type ty =
    not (fcpSyntax.is_numeric_type (wordsSyntax.dest_word_type ty))
      handle Feedback.HOL_ERR _ => false

  (* make sure that all word types in 't' are of fixed width; return 's' *)
  fun apfst_fixed_width_with (operations : 'term builtin_operations) s =
    Lib.apfst (fn t =>
      let
        val ty = (#type_of operations) t
        val (domtys, rngty) =
          builtin_type_with operations boolSyntax.strip_fun ty
      in
        if List.exists is_non_numeric_word_type (rngty :: domtys) then
          raise (#syntax_error operations) ("<builtin_symbols." ^ s ^ ">")
            "not a fixed-width word type"
        else
          s
      end)

  (* (HOL term, a function that maps a pair (rator, rands) to an
     SMT-LIB symbol and a list of remaining (still-to-be-encoded)
     argument terms) *)
  type 'term carrier_builtin_encoding =
    ('term * 'term list) -> (string * 'term list)
  type builtin_encoding = Term.term carrier_builtin_encoding

  (* One ordered registry supplies both the ordinary Term encoding and
     carrier encodings. Pattern keys remain the original bounded schemas;
     all operand observation and synthetic construction use this algebra. *)
  fun builtin_symbol_encodings_with (operations : 'term builtin_operations) =
  let
    fun one_arg f values = builtin_one_arg_with operations f values
    fun two_args f values = builtin_two_args_with operations f values
    fun three_args f values = builtin_three_args_with operations f values
    val indexed_char_encoding = indexed_char_encoding_with operations
    val indexed_power_encoding = indexed_power_encoding_with operations
    val indexed_loop_encoding = indexed_loop_encoding_with operations
    val literal_int_divides_mod_eq =
      literal_int_divides_mod_eq_with operations
    fun apfst_fixed_width name input =
      apfst_fixed_width_with operations name input
    (* Native smtstringTheory UnicodeStrings and RegLan surface, derived from
       'native_string_infos' so that the SMT name of an operator is recorded
       in one table only. *)
    val native_string_encodings :
        (Term.term * 'term carrier_builtin_encoding) list =
      List.map
        (fn {hol_name, smt_name} : native_string_info =>
          (smtstring_const hol_name,
           case hol_name of
             "smtstr_char" => indexed_char_encoding
           | "reglan_power" => indexed_power_encoding
           | "reglan_loop" => indexed_loop_encoding
           | _ => apfst_K smt_name))
        native_string_infos

    fun instantiated_result_type tm =
      let val ty = (#type_of operations) tm
      in builtin_type_with operations
        (Lib.snd o boolSyntax.strip_fun) ty end

    fun numeric_word_dimension tm =
      let val dimension = (#dim_of operations) tm
      in builtin_type_with operations fcpSyntax.dest_numeric_type
        dimension end

    fun numeric_word_type_width ty =
      builtin_type_with operations
        (numeric_type_width o wordsSyntax.dest_word_type) ty

    fun indexed_fp_name operator tm =
      let val ty = instantiated_result_type tm
          val (eb, sb) = builtin_type_with operations smtfp_format ty
      in
        "(_ " ^ operator ^ " " ^ Arbnum.toString eb ^ " " ^
        Arbnum.toString sb ^ ")"
      end

    fun fp_special_encoding name (tm, args) =
      if List.null args then
        (indexed_fp_name name tm, [])
      else
        raise (#syntax_error operations) "fp_special_encoding"
          "floating-point special takes no arguments"

    fun fp_target_encoding operator (tm, args) =
      (indexed_fp_name operator tm, args)

    fun fp_to_bv_encoding operator (tm, args) =
      let
        val result_ty = instantiated_result_type tm
        val width = numeric_word_type_width result_ty
      in
        ("(_ " ^ operator ^ " " ^ Arbnum.toString width ^ ")", args)
      end

    val native_fp_encodings :
        (Term.term * 'term carrier_builtin_encoding) list =
      List.map
        (fn {hol_name, smt_name} : native_fp_info =>
          (smtfloat_const hol_name, apfst_K smt_name))
        native_fp_infos @
      List.map
        (fn {hol_name, smt_name} : native_fp_info =>
          (smtfloat_const hol_name, fp_special_encoding smt_name))
        native_fp_special_infos @ [
      (smtfloat_const "smtfp_from_ieee_bv", fp_target_encoding "to_fp"),
      (smtfloat_const "smtfp_to_fp", fp_target_encoding "to_fp"),
      (smtfloat_const "smtfp_from_real", fp_target_encoding "to_fp"),
      (smtfloat_const "smtfp_from_sbv", fp_target_encoding "to_fp"),
      (smtfloat_const "smtfp_from_ubv",
        fp_target_encoding "to_fp_unsigned"),
      (smtfloat_const "smtfp_to_ubv", fp_to_bv_encoding "fp.to_ubv"),
      (smtfloat_const "smtfp_to_sbv", fp_to_bv_encoding "fp.to_sbv")
    ]

    val builtin_symbol_encodings = [
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
        one_arg (fn list_tm =>
          case Lib.fst ((#dest_list operations) list_tm) of
            elements as _ :: _ :: _ => ("distinct", elements)
          | _ => ("true", [])) ts),
      (boolSyntax.conditional, apfst_K "ite"),
      (* UnicodeStrings symbols are reached only through the smtstr operators
         appended from 'native_string_encodings'.  Encoding HOL's STRCAT and
         friends directly would emit str.* applied to arguments whose sort is
         no longer String (see 'builtin_types'). *)
      (* Reals_Ints *)
      (* numerals (excluding 'intSyntax.negate_tm') *)
      (Term.mk_var ("x", intSyntax.int_ty), Lib.apfst (fn tm =>
        if (#is_int_literal operations) tm andalso
           not ((#is_int_negated operations) tm) then
          let
            val i = (#int_of_term operations) tm
            val s = Arbint.toString (Arbint.abs i)
            val s = String.substring (s, 0, String.size s - 1)
          in
            if Arbint.< (i, Arbint.zero) then
              "(- " ^ s ^ ")"
            else
              s
          end
        else
          raise (#syntax_error operations) "<builtin_symbols.x:int>"
            "not a numeral (negated?)")),
      (intSyntax.negate_tm, apfst_K "-"),
      (intSyntax.Num_tm, apfst_K "abs"),
      (intSyntax.minus_tm, apfst_K "-"),
      (intSyntax.plus_tm, apfst_K "+"),
      (intSyntax.mult_tm, apfst_K "*"),
      (Term.prim_mk_const {Thy="integer", Name="ediv"}, apfst_K "div"),
      (Term.prim_mk_const {Thy="integer", Name="emod"}, apfst_K "mod"),
      (intSyntax.absval_tm, apfst_K "abs"),
      (intSyntax.divides_tm, fn (_, ts) =>
        two_args (fn (divisor, dividend) =>
          ("=", literal_int_divides_mod_eq (divisor, dividend))) ts),
      (intSyntax.leq_tm, apfst_K "<="),
      (intSyntax.less_tm, apfst_K "<"),
      (intSyntax.geq_tm, apfst_K ">="),
      (intSyntax.greater_tm, apfst_K ">"),
      (* decimals (excluding 'realSyntax.negate_tm') *)
      (Term.mk_var ("x", realSyntax.real_ty), Lib.apfst (fn tm =>
        if (#is_real_literal operations) tm andalso
           not ((#is_real_negated operations) tm)
            then
          let
            val i = (#real_int_of_term operations) tm
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
          raise (#syntax_error operations) "<builtin_symbols.x:real>"
            "not a decimal (negated?)")),
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
        one_arg (fn r =>
          ("-", [(#mk_comb operations)
            ((#constant operations) intrealSyntax.INT_FLOOR_tm,
             (#mk_comb operations)
               ((#constant operations) realSyntax.negate_tm, r))])) ts),
      (intrealSyntax.is_int_tm, apfst_K "is_int"),
      (* bit-vector constants *)
      (Term.mk_var ("x", wordsSyntax.mk_word_type Type.alpha),
       Lib.apfst (fn tm =>
        if (#is_word_literal operations) tm then
          let
            val value = (#dest_word_literal operations) tm
            val width = numeric_word_dimension tm
          in
            "(_ bv" ^ Arbnum.toString value ^ " " ^ Arbnum.toString width ^ ")"
          end
        else
          raise (#syntax_error operations) "<builtin_symbols.x:'a word>"
            "not a word literal")),
      (wordsSyntax.word_concat_tm, fn (t, ts) =>
        two_args (fn (w1, w2) =>
          let
            (* make sure that the result in HOL has the expected width *)
            val dim1 = numeric_word_dimension w1
            val dim2 = numeric_word_dimension w2
            val rngty = instantiated_result_type t
            val rngdim = numeric_word_type_width rngty
            val _ = if rngdim = Arbnum.+ (dim1, dim2) then
                ()
              else (
                if !Library.trace > 0 then
                  WARNING "translate_term" "word_concat: wrong result type"
                else
                  ();
                raise (#syntax_error operations)
                  "<builtin_symbols.word_concat_tm>" "wrong result type"
              )
          in
            ("concat", ts)
          end) ts),
      (wordsSyntax.word_extract_tm, fn (t, ts) =>
        three_args (fn (i, j, w) =>
          let
            (* make sure that j <= i < dim(w) *)
            val i = (#dest_numeral operations) i
            val j = (#dest_numeral operations) j
            val dim = numeric_word_dimension w
            val _ = if Arbnum.<= (j, i) then
                ()
              else (
                if !Library.trace > 0 then
                  WARNING "translate_term"
                    "word_extract: second index larger than first"
                else
                  ();
                raise (#syntax_error operations)
                  "<builtin_symbols.word_extract_tm>"
                  "second index larger than first"
              )
            val _ = if Arbnum.< (i, dim) then
                ()
              else (
                if !Library.trace > 0 then
                  WARNING "translate_term"
                    "word_extract: first index too large"
                else
                  ();
                raise (#syntax_error operations)
                  "<builtin_symbols.word_extract_tm>"
                  "first index too large"
              )
            (* make sure that the result in HOL has the expected width *)
            val rngty = instantiated_result_type t
            val rngdim = numeric_word_type_width rngty
            val _ = if rngdim = Arbnum.+ (Arbnum.- (i, j), Arbnum.one) then
                ()
              else (
                if !Library.trace > 0 then
                  WARNING "translate_term" "word_extract: wrong result type"
                else
                  ();
                raise (#syntax_error operations)
                  "<builtin_symbols.word_extract_tm>" "wrong result type"
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
        two_args (fn (n, w) =>
          let
            val n = (#dest_numeral operations) n
            (* make sure that the result in HOL has the expected width *)
            val dim = numeric_word_dimension w
            val rngty = instantiated_result_type t
            val rngdim = numeric_word_type_width rngty
            val _ = if rngdim = Arbnum.* (n, dim) then
                ()
              else (
                if !Library.trace > 0 then
                  WARNING "translate_term" "word_replicate: wrong result type"
                else
                  ();
                raise (#syntax_error operations)
                  "<builtin_symbols.word_replicate_tm>"
                  "wrong result type"
              )
          in
            ("(_ repeat " ^ Arbnum.toString n ^ ")", [w])
          end) ts),
      (wordsSyntax.w2w_tm, fn (t, ts) =>
        one_arg (fn w =>
          let
            (* make sure that the result in HOL is at least as long as 'w' *)
            val dim = numeric_word_dimension w
            val rngty = instantiated_result_type t
            val rngdim = numeric_word_type_width rngty
            val _ = if Arbnum.>= (rngdim, dim) then
                ()
              else (
                if !Library.trace > 0 then
                  WARNING "translate_term" "w2w: result type too short"
                else
                  ();
                raise (#syntax_error operations)
                  "<builtin_symbols.w2w_tm>" "result type too short"
              )
            val n = Arbnum.- (rngdim, dim)
          in
            ("(_ zero_extend " ^ Arbnum.toString n ^ ")", [w])
          end) ts),
      (wordsSyntax.sw2sw_tm, fn (t, ts) =>
        one_arg (fn w =>
          let
            (* make sure that the result in HOL is at least as long as 'w' *)
            val dim = numeric_word_dimension w
            val rngty = instantiated_result_type t
            val rngdim = numeric_word_type_width rngty
            val _ = if Arbnum.>= (rngdim, dim) then
                ()
              else (
                if !Library.trace > 0 then
                  WARNING "translate_term" "sw2sw: result type too short"
                else
                  ();
                raise (#syntax_error operations)
                  "<builtin_symbols.sw2sw_tm>" "result type too short"
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
          two_args (fn (w, n) =>
            ("(_ rotate_left " ^ Arbnum.toString ((#dest_numeral operations) n)
              ^ ")", [w])) ts
        )),
      (wordsSyntax.word_ror_tm, fn (t, ts) =>
        (
          apfst_fixed_width "rotate_right" (t, ());
          two_args (fn (w, n) =>
            ("(_ rotate_right " ^
           Arbnum.toString ((#dest_numeral operations) n)
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
    ] @ native_fp_encodings @ native_string_encodings

  in builtin_symbol_encodings end

  val builtin_symbol_encodings =
    builtin_symbol_encodings_with term_builtin_operations

  val builtin_symbols =
    List.foldl (Lib.uncurry Net.insert) Net.empty builtin_symbol_encodings

  (* The (theory, name) pairs of the constant-headed builtin symbols, so that
     `has_ranked_semantics` can test membership in O(log n) rather than
     scanning `builtin_symbol_encodings` with `Term.same_const` per node. *)
  val builtin_const_names =
    List.foldl
      (fn ((builtin, _), acc) =>
        if Term.is_const builtin then
          let val {Thy, Name, ...} = Term.dest_thy_const builtin
          in Redblackset.add (acc, (Thy, Name)) end
        else acc)
      (Redblackset.empty (Lib.pair_compare (String.compare, String.compare)))
      builtin_symbol_encodings

  (* The declared arity of a constant depends only on its (theory, name), and
     'translate_term' asks for the same rator up to four times per application
     node; cache the symbol-table lookup and the type traversal. *)
  val declared_const_arities = ref (Redblackmap.mkDict
    (Lib.pair_compare (String.compare, String.compare)) :
      (string * string, int) Redblackmap.dict)

  fun declared_const_arity c =
    let
      val {Thy, Name, ...} = Term.dest_thy_const c
    in
      case Redblackmap.peek (!declared_const_arities, (Thy, Name)) of
        SOME arity => arity
      | NONE =>
        let
          val generic = Term.prim_mk_const {Thy = Thy, Name = Name}
          val (doms, _) = boolSyntax.strip_fun (Term.type_of generic)
          val arity = List.length doms
        in
          declared_const_arities :=
            Redblackmap.insert (!declared_const_arities, (Thy, Name), arity);
          arity
        end
    end

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

  (* Lists are the native model of SMT sequences, except for HOL strings.
     The latter must retain Phase 4's str_inj/smtstr route rather than being
     silently reclassified as arbitrary (Seq Char) content. *)
  fun is_native_sequence_type ty =
    listSyntax.is_list_type ty andalso
    Type.compare (ty, stringSyntax.string_ty) <> EQUAL

  (* Checked Seq replay is introduced by TASK_18.  Until then, proof
     requests retain the old datatype encoding while oracle emission uses the
     native surface. *)
  val current_native_sequence_emission = ref true

  (* Some collection encodings introduce quantifiers which have no HOL binder
     in the source goal.  Every such emitter must construct its SMT-LIB forall
     through this helper, so logic selection and solver command policy observe
     the syntax that was actually emitted. *)
  val current_generated_forall_emissions = ref 0
  val current_backend_installation = ref (NONE:unit ref option)

  (* Output constructors are pure: they preserve byte order and do not
     render child documents. Sorts and symbol names remain plain strings. *)
  type 'doc output_operations = {
    text : string -> 'doc,
    concat : 'doc list -> 'doc,
    join : string -> 'doc list -> 'doc
  }

  val string_output_operations : string output_operations = {
    text = Lib.I,
    concat = String.concat,
    join = String.concatWith
  }

  fun generated_forall_with (output : 'doc output_operations)
      declarations body =
    (current_generated_forall_emissions :=
       !current_generated_forall_emissions + 1;
     (#concat output)
       [(#text output)
          ("(forall (" ^ String.concatWith " " declarations ^ ") "),
        body, (#text output) ")"])

  fun generated_forall declarations body =
    generated_forall_with string_output_operations declarations body

  (* Snapshot a translation-context cell now; the returned thunk puts it
     back.  Each cell then costs one list entry rather than a declaration,
     a save and a restore that must be kept in step. *)
  fun save_cell r = let val saved = !r in fn () => r := saved end

  fun restore_cells restorers = List.app (fn f => f ()) restorers

  fun sequence_element_type tm =
    if is_native_sequence_type (Term.type_of tm) then
      listSyntax.dest_list_type (Term.type_of tm)
    else
      raise ERR "sequence_element_type" "not a native sequence term"

  fun smt_sort_of_type regime tydict ty =
    if !current_native_sequence_emission andalso
       is_native_sequence_type ty then
      "(Seq " ^ smt_sort_of_type regime tydict
        (listSyntax.dest_list_type ty) ^ ")"
    else if is_function_type ty then
      (case regime of
         HigherOrder Standard27 =>
           let
             val (doms, rng) = boolSyntax.strip_fun ty
             val names = List.map (smt_sort_of_type regime tydict)
               (doms @ [rng])
           in
             "(-> " ^ String.concatWith " " names ^ ")"
           end
       | _ =>
           let
             val (dom, rng) = Type.dom_rng ty
           in
             "(Array " ^ smt_sort_of_type regime tydict dom ^ " " ^
             smt_sort_of_type regime tydict rng ^ ")"
           end)
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
  fun type_has_name thy tyop ty =
    let val {Thy, Tyop, ...} = Type.dest_thy_type ty in
      Thy = thy andalso Tyop = tyop
    end
    handle Feedback.HOL_ERR _ => false
  fun type_is_smtfp ty =
    type_has_name "smtfloat" "smtfp" ty orelse
    type_has_name "smtfloat" "smt_rounding" ty
  fun type_is_binary_ieee_float ty =
    type_has_name "binary_ieee" "float" ty
  fun type_contains_fp ty =
    type_is_smtfp ty orelse
    (List.exists type_contains_fp (Lib.snd (Type.dest_type ty))
      handle Feedback.HOL_ERR _ => false)
  (* smtstr only, which is exactly the set of types that 'builtin_types' maps
     to the SMT-LIB String sort; HOL's :string is an ordinary HOL type here. *)
  val type_contains_string = Library.type_contains_string

  fun type_contains_function ty =
    type_contains is_function_type ty

  val same_const = Library.same_const

  (* Use the same let grammar for Term and graph carriers. The Term
     callbacks retain the stock paired-abstraction and error policies. *)
  val let_binding_operations :
      Term.term SmtLib_CarrierLetBindings.operations =
    {dest_abs = Term.dest_abs,
     dest_let = boolSyntax.dest_let,
     dest_plet = pairSyntax.dest_plet,
     strip_pabs = pairSyntax.strip_pabs,
     list_mk_comb = Term.list_mk_comb,
     is_let = boolSyntax.is_let,
     is_syntax_error = fn Feedback.HOL_ERR _ => true | _ => false,
     not_a_let = fn () => Feedback.mk_HOL_ERR "pairSyntax" "dest_anylet"
       "not a \"let\"-term"}
  val dest_carrier_let =
    SmtLib_CarrierLetBindings.dest_anylet let_binding_operations

  (* HOL represents a set as an ordinary predicate, so the outbound boundary
     records set *terms*, rather than treating every `a -> bool` as a Set.
     The context is installed for one translation only (see
     goal_to_SmtLib_aux).  It lets cvc5 print its finite-set sort without
     changing the representation of unrelated predicates. *)
  datatype set_backend = Z3Set | CVC5NativeSet | CVC5ArraySet

  val current_set_backend = ref Z3Set
  val current_set_terms = ref ([] : Term.term list)
  val current_raw_num_terms = ref ([] : Term.term list)
  val current_collection_function_arguments =
    ref ([] : (Term.term * int * Term.term) list)

  fun contextual_collection_argument function index =
    case List.find
        (fn (other, other_index, _) =>
          index = other_index andalso Term.aconv function other)
        (!current_collection_function_arguments) of
      SOME (_, _, argument) => SOME argument
    | NONE => NONE

  fun has_contextual_collection_argument function =
    List.exists (fn (other, _, _) => Term.aconv function other)
      (!current_collection_function_arguments)

  val native_set_heads = [
    pred_setSyntax.in_tm, pred_setSyntax.insert_tm, pred_setSyntax.delete_tm,
    pred_setSyntax.union_tm, pred_setSyntax.inter_tm, pred_setSyntax.diff_tm,
    pred_setSyntax.compl_tm, pred_setSyntax.subset_tm, pred_setSyntax.empty_tm,
    pred_setSyntax.univ_tm, pred_setSyntax.card_tm
  ]

  (* SmtArrayProve's goal-directed fact table mirrors these emitted heads.
     Derive the audit input from the heads themselves, so extending the
     printer necessarily extends the replay-completeness check. *)
  val native_set_operator_names = List.map
    (fn head => #Name (Term.dest_thy_const head)) native_set_heads

  fun is_native_set_head tm =
    List.exists (fn head => same_const head tm) native_set_heads

  fun is_set_result_type ty =
    let
      val (_, result_ty) = Type.dom_rng ty
    in
      Type.compare (result_ty, Type.bool) = EQUAL
    end
    handle Feedback.HOL_ERR _ => false

  fun is_set_type tm =
    is_set_result_type (Term.type_of tm)
    handle Feedback.HOL_ERR _ => false

  fun set_element_type tm =
    if is_set_type tm then Lib.fst (Type.dom_rng (Term.type_of tm))
    else raise ERR "set_element_type" "not a set-valued term"

  fun mem_aconv tm = List.exists (Term.aconv tm)

  fun add_set_term tm terms =
    if is_set_type tm andalso not (mem_aconv tm terms) then tm :: terms
    else terms

  (* Record only terms at set-typed positions.  Recording all arguments of
     INSERT, for example, incorrectly declares its element as a Set. *)
  fun classify_set_marker_with same_head is_empty is_univ tm =
    if same_head pred_setSyntax.in_tm then
      SmtLib_CollectionMarkers.Membership
    else if same_head pred_setSyntax.card_tm orelse
            same_head pred_setSyntax.finite_tm then
      SmtLib_CollectionMarkers.UnaryObservation
    else if same_head pred_setSyntax.insert_tm then
      SmtLib_CollectionMarkers.Insert
    else if same_head pred_setSyntax.delete_tm then
      SmtLib_CollectionMarkers.Delete
    else if same_head pred_setSyntax.union_tm orelse
            same_head pred_setSyntax.inter_tm orelse
            same_head pred_setSyntax.diff_tm then
      SmtLib_CollectionMarkers.BinaryConstruction
    else if same_head pred_setSyntax.compl_tm then
      SmtLib_CollectionMarkers.UnaryConstruction
    else if same_head pred_setSyntax.subset_tm then
      SmtLib_CollectionMarkers.Inclusion
    else if is_empty tm orelse is_univ tm then
      SmtLib_CollectionMarkers.Empty
    else if same_head boolSyntax.equality then
      SmtLib_CollectionMarkers.Equality
    else SmtLib_CollectionMarkers.Other

  fun classify_set_marker (tm, rator) =
    classify_set_marker_with (same_const rator)
      pred_setSyntax.is_empty pred_setSyntax.is_univ tm

  val set_marker_operations :
      Term.term SmtLib_CollectionMarkers.operations =
    {strip_comb = boolSyntax.strip_comb,
     dest_abs = Term.dest_abs,
     dest_comb = Term.dest_comb,
     condition = Lib.total boolSyntax.dest_cond,
     bindings = fn tm => #1 (dest_carrier_let tm),
     add = add_set_term,
     member = mem_aconv,
     is_collection_type = is_set_type,
     classify = classify_set_marker}
  val collect_native_set_terms =
    SmtLib_CollectionMarkers.collect set_marker_operations
      {propagate_bindings = true, visit_prefix = false}

  fun is_marked_set_term tm = mem_aconv tm (!current_set_terms)

  (* Bool and fixed-width word types have finite SMT-LIB domains.  A
     polymorphic word remains unsupported until its width is instantiated. *)
  fun finite_element_type ty =
    Type.compare (ty, Type.bool) = EQUAL orelse
    (Lib.can wordsSyntax.dest_word_type ty andalso
     Lib.can fcpSyntax.dest_numeric_type (wordsSyntax.dest_word_type ty))

  fun is_set_hol_type ty =
    case Lib.total Type.dom_rng ty of
      SOME (_, range) => Type.compare (range, Type.bool) = EQUAL
    | NONE => false

  (* Bags are likewise functions in HOL, but their integer-valued array
     representation must remain distinct from arbitrary functions. *)
  datatype bag_backend = Z3ArrayBag | CVC5NativeBag | CVC5ArrayBag

  val current_bag_backend = ref Z3ArrayBag
  val current_bag_terms = ref ([] : Term.term list)
  val current_bag_helpers = ref ([] : string list)

  fun bag_const name = Term.prim_mk_const {Thy = "bag", Name = name}

  val bag_in_tm = bag_const "BAG_IN"
  val bag_merge_tm = bag_const "BAG_MERGE"
  val bag_inter_tm = bag_const "BAG_INTER"
  val finite_bag_tm = bag_const "FINITE_BAG"

  val native_bag_heads = [
    bag_in_tm, bagSyntax.BAG_INSERT_tm, bagSyntax.BAG_UNION_tm,
    bagSyntax.BAG_DIFF_tm, bag_merge_tm, bag_inter_tm,
    bagSyntax.SUB_BAG_tm, bagSyntax.BAG_CARD_tm, bagSyntax.EMPTY_BAG_tm
  ]

  val native_bag_operator_names = List.map
    (fn head => #Name (Term.dest_thy_const head)) native_bag_heads

  fun is_native_bag_head tm =
    List.exists (fn head => same_const head tm) native_bag_heads

  fun is_bag_type tm = bagSyntax.is_bag_ty (Term.type_of tm)

  fun bag_element_type tm =
    if is_bag_type tm then bagSyntax.base_type tm
    else raise ERR "bag_element_type" "not a bag-valued term"

  fun add_bag_term tm terms =
    if is_bag_type tm andalso not (mem_aconv tm terms) then tm :: terms
    else terms

  fun dest_bag_binary head tm =
    let val (rator, rands) = boolSyntax.strip_comb tm in
      if same_const rator head then
        case rands of [left, right] => (left, right)
        | _ => raise ERR "dest_bag_binary" "wrong arity"
      else
        raise ERR "dest_bag_binary" "wrong head"
    end

  (* cvc5 bag literals are parsed as their extensional HOL function.  Retain
     this exact shape so a checked proof can be sent back as a Bag literal,
     rather than as an unrelated higher-order lambda. *)
  val dest_parsed_bag_literal = #dest_parsed_bag_literal
    term_literal_recognizers
  val is_parsed_bag_literal = #is_parsed_bag_literal term_literal_recognizers

  fun classify_bag_marker_with same_head is_empty tm =
    if same_head bag_in_tm then
      SmtLib_CollectionMarkers.Membership
    else if same_head bagSyntax.BAG_CARD_tm orelse
            same_head finite_bag_tm then
      SmtLib_CollectionMarkers.UnaryObservation
    else if same_head bagSyntax.BAG_INSERT_tm then
      SmtLib_CollectionMarkers.Insert
    else if same_head bagSyntax.BAG_UNION_tm orelse
            same_head bagSyntax.BAG_DIFF_tm orelse
            same_head bag_merge_tm orelse same_head bag_inter_tm
    then SmtLib_CollectionMarkers.BinaryConstruction
    else if same_head bagSyntax.SUB_BAG_tm then
      SmtLib_CollectionMarkers.Inclusion
    else if is_empty tm then SmtLib_CollectionMarkers.Empty
    else if same_head boolSyntax.equality then
      SmtLib_CollectionMarkers.Equality
    else SmtLib_CollectionMarkers.Other

  fun classify_bag_marker (tm, rator) =
    classify_bag_marker_with (same_const rator) bagSyntax.is_empty tm

  val bag_marker_operations :
      Term.term SmtLib_CollectionMarkers.operations =
    {strip_comb = boolSyntax.strip_comb,
     dest_abs = Term.dest_abs,
     dest_comb = Term.dest_comb,
     condition = Lib.total boolSyntax.dest_cond,
     bindings = fn tm => #1 (dest_carrier_let tm),
     add = add_bag_term,
     member = mem_aconv,
     is_collection_type = is_bag_type,
     classify = classify_bag_marker}
  val collect_native_bag_terms =
    SmtLib_CollectionMarkers.collect bag_marker_operations
      {propagate_bindings = false, visit_prefix = true}

  fun is_marked_bag_term tm = mem_aconv tm (!current_bag_terms)

  fun collect_query_collection_markers roots =
    let
      val sets = List.foldl (fn (term, acc) =>
        collect_native_set_terms term acc) [] roots
      val bags = List.foldl (fn (term, acc) =>
        collect_native_bag_terms term acc) [] roots
    in {sets = sets, bags = bags} end

  datatype 'term backend_view =
      BackendVariable | BackendConstant
    | BackendApplication of 'term * 'term
    | BackendAbstraction of 'term * 'term
  type 'term backend_selection_operations =
    {view:'term -> 'term backend_view,type_of:'term -> Type.hol_type,
     strip_comb:'term -> 'term * 'term list,
     same:'term * 'term -> bool,shadow_same:'term * 'term -> bool,
     free_variables:'term -> 'term list,
     same_const:'term -> Term.term -> bool,
     is_empty_set:'term -> bool,is_univ_set:'term -> bool,
     is_empty_bag:'term -> bool,is_parsed_bag_literal:'term -> bool,
     set_element_type:'term -> Type.hol_type,
     bag_element_type:'term -> Type.hol_type,
     memoize:string -> 'term list list -> 'term ->
       (unit -> bool) -> bool}

  datatype finite_family = FiniteSet | FiniteBag
  datatype 'term finite_branch =
      Domain of Type.hol_type
    | Evidence of {saved:'term,index:IntInf.int}
    | Empty
    | UniverseDomain of Type.hol_type
    | Insert of 'term * 'term
    | Delete of 'term * 'term
    | Union of 'term * 'term
    | InterLeft of 'term * 'term
    | InterRight of 'term * 'term
    | Difference of 'term * 'term
    | Merge of 'term * 'term
    | ComplementDomain of {operand:'term,element_type:Type.hol_type}
    | ParsedLiteral
  type 'term finite_report =
    {family:finite_family,evidence:'term list,subject:'term,
     branch:'term finite_branch}

  (* One registry and one decision programme serve native and graph syntax.
     shadow_same is restricted to the old lexical evidence-shadow check;
     all actual finite-evidence membership uses the carrier's own equality.
     Memo contexts include every evidence list and lexical bound stack. *)
  fun backend_selection_with_finite_trace
      (operations:'term backend_selection_operations)
      (report:'term finite_report -> unit) =
    let
      val {view,type_of,strip_comb,same,shadow_same,free_variables,
           same_const,is_empty_set,is_univ_set,is_empty_bag,
           is_parsed_bag_literal,set_element_type,bag_element_type,
           memoize} = operations
      fun member equal current =
        List.exists (fn saved => equal (current,saved))
      fun first_evidence current evidence =
        let fun seek _ [] = NONE
              | seek index (saved::rest) =
                  if same (current,saved) then SOME {saved=saved,index=index}
                  else seek (index+1) rest
        in seek (0:IntInf.int) evidence end
      fun accepted family evidence subject branch =
        (report {family=family,evidence=evidence,subject=subject,
          branch=branch};true)
      fun dest head count current =
        let fun peel 0 current arguments =
                  if same_const current head then SOME arguments else NONE
              | peel count current arguments = case view current of
                  BackendApplication (function,argument) =>
                    peel (count-1) function (argument::arguments)
                | _ => NONE
        in peel count current [] end
      fun unary head current = case dest head 1 current of
          SOME [argument] => SOME argument | _ => NONE
      fun binary head current = case dest head 2 current of
          SOME [left,right] => SOME (left,right) | _ => NONE
      fun is_variable current = case view current of
          BackendVariable => true | _ => false
      fun native_set current = memoize "native-set" [] current (fn () =>
        is_variable current orelse is_empty_set current orelse
        is_univ_set current orelse
        (case binary pred_setSyntax.insert_tm current of
           SOME (_,set) => native_set set
         | NONE => (case binary pred_setSyntax.delete_tm current of
             SOME (set,_) => native_set set
           | NONE => (case binary pred_setSyntax.union_tm current of
               SOME (left,right) => native_set left andalso native_set right
             | NONE => (case binary pred_setSyntax.inter_tm current of
                 SOME (left,right) => native_set left andalso native_set right
               | NONE => (case binary pred_setSyntax.diff_tm current of
                   SOME (left,right) =>
                     native_set left andalso native_set right
                 | NONE => (case unary pred_setSyntax.compl_tm current of
                     SOME set => native_set set | NONE => false)))))))
      fun finite_set evidence current =
        memoize "finite-set" [evidence] current (fn () =>
          let
            val accept = accepted FiniteSet evidence current
            fun domain reason =
              let val ty = set_element_type current
              in finite_element_type ty andalso accept (reason ty) end
          in
            domain Domain orelse
            (case first_evidence current evidence of
               SOME found => accept (Evidence found) | NONE => false) orelse
            (is_empty_set current andalso accept Empty) orelse
            (is_univ_set current andalso domain UniverseDomain) orelse
            (case binary pred_setSyntax.insert_tm current of
               SOME (element,set) => finite_set evidence set andalso
                 accept (Insert (element,set))
             | NONE => (case binary pred_setSyntax.delete_tm current of
                 SOME (set,element) => finite_set evidence set andalso
                   accept (Delete (set,element))
               | NONE => (case binary pred_setSyntax.union_tm current of
                   SOME (left,right) => finite_set evidence left andalso
                     finite_set evidence right andalso
                     accept (Union (left,right))
                 | NONE => (case binary pred_setSyntax.inter_tm current of
                     SOME (left,right) =>
                       if finite_set evidence left then
                         accept (InterLeft (left,right))
                       else finite_set evidence right andalso
                         accept (InterRight (left,right))
                   | NONE => (case binary pred_setSyntax.diff_tm current of
                       SOME (left,right) => finite_set evidence left andalso
                         accept (Difference (left,right))
                     | NONE => (case unary pred_setSyntax.compl_tm current of
                         SOME operand => domain (fn ty => ComplementDomain
                           {operand=operand,element_type=ty})
                       | NONE => false))))))
          end)
      fun native_bag current = memoize "native-bag" [] current (fn () =>
        is_variable current orelse is_empty_bag current orelse
        is_parsed_bag_literal current orelse
        (case binary bagSyntax.BAG_INSERT_tm current of
           SOME (_,bag) => native_bag bag
         | NONE => (case binary bagSyntax.BAG_UNION_tm current of
             SOME (left,right) => native_bag left andalso native_bag right
           | NONE => (case binary bagSyntax.BAG_DIFF_tm current of
               SOME (left,right) => native_bag left andalso native_bag right
             | NONE => (case binary bag_merge_tm current of
                 SOME (left,right) => native_bag left andalso native_bag right
               | NONE => (case binary bag_inter_tm current of
                   SOME (left,right) =>
                     native_bag left andalso native_bag right
                 | NONE => false))))))
      fun finite_bag evidence current =
        memoize "finite-bag" [evidence] current (fn () =>
          let
            val accept = accepted FiniteBag evidence current
            fun domain () =
              let val ty = bag_element_type current
              in finite_element_type ty andalso accept (Domain ty) end
          in
            (case first_evidence current evidence of
               SOME found => accept (Evidence found) | NONE => false) orelse
            (is_empty_bag current andalso accept Empty) orelse
            (is_parsed_bag_literal current andalso accept ParsedLiteral) orelse
            domain () orelse
            (case binary bagSyntax.BAG_INSERT_tm current of
               SOME (element,bag) => finite_bag evidence bag andalso
                 accept (Insert (element,bag))
             | NONE => (case binary bagSyntax.BAG_UNION_tm current of
                 SOME (left,right) => finite_bag evidence left andalso
                   finite_bag evidence right andalso
                   accept (Union (left,right))
               | NONE => (case binary bagSyntax.BAG_DIFF_tm current of
                   SOME (left,right) => finite_bag evidence left andalso
                     accept (Difference (left,right))
                 | NONE =>
                     let val (head,arguments) = strip_comb current in
                       if same_const head bag_merge_tm then
                         (case arguments of [left,right] =>
                            finite_bag evidence left andalso
                            finite_bag evidence right andalso
                            accept (Merge (left,right)) | _ => false)
                       else if same_const head bag_inter_tm then
                         (case arguments of [left,right] =>
                            if finite_bag evidence left then
                              accept (InterLeft (left,right))
                            else finite_bag evidence right andalso
                              accept (InterRight (left,right)) | _ => false)
                       else false end)))
          end)
      fun shadowed tag is_collection native evidence roots =
        let
          fun uses_bound bound item = List.exists (fn free =>
            List.exists (fn variable => shadow_same (free,variable)) bound)
            (free_variables item)
          fun visit bound current =
            memoize tag [evidence,bound] current (fn () =>
              (is_collection (type_of current) andalso native current andalso
               List.exists (fn item => member shadow_same current evidence
                 andalso uses_bound bound item) evidence) orelse
              (case view current of
                 BackendAbstraction (binder,body) => visit (binder::bound) body
               | BackendApplication (left,right) =>
                   visit bound left orelse visit bound right
               | _ => false))
        in List.exists (visit []) roots end
      (* Only native type metadata enters these totalized type helpers. *)
      fun nested_type is_collection ty =
        let
          fun contains ty = is_collection ty orelse
            (List.exists contains (#2 (Type.dest_type ty))
             handle Feedback.HOL_ERR _ => false)
        in
          ((contains (listSyntax.dest_list_type ty)
            handle Feedback.HOL_ERR _ => false) orelse
           (case TypeBase.fetch ty of
              SOME info => List.exists (fn constructor =>
                List.exists contains
                  (#1 (boolSyntax.strip_fun (Term.type_of constructor))))
                (TypeBasePure.constructors_of info)
            | NONE => false)) handle Feedback.HOL_ERR _ => false
        end
      fun nested_container tag is_collection roots =
        let fun visit current = memoize tag [] current (fn () =>
              nested_type is_collection (type_of current) orelse
              (case view current of
                 BackendApplication (left,right) =>
                   visit left orelse visit right
               | BackendAbstraction (_,body) => visit body | _ => false))
        in List.exists visit roots end
      fun finite_sets assumptions =
        List.mapPartial (unary pred_setSyntax.finite_tm) assumptions
      fun finite_bags assumptions =
        List.mapPartial (unary finite_bag_tm) assumptions
      fun native_sets (assumptions,goal) sets =
        let val evidence = finite_sets assumptions
            val roots = assumptions @ [goal]
        in not (null sets) andalso
          not (nested_container "nested-set" is_set_hol_type roots) andalso
          not (List.exists
            (Option.isSome o unary pred_setSyntax.compl_tm) sets)
          andalso not (shadowed "shadow-set" is_set_hol_type native_set
            evidence roots) andalso
          not (List.exists
            (pred_setSyntax.is_set_type o set_element_type) sets)
          andalso List.all (fn set => native_set set andalso
            finite_set evidence set) sets end
      fun native_bags (assumptions,goal) bags =
        let val evidence = finite_bags assumptions
            val roots = assumptions @ [goal]
        in not (null bags) andalso
          not (nested_container "nested-bag" bagSyntax.is_bag_ty roots) andalso
          not (shadowed "shadow-bag" bagSyntax.is_bag_ty native_bag
            evidence roots) andalso
          not (List.exists
            (bagSyntax.is_bag_ty o bag_element_type) bags) andalso
          List.all (fn bag => native_bag bag andalso
            finite_bag evidence bag) bags end
      fun nested_collections sets bags =
        List.exists (fn set => let val ty = set_element_type set in
          is_set_hol_type ty orelse bagSyntax.is_bag_ty ty end) sets orelse
        List.exists (fn bag => let val ty = bag_element_type bag in
          is_set_hol_type ty orelse bagSyntax.is_bag_ty ty end) bags
      fun contains tag head current = memoize tag [] current (fn () =>
        Option.isSome (unary head current) orelse
        (case view current of
           BackendApplication (left,right) =>
             contains tag head left orelse contains tag head right
         | BackendAbstraction (_,body) => contains tag head body | _ => false))
      fun select (target:{solver:string,version:string option} option)
          {goal,sets,bags,computed_set,computed_bag,bound_set,bound_bag,
           mixed_set,mixed_bag} =
        let
          val cvc5 = case target of
              SOME {solver="cvc5",...} => true | _ => false
          val _ = if cvc5 andalso (bound_set () orelse bound_bag ()) then
              raise ERR "goal_to_SmtLib_aux_inner"
                "higher-order cvc5 functions over Sets or Bags are unsupported"
            else ()
          val initial_set = if cvc5 then
              (if native_sets goal sets then CVC5NativeSet else CVC5ArraySet)
            else Z3Set
          val initial_bag = if cvc5 then
              (if native_bags goal bags then CVC5NativeBag else CVC5ArrayBag)
            else Z3ArrayBag
          val (set,bag) = if cvc5 then
              if nested_collections sets bags then (CVC5ArraySet,CVC5ArrayBag)
              else (if computed_set then CVC5ArraySet else initial_set,
                    if computed_bag then CVC5ArrayBag else initial_bag)
            else (initial_set,initial_bag)
          val _ = if cvc5 andalso
              ((set <> CVC5ArraySet andalso mixed_set ()) orelse
               (bag = CVC5NativeBag andalso mixed_bag ())) then
              raise ERR "goal_to_SmtLib_aux_inner"
                "native collection passed to an ambiguously typed HOL function"
            else ()
          val roots = #2 goal :: #1 goal
          val _ = if cvc5 then
              if set = CVC5ArraySet andalso
                  List.exists
                    (contains "set-card" pred_setSyntax.card_tm) roots
              then raise ERR "goal_to_SmtLib_aux_inner"
                "set.card requires a finiteness-entailing cvc5 goal"
              else if bag = CVC5ArrayBag andalso
                  List.exists (contains "bag-card" bagSyntax.BAG_CARD_tm) roots
              then raise ERR "goal_to_SmtLib_aux_inner"
                "bag.card requires a finiteness-entailing cvc5 goal"
              else ()
            else ()
        in {set_backend=set,bag_backend=bag} end
    in
      {select=select,native_set_term=native_set,cvc5_native_bags=native_bags,
       finite_sets=finite_sets,finite_bags=finite_bags,
       finite_set_term=finite_set,finite_bag_term=finite_bag}
    end

  (* Reports describe successful finite branches only, inside the existing
     memo thunk, after all selected child decisions. They are syntax DATA,
     not checked finiteness facts or permission to erase a hypothesis. A
     traced caller must keep its report cache and bool memo in the SAME
     fresh lifetime: a prior bool hit does not repeat its report callback. *)
  fun backend_selection_with operations =
    backend_selection_with_finite_trace operations (fn _ => ())

  val term_backend_selection_operations :
      Term.term backend_selection_operations =
    {view=fn current => case Term.dest_term current of
         Term.VAR _ => BackendVariable | Term.CONST _ => BackendConstant
       | Term.COMB pair => BackendApplication pair
       | Term.LAMB pair => BackendAbstraction pair,
     type_of=Term.type_of,strip_comb=boolSyntax.strip_comb,
     same=fn (left,right) => Term.aconv left right,
     shadow_same=fn (left,right) => Term.aconv left right,
     free_variables=Term.free_vars,same_const=same_const,
     is_empty_set=pred_setSyntax.is_empty,is_univ_set=pred_setSyntax.is_univ,
     is_empty_bag=bagSyntax.is_empty,
     is_parsed_bag_literal=is_parsed_bag_literal,
     set_element_type=set_element_type,bag_element_type=bag_element_type,
     memoize=fn _ => fn _ => fn _ => fn compute => compute ()}
  val term_backend_selection =
    backend_selection_with term_backend_selection_operations
  val native_set_term = #native_set_term term_backend_selection
  val cvc5_native_bags = #cvc5_native_bags term_backend_selection
  val finite_set_term = #finite_set_term term_backend_selection
  val finite_bag_term = #finite_bag_term term_backend_selection
  fun finite_set_hypothesis current =
    case (#finite_sets term_backend_selection) [current] of
      [term] => SOME term | _ => NONE
  fun finite_bag_hypothesis current =
    case (#finite_bags term_backend_selection) [current] of
      [term] => SOME term | _ => NONE

  (* The shared first-order Seq surface is represented directly by stock list
     terms.  MAP and FOLDL below are the Z3-only higher-order extension. *)
  fun list_const name = Term.prim_mk_const {Thy = "list", Name = name}
  fun rich_list_const name =
    Term.prim_mk_const {Thy = "rich_list", Name = name}
  fun holsmt_const name = Term.prim_mk_const {Thy = "HolSmt", Name = name}

  val seq_append_tm = list_const "APPEND"
  val seq_length_tm = list_const "LENGTH"
  val seq_cons_tm = list_const "CONS"
  val seq_reverse_tm = list_const "REVERSE"
  val seq_prefix_tm = list_const "isPREFIX"
  val seq_lupdate_tm = list_const "LUPDATE"
  val seq_map_tm = list_const "MAP"
  val seq_foldl_tm = list_const "FOLDL"
  val seq_contains_tm = rich_list_const "IS_SUBLIST"
  val seq_suffix_tm = rich_list_const "IS_SUFFIX"
  val smt_seq_nth_tm = holsmt_const "smt_seq_nth"
  val smt_seq_extract_tm = holsmt_const "smt_seq_extract"
  val smt_seq_at_tm = holsmt_const "smt_seq_at"
  val smt_seq_indexof_tm = holsmt_const "smt_seq_indexof"
  val smt_seq_replace_tm = holsmt_const "smt_seq_replace"
  val smt_seq_replace_all_tm = holsmt_const "smt_seq_replace_all"
  val smt_seq_update_tm = holsmt_const "smt_seq_update"
  val smtstr_update_tm = smtstring_const "smtstr_update"
  val smtstr_rev_tm = smtstring_const "smtstr_rev"
  val z3_seq_nth_i_tm =
    Term.prim_mk_const {Thy = "smtstringz3", Name = "seq_nth_i"}
  val int_of_num_tm = Term.prim_mk_const {Thy="integer", Name="int_of_num"}

  (* One grammar serves the ordinary emitter and authenticated graph
     carriers. Primitive syntax callbacks retain the Term adapter's exact
     destructor/constructor diagnostics. Only optional_error classifies a
     failed shape probe: graph ownership/native failures must escape. *)
  type 'term collection_recognition_operations =
    {type_of : 'term -> Type.hol_type,
     same_const : 'term -> Term.term -> bool,
     is_native_set_head : 'term -> bool,
     same : 'term -> 'term -> bool,
     strip_comb : 'term -> 'term * 'term list,
     dest_comb : 'term -> 'term * 'term,
     dest_cond : 'term -> 'term * 'term * 'term,
     dest_take : 'term -> 'term * 'term,
     dest_drop : 'term -> 'term * 'term,
     dest_Num : 'term -> 'term,
     dest_cons : 'term -> 'term * 'term,
     dest_el : 'term -> 'term * 'term,
     is_nil : 'term -> bool,
     dest_nil : 'term -> Type.hol_type,
     sequence_element_type : 'term -> Type.hol_type,
     int_less : 'term * 'term -> 'term,
     int_leq : 'term * 'term -> 'term,
     num_leq : 'term * 'term -> 'term,
     length : 'term -> 'term,
     disjunction : 'term * 'term -> 'term,
     disjunctions : 'term list -> 'term,
     int_zero : unit -> 'term,
     mk_comb : 'term * 'term -> 'term,
     list_mk_comb : 'term * 'term list -> 'term,
     set_card : 'term -> bool,
     bag_card : 'term -> bool,
     optional_error : exn -> bool,
     syntax_error : string -> string -> exn}

  type 'term collection_recognizers =
    {string_nth_shape : 'term -> 'term * 'term,
     seq_extract_shape : 'term -> 'term * 'term * 'term,
     seq_at_shape : 'term -> 'term * 'term,
     sequence_symbol : 'term -> 'term -> 'term list -> bool,
     set_symbol : 'term -> 'term list -> bool,
     bag_symbol : 'term -> 'term list -> bool,
     bag_count_application : 'term -> 'term list -> ('term * 'term) option}

  fun collection_recognizers_with
      (operations : 'term collection_recognition_operations)
      {sequence_emission,is_raw_number} : 'term collection_recognizers =
    let
      val {type_of,same_const,is_native_set_head,same,strip_comb,dest_comb,
           dest_cond,dest_take,dest_drop,dest_Num,dest_cons,dest_el,is_nil,
           dest_nil,sequence_element_type,int_less,int_leq,num_leq,length,
           disjunction,disjunctions,int_zero,mk_comb,list_mk_comb,set_card,
           bag_card,optional_error,syntax_error} = operations
      fun optional function current = SOME (function current)
        handle primary => if optional_error primary then NONE
          else raise primary
      (* The parser represents String [seq.nth] with an explicit negative-index
         branch, since its out-of-range value is unspecified.  Recover the
         original surface operation before re-emission: translating the ARB
         branch separately loses sharing between repeated accesses. *)
      fun dest_string_nth_shape tm =
        let
          val (negative, _, in_range) = dest_cond tm
          val (nth, index_num) = dest_comb in_range
          val (head, string) = dest_comb nth
          val index = dest_Num index_num
          val _ =
            if same_const head z3_seq_nth_i_tm andalso
               same negative
                 (int_less (index, (int_zero ()))) then ()
            else raise syntax_error "dest_string_nth_shape"
              "not a String seq.nth"
        in
          (string, index)
        end

      fun dest_seq_extract_shape tm =
        let
          val (invalid, empty, body) = dest_cond tm
          val (count, drop) = dest_take body
          val (start, sequence) = dest_drop drop
          val index = dest_Num start
          val size = dest_Num count
          val expected_invalid = disjunctions [
            int_less (index, (int_zero ())),
            int_leq (size, (int_zero ())),
            num_leq (length sequence, start)]
          val _ =
            if is_nil empty andalso
               Type.compare (dest_nil empty,
                 sequence_element_type sequence) = EQUAL andalso
               same invalid expected_invalid then ()
            else raise syntax_error "dest_seq_extract_shape"
              "not a sequence extract"
        in
          (sequence, index, size)
        end

      fun dest_seq_at_shape tm =
        let
          val (invalid, empty, body) = dest_cond tm
          val (element, body_empty) = dest_cons body
          val (index_num, sequence) = dest_el element
          val index = dest_Num index_num
          val expected_invalid = disjunction
            (int_less (index, (int_zero ())),
             num_leq (length sequence, index_num))
          val _ =
            if is_nil empty andalso is_nil body_empty andalso
               Type.compare (dest_nil empty,
                 sequence_element_type sequence) = EQUAL andalso
               same invalid expected_invalid then ()
            else raise syntax_error "dest_seq_at_shape" "not a sequence at"
        in
          (sequence, index)
        end

        fun native_sequence_symbol tm rator rands =
          sequence_emission () andalso
          List.all (fn part =>
            not (listSyntax.is_list_type (type_of part)) orelse
            is_native_sequence_type (type_of part)) (tm :: rands) andalso
          (is_nil tm orelse
          ((same_const rator intSyntax.int_injection orelse
            same_const rator int_of_num_tm) andalso
           (case rands of
              [arg] => same_const (Lib.fst (strip_comb arg))
                seq_length_tm
            | _ => false)) orelse
          Option.isSome (optional dest_string_nth_shape tm) orelse
          Option.isSome (optional dest_seq_extract_shape tm) orelse
          Option.isSome (optional dest_seq_at_shape tm) orelse
          List.exists (fn head => same_const rator head) [
            seq_append_tm, seq_cons_tm, seq_reverse_tm,
            seq_prefix_tm, seq_lupdate_tm, seq_map_tm, seq_foldl_tm,
            seq_contains_tm, seq_suffix_tm,
            smt_seq_nth_tm,
            smt_seq_extract_tm, smt_seq_at_tm, smt_seq_indexof_tm,
            smt_seq_replace_tm, smt_seq_replace_all_tm, smt_seq_update_tm])
        fun native_set_symbol rator rands =
          same_const rator pred_setSyntax.in_tm orelse
          is_native_set_head rator orelse
          ((same_const rator intSyntax.int_injection orelse
            same_const rator int_of_num_tm) andalso
           (case rands of [arg] => set_card arg | _ => false))
        fun native_bag_count_application rator rands =
          case rands of
            [left, right, element] =>
              if same_const rator bagSyntax.BAG_INSERT_tm orelse
                 same_const rator bagSyntax.BAG_UNION_tm orelse
                 same_const rator bagSyntax.BAG_DIFF_tm orelse
                 same_const rator bag_merge_tm orelse
                 same_const rator bag_inter_tm then
                SOME (list_mk_comb (rator, [left, right]), element)
              else NONE
          | [element] =>
              if same_const rator bagSyntax.EMPTY_BAG_tm then
                SOME (rator, element)
              else NONE
          | _ => NONE
        fun native_bag_symbol rator rands =
          ((case rands of
              [_, _] => same_const rator bag_in_tm orelse
                        same_const rator bagSyntax.BAG_INSERT_tm orelse
                        same_const rator bagSyntax.BAG_UNION_tm orelse
                        same_const rator bagSyntax.BAG_DIFF_tm orelse
                        same_const rator bag_merge_tm orelse
                        same_const rator bag_inter_tm orelse
                        same_const rator bagSyntax.SUB_BAG_tm
            | [arg] =>
                (same_const rator bagSyntax.BAG_CARD_tm andalso
                 not (is_raw_number (mk_comb (rator, arg))))
            | [] => same_const rator bagSyntax.EMPTY_BAG_tm
            | _ => false) orelse
           ((same_const rator intSyntax.int_injection orelse
             same_const rator int_of_num_tm) andalso
            (case rands of
               [arg] =>
                 bag_card arg orelse
                 Option.isSome
                   (native_bag_count_application (Lib.fst (strip_comb arg))
                     (Lib.snd (strip_comb arg)))
             | _ => false)))
    in
      {string_nth_shape=dest_string_nth_shape,
       seq_extract_shape=dest_seq_extract_shape,seq_at_shape=dest_seq_at_shape,
       sequence_symbol=native_sequence_symbol,set_symbol=native_set_symbol,
       bag_symbol=native_bag_symbol,
       bag_count_application=native_bag_count_application}
    end

  val term_collection_recognition_operations :
      Term.term collection_recognition_operations =
    {type_of=Term.type_of,same_const=same_const,
     is_native_set_head=is_native_set_head,same=Term.aconv,
     strip_comb=boolSyntax.strip_comb,dest_comb=Term.dest_comb,
     dest_cond=boolSyntax.dest_cond,dest_take=listSyntax.dest_take,
     dest_drop=listSyntax.dest_drop,dest_Num=intSyntax.dest_Num,
     dest_cons=listSyntax.dest_cons,dest_el=listSyntax.dest_el,
     is_nil=listSyntax.is_nil,dest_nil=listSyntax.dest_nil,
     sequence_element_type=sequence_element_type,
     int_less=intSyntax.mk_less,int_leq=intSyntax.mk_leq,
     num_leq=numSyntax.mk_leq,length=listSyntax.mk_length,
     disjunction=boolSyntax.mk_disj,disjunctions=boolSyntax.list_mk_disj,
     int_zero=fn () => intSyntax.zero_tm,mk_comb=Term.mk_comb,
     list_mk_comb=Term.list_mk_comb,
     set_card=pred_setSyntax.is_card,bag_card=bagSyntax.is_card,
     optional_error=fn Portable.Interrupt => false | _ => true,
     syntax_error=ERR}
  val term_collection_recognizers = collection_recognizers_with
    term_collection_recognition_operations
    {sequence_emission=fn () => !current_native_sequence_emission,
     is_raw_number=fn current => mem_aconv current (!current_raw_num_terms)}
  val dest_string_nth_shape = #string_nth_shape term_collection_recognizers
  val dest_seq_extract_shape = #seq_extract_shape term_collection_recognizers
  val dest_seq_at_shape = #seq_at_shape term_collection_recognizers

  datatype 'term native_candidate =
      NativeSequence of 'term * 'term list
    | NativeSet of 'term * 'term list
    | NativeBag of 'term * 'term list
    | NativeBuiltin of 'term * 'term list
    | NativeEquality of 'term * 'term list
    | NativeBagCount of 'term * 'term

  type 'term native_dispatch_operations =
    {same_const : 'term -> Term.term -> bool,
     is_constant : 'term -> bool,declared_arity : 'term -> int,
     type_of : 'term -> Type.hol_type,is_raw_number : 'term -> bool,
     syntax_error : string -> string -> exn}

  (* Selection does not emit or recursively translate operands. Keep whole
     and decomposed attempts separate: a failed whole literal attempt must
     finish before the application recognizers or ranked checks execute.
     The caller supplies its already computed base-type observation. *)
  fun native_dispatch_with
      (operations : 'term native_dispatch_operations)
      (recognizers : 'term collection_recognizers) regime =
    let
      val {same_const,is_constant,declared_arity,type_of,is_raw_number,
           syntax_error} = operations
      val {sequence_symbol,set_symbol,bag_symbol,bag_count_application,...} =
        recognizers
      fun ordinary current head arguments =
        if sequence_symbol current head arguments then
          NativeSequence (head,arguments)
        else if set_symbol head arguments then NativeSet (head,arguments)
        else if bag_symbol head arguments then NativeBag (head,arguments)
        else NativeBuiltin (head,arguments)
      fun whole_candidate base_type current =
        if base_type then ordinary current current []
        else raise syntax_error "translate_term" "not first-order"
      fun application_candidate base_type current head arguments =
        case bag_count_application head arguments of
          SOME operands => NativeBagCount operands
        | NONE =>
            if same_const head boolSyntax.equality then
              NativeEquality (head,arguments)
            else if sequence_symbol current head arguments orelse
                set_symbol head arguments orelse
                bag_symbol head arguments orelse
                (case regime of FirstOrder => base_type
                 | HigherOrder _ => is_constant head andalso
                     List.length arguments = declared_arity head)
            then ordinary current head arguments
            else raise syntax_error "translate_term" "not first-order"
      fun guard_builtin current head =
        if same_const head intSyntax.Num_tm andalso is_raw_number current then
          raise syntax_error "builtin_symbol"
            "Num retains its opaque result sort"
        else ()
      fun equality_operands head arguments =
        if same_const head boolSyntax.equality then
          case arguments of [left,right] =>
            if Type.compare (type_of left,reglan_ty) = EQUAL then
              raise syntax_error "builtin_equality"
                ("HOL equality on smtstring$reglan is intensional; " ^
                 "SMT-LIB RegLan equality is language equivalence")
            else (left,right)
          | _ => raise syntax_error "builtin_equality" "wrong equality arity"
        else raise syntax_error "builtin_equality" "not equality"
    in
      {whole_candidate=whole_candidate,
       application_candidate=application_candidate,
       guard_builtin=guard_builtin,equality_operands=equality_operands}
    end

  type 'term sequence_eligibility_operations = {
    constant_name : 'term -> (string * string) option,
    type_of : 'term -> Type.hol_type,
    is_extract : 'term -> bool,
    is_at : 'term -> bool,
    is_word_num : 'term -> bool
  }

  fun sequence_eligibility_with
      (operations : 'term sequence_eligibility_operations) =
    let
      val {constant_name, type_of, is_extract, is_at, is_word_num} = operations
      fun totalized tm = is_extract tm orelse is_at tm
      fun named theory names tm =
        case constant_name tm of
          SOME (thy, name) =>
            thy = theory andalso List.exists (fn expected =>
              expected = name) names
        | NONE => false
      val direct_list_heads =
        ["APPEND", "LENGTH", "CONS", "NIL", "REVERSE", "isPREFIX",
         "LUPDATE", "MAP", "FOLDL"]
      val totalized_list_heads = ["TAKE", "DROP", "EL"]
      val rich_list_heads = ["IS_SUBLIST", "IS_SUFFIX"]
      val holsmt_heads =
        ["smt_seq_nth", "smt_seq_extract", "smt_seq_at", "smt_seq_indexof",
         "smt_seq_replace", "smt_seq_replace_all", "smt_seq_update"]
      fun supported is_totalized_part tm =
        case constant_name tm of
          SOME ("list", _) =>
            named "list" direct_list_heads tm orelse
            (named "list" totalized_list_heads tm andalso
             is_totalized_part tm)
        | SOME ("rich_list", _) =>
            named "rich_list" rich_list_heads tm
        | _ => true
      fun native_part tm =
        not (listSyntax.is_list_type (type_of tm)) orelse
        is_native_sequence_type (type_of tm)
      fun selects_seq {native_parts, is_totalized_whole} tm =
        ((named "list" direct_list_heads tm orelse
          named "rich_list" rich_list_heads tm orelse
          named "HolSmt" holsmt_heads tm) andalso native_parts tm) orelse
        is_totalized_whole tm
    in
      {totalized=totalized, supported=supported, native_part=native_part,
       selects_seq=selects_seq, is_word_num=is_word_num}
    end

  val term_sequence_eligibility = sequence_eligibility_with {
    constant_name = fn tm =>
      case Lib.total Term.dest_thy_const tm of
        SOME {Thy, Name, ...} => SOME (Thy, Name)
      | NONE => NONE,
    type_of = Term.type_of,
    is_extract = fn tm => Option.isSome (Lib.total dest_seq_extract_shape tm),
    is_at = fn tm => Option.isSome (Lib.total dest_seq_at_shape tm),
    is_word_num = Lib.can wordsSyntax.dest_w2n
  }

  (* List types alone remain ordinary HOL datatypes: only a supported stock
     list operation (or one of TASK_16's exact totalized-access shapes)
     selects the Seq model.  This keeps unrelated recursive-list datatype
     goals on their existing encoding while refusing partial TAKE/DROP/EL
     terms that have no direct Seq counterpart. *)
  fun native_sequence_goal (assumptions, conclusion) =
    let
      val terms = conclusion :: assumptions
      val subterms = List.concat (List.map Library.subterms terms)
      val totalized =
        List.filter (#totalized term_sequence_eligibility) subterms
      val totalized_subterms =
        List.concat (List.map Library.subterms totalized)
      fun is_totalized_part tm =
        List.exists (fn part => Term.aconv tm part) totalized_subterms
      val supported =
        (#supported term_sequence_eligibility) is_totalized_part
      fun native_sequence_parts tm =
        List.all (#native_part term_sequence_eligibility)
          (Library.subterms tm)
      fun is_totalized_whole tm =
        List.exists (fn whole => Term.aconv tm whole) totalized
      val selects_seq = (#selects_seq term_sequence_eligibility)
        {native_parts=native_sequence_parts,
         is_totalized_whole=is_totalized_whole}
      val has_unconverted_word_num = #is_word_num term_sequence_eligibility
    in
      List.all supported subterms andalso
      not (List.exists has_unconverted_word_num subterms) andalso
      List.exists selects_seq subterms
    end

  val smt_rdiv_tm = Term.prim_mk_const {Thy="HolSmt", Name="smt_rdiv"}

  val raw_num_operations :
      Term.term SmtLib_RawNumAnalysis.operations =
    {same = fn (left, right) => Term.aconv left right,
     type_of = Term.type_of,
     is_abstraction = Term.is_abs,
     dest_abs = Term.dest_abs,
     is_combination = Term.is_comb,
     dest_comb = Term.dest_comb,
     strip_comb = boolSyntax.strip_comb,
     is_integer_coercion = fn rator =>
       same_const rator intSyntax.int_injection orelse
       same_const rator int_of_num_tm,
     is_num_head = fn rator => same_const rator intSyntax.Num_tm,
     is_bag_card_head = fn rator =>
       same_const rator bagSyntax.BAG_CARD_tm,
     number_type = numSyntax.num}
  val num_of_int_tm = Term.prim_mk_const {Thy="integer", Name="Num"}
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
    same_const str_inj_tm tm orelse is_native_string_const tm

  fun is_fp_const tm =
    if Term.is_const tm then
      let val {Thy, Name, ...} = Term.dest_thy_const tm in
        Thy = "smtfloat" andalso
        List.exists (fn name => name = Name) native_fp_names
      end
    else
      false

  val native_string_literal = #native_string_literal term_literal_recognizers

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
      floating_point, strings, sequences, sets, bags, datatypes, nonlinear,
      higher_order}) =
    String.concatWith "," (List.map Lib.fst (List.filter Lib.snd [
      ("quantifiers", quantifiers),
      ("uninterpreted", uninterpreted),
      ("arrays", arrays),
      ("bitvectors", bitvectors),
      ("integers", integers),
      ("reals", reals),
      ("floating-point", floating_point),
      ("strings", strings),
      ("sequences", sequences),
      ("sets", sets),
      ("bags", bags),
      ("datatypes", datatypes),
      ("nonlinear", nonlinear),
      ("higher-order", higher_order)
    ]))

  fun infer_logic_from_features_for_regime regime
      (features as LogicFeatures {
      quantifiers, uninterpreted, arrays, bitvectors, integers, reals,
      floating_point, strings, sequences, sets, bags, datatypes, nonlinear,
      higher_order}) =
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
      fun floating_point_logic () =
        if strings orelse datatypes orelse integers orelse nonlinear then
          "ALL"
        else if reals andalso uninterpreted then
          (* SMT-LIB has no UFFPLRA or AUFBVFPLRA packet. *)
          "ALL"
        else if arrays then
          if reals then qf ^ "ABVFPLRA"
          else if uninterpreted then qf ^ "AUFBVFP"
          else qf ^ "ABVFP"
        else if reals then
          qf ^ (if bitvectors then "BVFPLRA" else "FPLRA")
        else if uninterpreted then
          qf ^ (if bitvectors then "UFBVFP" else "UFFP")
        else
          qf ^ (if bitvectors then "BVFP" else "FP")
      val logic =
        if sequences orelse sets orelse bags then
          "ALL"
        else if floating_point then
          floating_point_logic ()
        else if strings then
          (* RegLan and dedicated smtstring symbols are classified as the
             UnicodeStrings feature, not as HOL datatypes or UFs.  Only
             genuinely orthogonal theories force the conservative fallback. *)
          if bitvectors orelse reals orelse quantifiers orelse arrays orelse
             uninterpreted orelse datatypes then
            "ALL"
          else if integers then
            if nonlinear then "QF_SNIA" else "QF_SLIA"
          else
            "QF_S"
        else if bitvectors then
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
      val curated_ho_stems = [
        "ALL", "UF", "QF_UF", "UFLIA", "QF_UFLIA",
        "UFLRA", "QF_UFLRA", "AUFLIA", "AUFLIRA", "QF_AUFLIA"
      ]
      val logic =
        case regime of
          HigherOrder Standard27 =>
            if higher_order then
              if List.exists (fn stem => stem = logic) curated_ho_stems then
                "HO_" ^ logic
              else
                "HO_ALL"
            else
              logic
        | _ => logic
      val reason =
        "deterministic feature scan: " ^
        (case features_to_string features of "" => "core" | s => s)
    in
      (logic, reason)
    end

  fun term_declaration_text regime name domain_sorts range_sort =
    case (regime, domain_sorts) of
      (HigherOrder Standard27, []) =>
        "(declare-const " ^ name ^ " " ^ range_sort ^ ")\n"
    | _ =>
        "(declare-fun " ^ name ^ " (" ^
        String.concatWith " " domain_sorts ^ ") " ^ range_sort ^ ")\n"

  val emitted_term_sorts =
    ref ([] : ((Term.term * int) * (string list * string)) list)

  fun record_emitted_term_sorts key sorts =
    emitted_term_sorts := (key, sorts) :: !emitted_term_sorts

  fun emitted_term_sorts_for (tm, arity) =
    case List.find (fn ((other_tm, other_arity), _) =>
      arity = other_arity andalso Term.aconv tm other_tm) (!emitted_term_sorts)
      of
        SOME (_, sorts) => SOME sorts
      | NONE => NONE

  type 'term term_declaration_operations = {
    type_of : 'term -> Type.hol_type,
    is_injected_string : 'term -> bool,
    is_injected_float : 'term -> bool,
    recorded_sorts : 'term * int -> (string list * string) option,
    sort_of_type : Type.hol_type -> string
  }

  (* Observe the carrier outside pure type operations. Callbacks preserve
     their primary exceptions; recorded sorts are read after type splitting,
     as on the native path, even when they override the emitted sorts. *)
  fun term_declaration_metadata_with
      (operations : 'term term_declaration_operations)
      regime ((tm, arity), name) =
    let
      fun doms_rng acc 0 ty = (List.rev acc, ty)
        | doms_rng acc n ty =
          let val (dom, rng) = Type.dom_rng ty
          in doms_rng (dom :: acc) (n - 1) rng end
      val injected_string =
        arity = 0 andalso (#is_injected_string operations) tm
      val injected_float =
        arity = 0 andalso (#is_injected_float operations) tm
      val (domtys, rngty) = doms_rng [] arity ((#type_of operations) tm)
      val (domain_sorts, range_sort) =
        case (#recorded_sorts operations) (tm, arity) of
          SOME sorts => sorts
        | NONE =>
            (List.map (#sort_of_type operations) domtys,
             if injected_string then "String"
             else if injected_float then smtfp_sort rngty
             else (#sort_of_type operations) rngty)
      val declaration =
        term_declaration_text regime name domain_sorts range_sort
    in
      {domain_sorts = domain_sorts, range_sort = range_sort,
       declaration = declaration}
    end

  fun term_declaration_operations regime tydict :
      Term.term term_declaration_operations =
    {type_of=Term.type_of,is_injected_string=is_injected_string,
     is_injected_float=is_injected_float,
     recorded_sorts=emitted_term_sorts_for,
     sort_of_type=smt_sort_of_type regime tydict}

  fun term_decl_for_tmdict regime tydict ((tm, arity), name) =
    let
      val {domain_sorts,range_sort,declaration} =
        term_declaration_metadata_with
          (term_declaration_operations regime tydict) regime
          ((tm,arity),name)
    in
      TermDeclaration {hol_term = tm, arity = arity, smt_name = name,
        domain_sorts = domain_sorts, range_sort = range_sort,
        declaration = declaration}
    end

  val smt_reserved_type_names = [
    "Bool", "Int", "Real", "String", "RoundingMode", "FloatingPoint",
    "Float16", "Float32", "Float64", "Float128", "Array", "BitVec",
    "Seq", "Set", "Bag", "RegLan"
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

  (* 'num' is transferred to SMT Int by preprocessing.  A residual HOL :string
     is a char list, but its content reaches SMT only through str_inj, so
     enumerating its list structure would burden the solver with a datatype no
     emitted symbol ever inspects; it stays an opaque sort instead. *)
  fun datatype_translation_excluded ty =
    same_type (ty, numSyntax.num) orelse
    same_type (ty, stringSyntax.string_ty) orelse
    type_is_binary_ieee_float ty

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

  val invented_uf_native_datatype_domain_diagnostic =
    "HOLSMT_TRANSLATION_INVENTED_UF_NATIVE_DATATYPE_DOMAIN"

  val uninterpreted_native_datatype_destructor_diagnostic =
    "HOLSMT_TRANSLATION_UNINTERPRETED_NATIVE_DATATYPE_DESTRUCTOR"

  val unsupported_smtfloat_constant_diagnostic =
    "HOLSMT_TRANSLATION_UNSUPPORTED_SMTFLOAT_CONSTANT"

  (* The generic symbol emitter is deliberately closed over the smtfloat
     theory.  These constants are representation or replay scaffolding, not
     additional SMT FloatingPoint operations: replay may keep them opaque
     while proving the surrounding formula.  Every name is explicit so a new
     smtfloat definition cannot silently acquire invented-UF semantics. *)
  val smtfloat_opaque_replay_constants =
    Redblackset.addList
      (Redblackset.empty String.compare,
       ["SmtFp", "smtfp_rep", "canon",
        "smtfp_circuit_sig", "smtfp_circuit_exp",
        "smtfp_circuit_round_up", "smtfp_circuit_round",
        "smtfp_circuit_infinity", "smtfp_circuit_top",
        "smtfp_circuit_overflow", "smtfp_circuit_wanted_exponent",
        "smtfp_circuit_encoded_exponent",
        "smtfp_circuit_effective_exponent", "smtfp_circuit_shift",
        "smtfp_circuit_divisor", "smtfp_circuit_quotient",
        "smtfp_circuit_remainder", "smtfp_circuit_rounded",
        "smtfp_circuit_pack", "smtfp_circuit_encode",
        "smtfp_addsub_trace", "smtfp_addsub_zero_sign",
        "smtfp_addsub_circuit",
        "smtfp_mul_trace", "smtfp_mul_sign", "smtfp_mul_product",
        "smtfp_mul_exponent_sum", "smtfp_mul_wanted_exponent",
        "smtfp_mul_encoded_exponent", "smtfp_mul_shift_right",
        "smtfp_mul_divisor", "smtfp_mul_quotient",
        "smtfp_mul_remainder", "smtfp_mul_encode",
        "smtfp_mul_circuit"])

  fun reject_unsupported_smtfloat_constant rator =
    if not (Term.is_const rator) then ()
    else
      case Lib.total Term.dest_thy_const rator of
        SOME {Thy = "smtfloat", Name, ...} =>
          if Redblackset.member (smtfloat_opaque_replay_constants, Name) then
            ()
          else
            raise ERR "translate_term"
              (unsupported_smtfloat_constant_diagnostic ^
               ": refusing to invent SMT semantics for smtfloat$" ^ Name ^
               "; constant=" ^ Hol_pp.term_to_string rator ^
               "; type=" ^ Hol_pp.type_to_string (Term.type_of rator))
      | _ => ()

  fun datatype_destructor_head theorem =
    let
      val (_, body) = boolSyntax.strip_forall (Thm.concl theorem)
      val clauses = boolSyntax.strip_conj body
      fun clause_head clause =
        let
          val (_, equation) = boolSyntax.strip_forall clause
          val (lhs, _) = boolSyntax.dest_eq equation
          val (head, arguments) = boolSyntax.strip_comb lhs
          val _ = if List.length arguments = 1 then () else
            raise ERR "datatype_destructor_head"
              "destructor equation is not unary"
        in
          head
        end
      val heads = List.map clause_head clauses
      val head = List.hd heads
      val _ = List.all (Term.same_const head) heads orelse
        raise ERR "datatype_destructor_head"
          "destructor theorem defines multiple constants"
    in
      head
    end

  (* Upstream list metadata does not register HD/TL.  Supply their proved
     laws only in our translation view; never update TypeBase, even
     temporarily.  Explicit caller registrations remain authoritative, as
     for every other datatype.  These laws guide checked case proofs, not
     semantic rewrites justified by metadata alone. *)
  val list_destructor_laws = [listTheory.HD, listTheory.TL_DEF]
  fun datatype_destructor_theorems tyinfo =
    let val registered = TypeBasePure.destructors_of tyinfo in
      if List.null registered andalso
         TypeBasePure.ty_name_of tyinfo = ("list", "list") then
        list_destructor_laws
      else registered
    end

  fun datatype_destructor_theorem_with metadata_error same_const
      tyinfo destructor =
    let
      fun metadata thunk = thunk () handle primary as Feedback.HOL_ERR _ =>
        raise metadata_error primary
    in
      List.find
        (fn theorem =>
          let val head = metadata (fn () => datatype_destructor_head theorem)
          in same_const destructor head end)
        (metadata (fn () => datatype_destructor_theorems tyinfo))
    end

  fun datatype_destructor_theorem tyinfo destructor =
    datatype_destructor_theorem_with Lib.I Term.same_const tyinfo destructor

  (* This predicate follows the actual type emitter: ordinary native lists
     are datatypes, but a selected Seq backend emits them as `(Seq ...)` and
     therefore does not create the under-specified native-datatype boundary. *)
  fun emits_native_datatype_sort ty =
    not (is_function_type ty) andalso
    not (has_type_builtin ty) andalso
    not (!current_native_sequence_emission andalso
      is_native_sequence_type ty) andalso
    Option.isSome (datatype_family ty)

  fun registered_destructor_for_domain destructor domain =
    case TypeBase.fetch domain of
      SOME tyinfo =>
        Option.isSome (datatype_destructor_theorem tyinfo destructor)
    | NONE => false

  fun emitted_native_sort ty =
    emits_native_datatype_sort ty orelse
    (!current_native_sequence_emission andalso is_native_sequence_type ty)

  (* The domain policy observes only types and genuine atomic declarations.
     Query authentication and diagnostic formatting stay outside the pure
     metadata exception boundary. The caller supplies its existing shape
     error policy; this factory grants no Source or equality permission. *)
  type 'term native_datatype_policy_operations =
    {constant_leaf : 'term -> Term.term option,
     term_to_string : 'term -> string,
     syntax_error : string -> string -> exn,metadata_error : exn -> exn}

  type 'term native_datatype_policy =
    {destructor_domain : 'term -> Type.hol_type list -> Type.hol_type option,
     raise_destructor : 'term -> Type.hol_type -> unit,
     reject_invented : 'term -> Type.hol_type list -> unit}

  fun native_datatype_policy_with
      (operations : 'term native_datatype_policy_operations)
      : 'term native_datatype_policy =
    let
      fun metadata thunk = thunk () handle primary as Feedback.HOL_ERR _ =>
        raise (#metadata_error operations) primary
      fun destructor_domain rator domain_types =
        case (#constant_leaf operations) rator of
          SOME atom => metadata (fn () =>
            List.find (fn domain => emitted_native_sort domain andalso
              registered_destructor_for_domain atom domain) domain_types)
        | NONE => NONE
      fun raise_destructor rator domain =
        raise (#syntax_error operations) "translate_term"
          (uninterpreted_native_datatype_destructor_diagnostic ^
           ": refusing an uninterpreted TypeBase destructor over a native " ^
           "sort; destructor=" ^ (#term_to_string operations) rator ^
           "; domain=" ^ Hol_pp.type_to_string domain)
      fun reject_invented rator domain_types =
        let val domain = destructor_domain rator domain_types in
          case domain of
            SOME domain => raise_destructor rator domain
          | NONE =>
              (case metadata (fn () =>
                  List.find emits_native_datatype_sort domain_types) of
                NONE => ()
              | SOME domain =>
                  raise (#syntax_error operations) "translate_term"
                    (invented_uf_native_datatype_domain_diagnostic ^
                     ": refusing an invented function whose domain was " ^
                     "emitted as a native datatype sort; the query is " ^
                     "under-specified and its sat/unknown verdict is not " ^
                     "a countermodel; function=" ^
                     (#term_to_string operations) rator ^ "; domain=" ^
                     Hol_pp.type_to_string domain))
        end
    in
      {destructor_domain=destructor_domain,raise_destructor=raise_destructor,
       reject_invented=reject_invented}
    end

  val term_native_datatype_policy_operations :
      Term.term native_datatype_policy_operations =
    {constant_leaf=fn rator =>
       if Term.is_const rator then SOME rator else NONE,
     term_to_string=Hol_pp.term_to_string,
     syntax_error=ERR,metadata_error=Lib.I}
  val term_native_datatype_policy =
    native_datatype_policy_with term_native_datatype_policy_operations
  val uninterpreted_native_destructor_domain =
    #destructor_domain term_native_datatype_policy
  val raise_uninterpreted_native_destructor =
    #raise_destructor term_native_datatype_policy
  val reject_invented_native_datatype_domain =
    #reject_invented term_native_datatype_policy

  fun theorem_reduces_exact_application theorem tm =
    let
      val reduction = simpLib.SIMP_CONV pureSimps.pure_ss [theorem] tm
      val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl reduction)
      val _ = Term.aconv lhs tm orelse
        raise ERR "closed_constructor_destructor_residual"
          "registered destructor proof has the wrong left-hand side"
    in
      not (Term.aconv lhs rhs)
    end
    handle Conv.UNCHANGED => false

  (* A partial destructor on a closed constructor outside its owning branch
     is a fixed but unspecified HOL value.  It can soundly be represented by
     one zero-arity SMT constant keyed by the whole application: unlike an
     uninterpreted destructor function, that declaration has no native-sort
     domain.  Admission is theorem-sensitive: a registered equation which can
     reduce the exact application must be used by preprocessing, never hidden
     behind this residual boundary.  Any free/symbolic scrutinee remains behind
     the hard diagnostic. *)
  type 'term carrier_residual_operations =
    {is_comb : 'term -> bool,dest_comb : 'term -> 'term * 'term,
     type_of : 'term -> Type.hol_type,
     strip_comb : 'term -> 'term * 'term list,
     same_const : 'term -> Term.term -> bool,
     constant_leaf : 'term -> Term.term option,
     free_vars : 'term -> 'term list,
     theorem_reduces_exact_application : Thm.thm -> 'term -> bool,
     metadata_error : exn -> exn}

  (* The reducer must observe the exact registered theorem's complete
     pure_ss simplification of this application. In particular, absence of
     an outer constructor rule is not evidence that descendants are normal.
     Only declaration/type observations enter the metadata error boundary;
     carrier authentication and the required reducer remain outside it. *)
  fun closed_constructor_destructor_residual_with
      (operations : 'term carrier_residual_operations) =
    let
      val {is_comb,dest_comb,type_of,strip_comb,same_const,constant_leaf,
           free_vars,theorem_reduces_exact_application,metadata_error} =
        operations
      fun metadata thunk = thunk () handle primary as Feedback.HOL_ERR _ =>
        raise metadata_error primary
      fun residual tm =
        if not (is_comb tm) then false
        else
          let
            val (destructor, scrutinee) = dest_comb tm
            val domain = type_of scrutinee
            val (constructor, _) = strip_comb scrutinee
            val registered =
              case metadata (fn () => TypeBase.fetch domain) of
                NONE => NONE
              | SOME tyinfo =>
                  Option.map (fn theorem => (tyinfo, theorem))
                    (datatype_destructor_theorem_with metadata_error
                      same_const tyinfo destructor)
          in
            case registered of
              NONE => false
            | SOME (_, theorem) =>
                metadata (fn () => emitted_native_sort domain) andalso
                (case constant_leaf constructor of
                   NONE => false
                 | SOME atom =>
                     metadata (fn () => TypeBase.is_constructor atom))
                andalso List.null (free_vars tm) andalso
                not (theorem_reduces_exact_application theorem tm)
          end
    in residual end

  val term_carrier_residual_operations :
      Term.term carrier_residual_operations =
    {is_comb=Term.is_comb,dest_comb=Term.dest_comb,type_of=Term.type_of,
     strip_comb=boolSyntax.strip_comb,same_const=Term.same_const,
     constant_leaf=fn term => if Term.is_const term then SOME term else NONE,
     free_vars=Term.free_vars,
     theorem_reduces_exact_application=theorem_reduces_exact_application,
     metadata_error=Lib.I}
  val closed_constructor_destructor_residual =
    closed_constructor_destructor_residual_with
      term_carrier_residual_operations

  fun reject_uninterpreted_native_destructors terms =
  let
    fun reject tm =
      if not (Term.is_comb tm) then ()
      else
        let val (rator, argument) = Term.dest_comb tm in
          if closed_constructor_destructor_residual tm then ()
          else
            (case uninterpreted_native_destructor_domain rator
                [Term.type_of argument] of
              SOME domain => raise_uninterpreted_native_destructor rator domain
            | NONE => ())
        end
  in
    List.app reject (List.concat (List.map Library.subterms terms))
  end


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
          val name = fresh_smt_name smt_reserved_term_names used
            ("sel_" ^ constructor_name ^ "_" ^ raw)
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

  fun datatype_decl_record regime tydict ty =
    case datatype_family ty of
      NONE => NONE
    | SOME family =>
      let
        val names = List.map (fn fam_ty => Redblackmap.find (tydict, fam_ty))
          family
        val declaration = datatype_declaration_text
          (smt_sort_of_type regime tydict) family names
      in
        SOME (DatatypeDeclaration {hol_types = family, smt_names = names,
          declaration = declaration}, family)
      end
      handle Redblackmap.NotFound => NONE
           | Feedback.HOL_ERR _ => NONE

  (* The same feature grammar serves native terms and borrowed graph DATA.
     State observations are thunks to preserve the native scan's read order.
     Graph callers supply immutable snapshots of the actual emission state. *)
  type feature_state = {
    generated_forall : unit -> bool,
    sequence_emission : unit -> bool,
    has_set_terms : unit -> bool,
    native_set_backend : unit -> bool,
    has_bag_terms : unit -> bool,
    native_bag_backend : unit -> bool
  }

  (* Graph test_constant may inspect only authenticated constant leaves.
     Memo hooks belong to one fixed query/context and cache returned bools,
     never exceptions; authenticate before hits and before publication.
     Graph shape/optional predicates must exclude native callback primaries.
     The native instance retains its original broader exception policies. *)
  type 'term feature_operations = {
    type_of : 'term -> Type.hol_type,
    is_var : 'term -> bool,
    is_comb : 'term -> bool,
    is_abs : 'term -> bool,
    dest_comb : 'term -> 'term * 'term,
    dest_abs : 'term -> 'term * 'term,
    strip_comb : 'term -> 'term * 'term list,
    is_all_distinct : 'term -> bool,
    dest_all_distinct : 'term -> 'term,
    dest_list : 'term -> 'term list * Type.hol_type,
    constant_name : 'term -> string * string,
    test_constant : (Term.term -> bool) -> 'term -> bool,
    term_same_const : 'term -> Term.term -> bool,
    is_forall : 'term -> bool,
    is_exists : 'term -> bool,
    is_update_comb : 'term -> bool,
    is_injected_string : 'term -> bool,
    is_injected_float : 'term -> bool,
    is_word_literal : 'term -> bool,
    is_shape_error : exn -> bool,
    is_optional_error : exn -> bool,
    metadata_error : exn -> exn,
    syntax_error : string -> string -> exn,
    memo_quantifier : 'term -> (unit -> bool) -> bool,
    memo_bitvector : 'term -> (unit -> bool) -> bool
  }

  fun feature_analysis_with (operations : 'term feature_operations) =
    let
      val {type_of,is_var,is_comb,is_abs,dest_comb,dest_abs,strip_comb,
           is_all_distinct,dest_all_distinct,dest_list,constant_name,
           test_constant,term_same_const,is_forall,is_exists,is_update_comb,
           is_injected_string,is_injected_float,is_word_literal,
           is_shape_error,is_optional_error,metadata_error,syntax_error,
           memo_quantifier,memo_bitvector} = operations
      fun shape thunk fallback = thunk () handle primary =>
        if is_shape_error primary then fallback () else raise primary
      fun optional observe current = SOME (observe current)
        handle primary =>
          if is_optional_error primary then NONE else raise primary
      fun metadata thunk = thunk ()
        handle primary as Feedback.HOL_ERR _ => raise metadata_error primary
      fun distinct_elements tm = dest_list (dest_all_distinct tm)
      fun encoding_subterms tm =
        let
          fun walk (tm, acc) =
            tm ::
            (if is_all_distinct tm then
               let val (elements, _) = distinct_elements tm in
                 List.foldl (fn (element, rest) => walk (element, rest))
                   acc elements
               end
             else shape
               (fn () => let val (rator, rand) = dest_comb tm
                 in walk (rator, walk (rand, acc)) end)
               (fn () => shape
                 (fn () => let val (_, body) = dest_abs tm
                   in walk (body, acc) end)
                 (fn () => acc)))
        in walk (tm, []) end
      (* The graph inventory uses this single-step form and a scoped visited
         set. ALL_DISTINCT visits current plus reversed explicit elements;
         list constructors and abstraction binder leaves are excluded. *)
      fun encoding_children tm =
        if is_all_distinct tm then List.rev (#1 (distinct_elements tm))
        else shape (fn () => let val (left,right) = dest_comb tm
            in [left,right] end)
          (fn () => shape (fn () => [#2 (dest_abs tm)]) (fn () => []))
      fun has_quantifier tm = memo_quantifier tm (fn () =>
        is_forall tm orelse is_exists tm orelse shape
          (fn () => let val (rator,rand) = dest_comb tm
            in has_quantifier rator orelse has_quantifier rand end)
          (fn () => shape (fn () => has_quantifier (#2 (dest_abs tm)))
            (fn () => false)))
      fun is_smtfp_bits_application tm = shape
        (fn () =>
          let val (head,args) = strip_comb tm
              val (theory,name) = constant_name head
          in theory = "smtfloat" andalso name = "smtfp_bits" andalso
            List.length args = 3 end)
        (fn () => false)
      (* FP constructor literal fields do not independently require BV. *)
      fun has_nonconstructor_bitvector tm = memo_bitvector tm (fn () =>
        if is_smtfp_bits_application tm then
          let val (_,fields) = strip_comb tm
          in not (List.all is_word_literal fields) end
        else if type_contains_word (type_of tm) orelse
          test_constant is_bv_const (#1 (strip_comb tm)) then true
        else if is_comb tm then
          let val (rator,rand) = dest_comb tm
          in has_nonconstructor_bitvector rator orelse
            has_nonconstructor_bitvector rand end
        else if is_abs tm then has_nonconstructor_bitvector (#2 (dest_abs tm))
        else false)
      fun infer (state : feature_state) regime all_subterms terms
          type_exists term_exists =
        let
          fun subterm_types predicate =
            List.exists (fn tm => predicate (type_of tm)) all_subterms
          val quantifiers = (#generated_forall state) () orelse
            List.exists has_quantifier terms
          val bitvectors = List.exists has_nonconstructor_bitvector terms
          val integers =
            subterm_types type_contains_int orelse
            List.exists (fn tm => (test_constant is_int_arith_const)
              (Lib.fst (strip_comb tm))) all_subterms
          val reals =
            subterm_types type_contains_real orelse
            List.exists (fn tm => (test_constant is_real_arith_const)
              (Lib.fst (strip_comb tm))) all_subterms
          val floating_point =
            subterm_types type_contains_fp orelse
            List.exists (fn tm => (test_constant is_fp_const)
              (Lib.fst (strip_comb tm))) all_subterms
          val strings =
            subterm_types type_contains_string orelse
            subterm_types
              (Library.type_contains
                (fn ty => Type.compare (ty, reglan_ty) = EQUAL)) orelse
            List.exists (fn tm => (test_constant is_string_const)
              (Lib.fst (strip_comb tm))) all_subterms
          fun thy_const_named theory names tm =
            case optional constant_name tm of
              SOME (Thy, Name) =>
                Thy = theory andalso List.exists (fn name => name = Name) names
            | NONE => false
          val sequence_names =
            ["APPEND", "LENGTH", "CONS", "NIL", "TAKE", "DROP", "EL",
             "MAP", "FOLDL", "REVERSE", "isPREFIX", "LUPDATE"]
          val rich_sequence_names = ["IS_SUBLIST", "IS_SUFFIX"]
          val holsmt_sequence_names =
            ["smt_seq_nth", "smt_seq_extract", "smt_seq_at", "smt_seq_indexof",
             "smt_seq_replace", "smt_seq_replace_all", "smt_seq_update"]
          val set_names =
            ["INSERT", "DELETE", "UNION", "INTER", "DIFF", "COMPL", "SUBSET",
             "EMPTY", "UNIV", "SING", "CARD"]
          val bag_names =
            ["BAG_IN", "BAG_INSERT", "BAG_UNION", "BAG_MERGE", "BAG_INTER",
             "BAG_DIFF", "BAG_CARD", "EMPTY_BAG", "SUB_BAG"]
          fun is_native_sequence_const tm =
            thy_const_named "list" sequence_names tm orelse
            thy_const_named "rich_list" rich_sequence_names tm orelse
            thy_const_named "HolSmt" holsmt_sequence_names tm
          fun is_native_set_const tm =
            thy_const_named "pred_set" set_names tm orelse
            thy_const_named "bool" ["IN"] tm
          fun is_native_bag_const tm = thy_const_named "bag" bag_names tm
          val sequences = (#sequence_emission state) () andalso
            (subterm_types is_native_sequence_type orelse
             List.exists (fn tm => is_native_sequence_const
               (Lib.fst (strip_comb tm))) all_subterms)
          (* Finite-set hypotheses select cvc5's native Set sort and are
             removed before this scan. Backend selection is a Set feature. *)
          val sets = (#has_set_terms state) () orelse
            (#native_set_backend state) () orelse
            List.exists (fn tm => is_native_set_const
              (Lib.fst (strip_comb tm))) all_subterms
          (* Checked preprocessing can lower native bag operations to count
             applications.  The native cvc5 backend still emits Bag sorts. *)
          val bags = (#has_bag_terms state) () orelse
            (#native_bag_backend state) () orelse
            List.exists (fn tm => is_native_bag_const
              (Lib.fst (strip_comb tm))) all_subterms
          fun term_is_native_string_surface tm =
            let val (rator, _) = strip_comb tm
            in
              (test_constant is_native_string_const) rator orelse
              type_contains_string (type_of tm) orelse
              Library.type_contains
                (fn ty => Type.compare (ty, reglan_ty) = EQUAL)
                (type_of tm)
            end
          fun type_is_datatype ty =
            not (has_type_builtin ty) andalso
            Option.isSome (datatype_family ty)
          fun type_contains_datatype ty =
            type_contains type_is_datatype ty
          val has_injected_strings =
            List.exists is_injected_string all_subterms
          fun term_contains_datatype tm =
            let
              val (rator, _) = strip_comb tm
            in
              not (term_is_native_string_surface tm) andalso
              not (strings andalso
                test_constant (same_const boolSyntax.equality) rator) andalso
              not (has_injected_strings andalso
                ((test_constant is_string_const) rator orelse
                  test_constant (Lib.can injected_string_operator) rator))
              andalso
              type_contains_datatype (type_of tm)
            end
          fun term_is_datatype_constructor tm =
            test_constant TypeBase.is_constructor tm
          fun term_is_datatype_record_selector tm =
            let
              val ty = type_of tm
              val (dom, _) = metadata (fn () => Type.dom_rng ty)
              val tyinfo =
                case metadata (fn () => TypeBase.fetch dom) of
                  SOME info => info
                | NONE => raise syntax_error "infer_features"
                    "not a datatype selector"
              val fields = metadata (fn () => TypeBasePure.fields_of tyinfo)
            in
              List.exists
                (fn (_, {accessor, ...} : TypeBasePure.rcd_fieldinfo) =>
                   term_same_const tm accessor)
                fields
            end
          fun term_is_datatype_native ((tm, arity), _) =
            (arity = 0 andalso
             type_contains_datatype (type_of tm)) orelse
            term_is_datatype_constructor tm orelse
            (case optional term_is_datatype_record_selector tm of
               SOME result => result
             | NONE => false)
          val datatypes =
            List.exists term_contains_datatype all_subterms orelse
            type_exists type_contains_datatype orelse
            term_exists (fn (tm, arity) =>
              not (is_injected_string tm) andalso
              not (is_injected_float tm) andalso
              type_contains_datatype (type_of tm))
          val nonlinear =
            List.exists (fn tm => (test_constant is_nonlinear_arith_const)
              (Lib.fst (strip_comb tm))) all_subterms
          val has_uninterpreted_type =
            type_exists (fn ty => not (type_contains_datatype ty))
          fun range_after 0 ty = ty
            | range_after n ty =
                range_after (n - 1) (Lib.snd (Type.dom_rng ty))
          fun term_needs_uf ((tm, arity), _) =
            if term_is_datatype_native ((tm, arity), "") then
              false
            else if arity = 0 andalso
                    (is_injected_string tm orelse is_injected_float tm) then
              false
            else
              arity > 0 orelse
              (arity = 0 andalso
               not (has_type_builtin (range_after arity (type_of tm))) andalso
               not (is_function_type (range_after arity (type_of tm))))
          val uninterpreted =
            has_uninterpreted_type orelse
            term_exists (fn key => term_needs_uf (key, ""))
          val higher_order =
            case regime of FirstOrder => false | HigherOrder _ => true
          val function_arrays =
            case regime of
              FirstOrder =>
                List.exists (fn tm =>
                  is_var tm andalso
                  type_contains_function (type_of tm)) all_subterms orelse
                term_exists (fn (tm, arity) => arity = 0 andalso
                  type_contains_function (type_of tm))
            | HigherOrder _ => false
          val arrays =
            function_arrays orelse
            List.exists is_update_comb all_subterms
        in
          LogicFeatures {quantifiers = quantifiers,
            uninterpreted = uninterpreted,
            arrays = arrays, bitvectors = bitvectors, integers = integers,
            reals = reals, floating_point = floating_point, strings = strings,
            sequences = sequences, sets = sets, bags = bags,
            datatypes = datatypes, nonlinear = nonlinear,
            higher_order = higher_order}
        end
    in
      {encoding_subterms=encoding_subterms,
       encoding_children=encoding_children,
       has_quantifier=has_quantifier,
       has_nonconstructor_bitvector=has_nonconstructor_bitvector,
       infer=infer}
    end

  val term_feature_operations : Term.term feature_operations =
    {type_of=Term.type_of,is_var=Term.is_var,is_comb=Term.is_comb,
     is_abs=Term.is_abs,dest_comb=Term.dest_comb,dest_abs=Term.dest_abs,
     strip_comb=boolSyntax.strip_comb,
     is_all_distinct=listSyntax.is_all_distinct,
     dest_all_distinct=listSyntax.dest_all_distinct,
     dest_list=listSyntax.dest_list,
     constant_name=fn tm =>
       let val {Thy,Name,...} = Term.dest_thy_const tm in (Thy,Name) end,
     test_constant=fn predicate => predicate,term_same_const=Term.same_const,
     is_forall=boolSyntax.is_forall,is_exists=boolSyntax.is_exists,
     is_update_comb=combinSyntax.is_update_comb,
     is_injected_string=is_injected_string,is_injected_float=is_injected_float,
     is_word_literal=wordsSyntax.is_word_literal,
     is_shape_error=fn Feedback.HOL_ERR _ => true | _ => false,
     is_optional_error=fn Portable.Interrupt => false | _ => true,
     metadata_error=fn primary => primary,syntax_error=ERR,
     memo_quantifier=fn _ => fn compute => compute (),
     memo_bitvector=fn _ => fn compute => compute ()}
  val term_feature_analysis = feature_analysis_with term_feature_operations
  val current_feature_state : feature_state =
    {generated_forall=fn () => !current_generated_forall_emissions > 0,
     sequence_emission=fn () => !current_native_sequence_emission,
     has_set_terms=fn () => not (List.null (!current_set_terms)),
     native_set_backend=fn () => !current_set_backend = CVC5NativeSet,
     has_bag_terms=fn () => not (List.null (!current_bag_terms)),
     native_bag_backend=fn () => !current_bag_backend = CVC5NativeBag}

  fun infer_features_with_state state regime terms tydict tmdict =
    let val all_subterms = List.concat (List.map
          (#encoding_subterms term_feature_analysis) terms)
    in (#infer term_feature_analysis) state regime
      all_subterms terms
      (fn predicate => Redblackmap.foldl
        (fn (ty,_,found) => found orelse predicate ty) false tydict)
      (fn predicate => Redblackmap.foldl
        (fn (key,_,found) => found orelse predicate key) false tmdict)
    end

  fun infer_features regime terms tydict tmdict =
    infer_features_with_state current_feature_state regime terms tydict tmdict

  type 'term string_presence_operations = {
    type_of : 'term -> Type.hol_type,
    head_of : 'term -> 'term,
    test_constant : (Term.term -> bool) -> 'term -> bool
  }

  (* The ordered type pass precedes every head observation. Unlike the
     feature inventory, this consumes all raw subterms, including the list
     syntax hidden by an ALL_DISTINCT encoding. No callback error is caught. *)
  fun string_presence_with
      ({type_of,head_of,test_constant} : 'term string_presence_operations)
      all_subterms =
    List.exists (fn tm => type_contains_string (type_of tm)) all_subterms
    orelse List.exists
      (fn tm => test_constant is_string_const (head_of tm)) all_subterms

  val term_string_presence_operations :
      Term.term string_presence_operations =
    {type_of=Term.type_of,head_of=Lib.fst o boolSyntax.strip_comb,
     test_constant=fn predicate => predicate}

  fun native_string_presence terms = string_presence_with
    term_string_presence_operations (List.concat (List.map subterms terms))

  (* This presence flag retains the legacy string type/operator scan,
     including str_inj and native string operators. LogicFeatures.strings
     also includes RegLan alone, so cannot replace that observation. *)
  fun advanced_encoding_records_with_presence regime {has_hol_strings}
      (LogicFeatures {sequences, sets, bags, ...}) =
    let
      val string_record =
        HOLTheoryEncoding {
          feature =
            "HOL strings: str_inj images of STRCAT, isPREFIX, string_lt, " ^
            "string_le and string equality",
          smt_theory = "UnicodeStrings",
          mode = NativeSMTLIB,
          parse = true,
          typecheck = true,
          translate = true,
          replay = false,
          notes =
            "HOL strings are rewritten through the proved str_inj transfer " ^
            "kit; injected occurrences are generalized to SMT-LIB String.  " ^
            "The HOL :string type itself is not the SMT String sort: a " ^
            "residual occurrence is emitted as an uninterpreted sort.  " ^
            "Ground native smtstr goals do replay; the oracle tactics " ^
            "cover the injected HOL-string surface.",
          proof_obligation =
            "Translation is discharged by the str_inj injectivity and " ^
            "operator-transfer theorems.  Checked replay of an injected " ^
            "HOL-string goal is not implemented: Z3 answers such goals " ^
            "with seq th-lemmas over the str_inj image, and cvc5 with the " ^
            "trust and str-substr-full-eq CPC rules, none of which the " ^
            "replay engines support."
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
          feature =
            "SMT floating point and proved binary_ieee classification, " ^
            "comparison, abs/neg, add/sub/mul/div/sqrt/fma transfer",
          smt_theory = "FloatingPoint",
          mode = NativeSMTLIB,
          parse = true,
          typecheck = true,
          translate = true,
          replay = true,
          notes =
            "The canonical-NaN smtfp carrier and its native operators are " ^
            "emitted as SMT-LIB FloatingPoint.  Native binary_ieee terms " ^
            "on the enumerated transfer surface are rewritten through " ^
            "smtfp_intro and proved homomorphism and binder theorems.  A " ^
            "residual raw float, including raw record equality, is emitted " ^
            "as an uninterpreted sort; it is never an SMT FloatingPoint sort.",
          proof_obligation =
            "The exact smtfp carrier justifies native sort equality, and " ^
            "the native_float_transfer_infos theorem list discharges the " ^
            "binary_ieee transfer.  Checked Z3 4.x and cvc5 CPC replay " ^
            "cover the native smtfp surface and transferred " ^
            "classification/comparison goals; " ^
            "over-budget bit-blasts use the reserved D12 diagnostic, while " ^
            "unsupported symbolic arithmetic uses the structured D2 rung."
        }
      val z3_ext_record =
        HOLTheoryEncoding {
          feature = "sequences, sets, and bags",
          smt_theory = "Z3 sequence/set/bag extensions",
          mode = if sets orelse bags then NativeSMTLIB
                 else ConservativeEmbedding,
          parse = true,
          typecheck = true,
          translate = true,
          replay = true,
          notes =
            if sequences andalso sets andalso bags then
              "Stock list, pred_set, and bag operations emit their native " ^
              "dialects; non-finite cvc5 goals use quantified arrays."
            else if sequences then
              "Stock list operations emit the shared first-order seq.* " ^
              "surface; seq.update and seq.rev are cvc5-only."
            else if sets andalso bags then
              "Stock pred_set and bag operations emit their native dual " ^
              "dialects; non-finite cvc5 goals use quantified arrays."
            else if sets then
              "Stock pred_set operations emit Z3 array-sets or cvc5 finite " ^
              "set.* terms; non-finite cvc5 goals use quantified arrays."
            else if bags then
              "Stock bag operations emit Z3 Int arrays with (_ map ...) or " ^
              "finite cvc5 bag.* terms; non-finite cvc5 goals use arrays."
            else
              "Z3 extension symbols are parser/typechecker entries only.",
          proof_obligation =
            "Checked Z3 replay uses SmtSeqProve for native Seq terms, " ^
            "SmtArrayProve for sets, and SmtBagProve over the array/arith " ^
            "bag encoding; cvc5 CPC replay uses the corresponding checked " ^
            "Seq/Set/Bag rules."
        }
      val regex_record =
        HOLTheoryEncoding {
          feature = "regular expressions",
          smt_theory = "UnicodeStrings RegLan",
          mode = ConservativeEmbedding,
          parse = true,
          typecheck = true,
          translate = true,
          replay = false,
          notes =
            "Native smtstring/RegLan terms use the UnicodeStrings surface; " ^
            "HOL regex libraries have no implicit RegLan injection.",
          proof_obligation =
            "A checked soundness argument must relate HOL regex languages to SMT-LIB RegLan membership and Unicode string semantics before replay support."
        }
      val (ho_mode, ho_notes) =
        case regime of
          FirstOrder =>
            (ConservativeEmbedding,
             "The FirstOrder regime conservatively embeds HOL function " ^
             "types as nested SMT-LIB Arrays, with select/store for " ^
             "application/update.")
        | HigherOrder Standard27 =>
            (NativeSMTLIB,
             "The HigherOrder Standard27 regime emits native SMT-LIB 2.7 " ^
             "HO-Core maps, lambdas, and application.")
        | HigherOrder Z3LambdaArray =>
            (NativeSMTLIB,
             "The HigherOrder Z3LambdaArray dialect lowers HO-Core maps " ^
             "to equivalent nested Arrays/select while retaining lambdas.")
      val ho_core_record =
        HOLTheoryEncoding {
          feature =
            "HOL function types, lambda abstractions, and application",
          smt_theory = "HO-Core",
          mode = ho_mode,
          parse = true,
          typecheck = true,
          translate = true,
          replay = false,
          notes = ho_notes,
          proof_obligation =
            "Checked replay must reconstruct lambda, beta/eta, partial " ^
            "application, and function-extensionality proof steps without " ^
            "oracles before replay support is claimed."
        }
    in
      (if has_hol_strings then [string_record] else []) @
      [datatype_record, fp_record] @
      (if sequences orelse sets orelse bags then [z3_ext_record] else []) @
      [regex_record, ho_core_record]
    end

  fun advanced_encoding_records regime terms features =
    let
      val has_strings = native_string_presence terms
    in
      advanced_encoding_records_with_presence regime
        {has_hol_strings = has_strings} features
    end

  (* Preserve the native dictionary fold and datatype-family suppression.
     These records contain only type/declaration metadata, never a query
     carrier or a borrowed graph closure. *)
  fun type_declaration_records regime tydict =
    let
      fun add_type_record (ty, name, (seen, acc)) =
        if member_type ty seen then
          (seen, acc)
        else
          case datatype_decl_record regime tydict ty of
            SOME (record, family) =>
              (List.foldl (fn (fam_ty, seen) => add_type fam_ty seen)
                seen family, record :: acc)
          | NONE =>
              (add_type ty seen, type_decl_record (ty, name) :: acc)
      val (_, type_records) = Redblackmap.foldl add_type_record ([], []) tydict
    in
      List.rev type_records
    end

  fun build_translation_records regime regime_reason terms logic reason
      features tydict tmdict =
    let
      val regime_record =
        RegimeSelection {regime = regime, reason = regime_reason}
      val logic_record = LogicSelection {logic = logic, reason = reason,
        features = features}
      val type_records = type_declaration_records regime tydict
      val term_records = Redblackmap.foldl (fn (key, name, acc) =>
        term_decl_for_tmdict regime tydict (key, name) :: acc)
        [] tmdict
      val builtin_records = encoded_symbol_records terms
      val advanced_records = advanced_encoding_records regime terms features
    in
      regime_record :: logic_record :: type_records @
      List.rev term_records @ List.rev builtin_records @ advanced_records
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

  datatype parser_datatype_case =
      ParserSelector of {constructor : Term.term, selector_index : int,
                         scrutinee : Term.term}
    | ParserTester of {constructor : Term.term, scrutinee : Term.term}

  fun datatype_constructors ty =
    case TypeBase.fetch ty of
      SOME tyinfo =>
        List.map (TypeBasePure.cinst ty)
          (TypeBasePure.constructors_of tyinfo)
    | NONE => raise ERR "datatype_constructors" "missing TypeBase entry"

  (* These are exactly the HOL terms installed in the parser dictionary for
     SMT datatype selectors and testers.  Recognizing them centrally makes
     them fixed points of both preprocessing and outbound translation. *)
  fun parser_datatype_case tm =
    let
      val (_, scrutinee, _) = TypeBase.dest_case tm
      val ty = Term.type_of scrutinee
      val constructors = datatype_constructors ty
      fun selector_for constructor =
        let
          val (doms, _) = boolSyntax.strip_fun (Term.type_of constructor)
          fun matches selector_index =
            Term.aconv tm
              (datatype_selector_term ty constructor selector_index
                scrutinee)
        in
          case List.find matches
              (List.tabulate (List.length doms, fn n => n)) of
            SOME selector_index =>
              SOME (ParserSelector {constructor = constructor,
                selector_index = selector_index, scrutinee = scrutinee})
          | NONE => NONE
        end
      fun tester_for constructor =
        if Term.aconv tm (datatype_tester_term ty constructor scrutinee) then
          SOME (ParserTester {constructor = constructor,
            scrutinee = scrutinee})
        else
          NONE
    in
      case Lib.get_first selector_for constructors of
        SOME result => SOME result
      | NONE => Lib.get_first tester_for constructors
    end
    handle Feedback.HOL_ERR _ => NONE

  type datatype_case_parts = {
    data_ty : Type.hol_type,
    scrutinee : Term.term,
    constructors : Term.term list,
    branches : Term.term list
  }

  (* Decompose a HOL datatype case using the same selector spelling that the
     parser assigns to SMT selector applications. *)
  fun datatype_case_parts tm : datatype_case_parts =
    let
      val (_, scrutinee, clauses) = TypeBase.dest_case tm
      val data_ty = Term.type_of scrutinee
      val constructors = datatype_constructors data_ty
      fun clause_for constructor =
        case List.find
            (fn (pattern, _) =>
              let val (head, _) = boolSyntax.strip_comb pattern
              in Term.same_const constructor head end)
            clauses of
          SOME clause => clause
        | NONE => raise ERR "datatype_case_parts" "missing case branch"
      fun branch constructor =
        let
          val (pattern, rhs) = clause_for constructor
          val (_, pattern_args) = boolSyntax.strip_comb pattern
          val (doms, _) = boolSyntax.strip_fun (Term.type_of constructor)
          val _ = if List.length pattern_args = List.length doms then ()
                  else raise ERR "datatype_case_parts"
                    "case pattern arity mismatch"
          val selectors = List.map
            (fn n => datatype_selector_term data_ty constructor n scrutinee)
            (List.tabulate (List.length doms, fn n => n))
          val subst = ListPair.mapEq
            (fn (redex, residue) => {redex = redex, residue = residue})
            (pattern_args, selectors)
        in
          Term.subst subst rhs
        end
    in
      {data_ty = data_ty, scrutinee = scrutinee,
       constructors = constructors, branches = List.map branch constructors}
    end

  fun datatype_case_normal_form tm =
    let
      val {data_ty, scrutinee, constructors, branches} =
        datatype_case_parts tm
      fun tester constructor =
        datatype_tester_term data_ty constructor scrutinee
      fun cascade [] [] = raise ERR "datatype_case_normal_form"
            "empty datatype case"
        | cascade [_] [branch] = branch
        | cascade (constructor :: constructors) (branch :: branches) =
            boolSyntax.mk_cond
              (tester constructor, branch, cascade constructors branches)
        | cascade _ _ = raise ERR "datatype_case_normal_form"
            "case branch mismatch"
    in
      cascade constructors branches
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
              SmtLib_Theories.decline ("<" ^ token ^ ">")
                "wrong number of arguments"
          fun selector_entry ((selector_index, (selector_name, _)), dict) =
            let
              fun selector_parse token indices args =
                case (indices, args) of
                  ([], [arg]) =>
                    datatype_selector_term ty constructor selector_index arg
                | _ => SmtLib_Theories.decline ("<" ^ token ^ ">")
                    "one argument expected"
            in
              Library.extend_dict ((selector_name, selector_parse), dict)
            end
          fun tester_parse token indices args =
            case (indices, args) of
              ([index], [arg]) =>
                let
                  val index_matches_constructor =
                    Term.aconv index constructor
                    handle Feedback.HOL_ERR _ => false
                  val index_name =
                    Lib.fst (Term.dest_var index)
                    handle Feedback.HOL_ERR _ =>
                      #Name (Term.dest_thy_const index)
                in
                  if same_type (Term.type_of arg, ty) andalso
                     (index_name = cname orelse index_matches_constructor) then
                    datatype_tester_term ty constructor arg
                  else
                    SmtLib_Theories.decline
                      ("<" ^ token ^ " " ^ cname ^ ">")
                      "tester constructor mismatch"
                end
            | _ => SmtLib_Theories.decline
                ("<" ^ token ^ " " ^ cname ^ ">")
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

  fun parser_datatype_term_dictionary_from_types types initial =
    Redblackmap.foldl (fn (ty, name, dict) =>
      case datatype_family ty of
        SOME _ => add_datatype_parser_entries (ty, name, dict)
      | NONE => dict) initial types

  fun parser_dicts_for_translation_aux solver
      ({logic, regime, tydict, tmdict, ...} : translation) =
    let
      fun parsedicts_for_logic logic =
        (case solver of
           SOME solver => SmtLib_Logics.parsedicts_of_solver_logic solver logic
         | NONE => SmtLib_Logics.parsedicts_of_any_solver_logic logic)
        handle e as Feedback.HOL_ERR _ =>
          if String.isSubstring "DT" logic then
            (case solver of
               SOME solver =>
                 SmtLib_Logics.parsedicts_of_solver_logic solver "ALL"
             | NONE => SmtLib_Logics.parsedicts_of_any_solver_logic "ALL")
          else
            raise e
      val ty_dict = Redblackmap.foldl (fn (ty, s, dict) =>
        Redblackmap.insert (dict, s, [SmtLib_Theories.K_zero_zero ty]))
        (Redblackmap.mkDict String.compare) tydict
      val tm_dict = Redblackmap.foldl (fn ((tm, n), s, dict) =>
        let
          (* `full_arity` is only consulted in the HigherOrder regime, so it is
             computed lazily there rather than for every FirstOrder entry. *)
          val accepted_arity =
            case regime of
              FirstOrder => (fn args => List.length args = n)
            | HigherOrder _ =>
                let
                  val full_arity =
                    List.length (Lib.fst (boolSyntax.strip_fun
                      (Term.type_of tm)))
                in
                  fn args => List.length args <= full_arity
                end
        in
          Redblackmap.insert (dict, s, [Lib.K (SmtLib_Theories.zero_args
            (fn args =>
              if accepted_arity args then
                Term.list_mk_comb (tm, args)
              else
                SmtLib_Theories.decline ("<" ^ s ^ ">")
                  "wrong number of arguments"))])
        end)
        (Redblackmap.mkDict String.compare) tmdict
      val tm_dict = parser_datatype_term_dictionary_from_types tydict tm_dict
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
  fun translate_type regime (tydict, ty) =
    if !current_native_sequence_emission andalso
       is_native_sequence_type ty then
      let
        val (tydict, (decls, element_sort)) =
          translate_type regime (tydict, listSyntax.dest_list_type ty)
      in
        (tydict, (decls, "(Seq " ^ element_sort ^ ")"))
      end
    else if is_function_type ty then
      (case regime of
         HigherOrder Standard27 =>
           let
             val (doms, rng) = boolSyntax.strip_fun ty
             val (tydict, declnames) =
               Lib.foldl_map (translate_type regime) (tydict, doms @ [rng])
             val (declss, names) = Lib.split declnames
           in
             (tydict, (List.concat declss,
               "(-> " ^ String.concatWith " " names ^ ")"))
           end
       | _ =>
           let
             val (dom, rng) = Type.dom_rng ty
             val (tydict, (domdecls, domname)) =
               translate_type regime (tydict, dom)
             val (tydict, (rngdecls, rngname)) =
               translate_type regime (tydict, rng)
           in
             (tydict, (domdecls @ rngdecls, "(Array " ^ domname ^ " " ^
               rngname ^ ")"))
           end)
    else
      case first_success (fn (_, f) => f ty)
          (TypeNet.match (builtin_types, ty)) of
        SOME name => (tydict, ([], name))
      | NONE =>
        (case Redblackmap.peek (tydict, ty) of
          SOME name => (tydict, ([], name))
        | NONE =>
          (case translate_datatype_type regime (tydict, ty) of
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
  and translate_datatype_type regime (tydict, ty) =
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
        fun translate_constructor_doms (fam_ty, (dict, decls, sorts)) =
          let
            val tyinfo =
              case TypeBase.fetch fam_ty of
                SOME info => info
              | NONE => raise ERR "translate_datatype_type"
                  "missing TypeBase entry"
            fun translate_one (constructor, (dict, decls, sorts)) =
              let
                val constructor = TypeBasePure.cinst fam_ty constructor
                val (doms, _) = boolSyntax.strip_fun (Term.type_of constructor)
                fun translate_dom (dom, (dict, decls, sorts)) =
                  let
                    val (dict, (new_decls, sort)) =
                      translate_type regime (dict, dom)
                  in
                    (dict, decls @ new_decls, (dom, sort) :: sorts)
                  end
              in
                List.foldl translate_dom (dict, decls, sorts) doms
              end
          in
            List.foldl translate_one (dict, decls, sorts)
              (TypeBasePure.constructors_of tyinfo)
          end
        val (tydict, dependency_decls, field_sorts) =
          List.foldl translate_constructor_doms
            (tydict_with_family, [], []) family
        fun field_sort ty =
          case List.find (fn (field_ty, _) => same_type (ty, field_ty))
              field_sorts of
            SOME (_, sort) => sort
          | NONE => smt_sort_of_type regime tydict ty
        val declaration = datatype_declaration_text field_sort family names
        val name =
          case Redblackmap.peek (tydict, ty) of
            SOME n => n
          | NONE => raise ERR "translate_datatype_type" "unregistered type"
      in
        SOME (tydict, (dependency_decls @ [declaration], name))
      end
      handle Feedback.HOL_ERR _ => NONE
           | Redblackmap.NotFound => NONE

  (* Translation has two regimes.  FirstOrder preserves the legacy,
     arity-keyed encoding: function values use nested Array sorts and
     application/update use select/store.  HigherOrder preserves first-class
     functions, lambdas, and partial application.  Standard27 emits native
     HO-Core syntax; Z3LambdaArray lowers function sorts and applications to
     nested Array/select.  Both dialects eta-expand partially applied ranked
     constants when omission would lose their built-in semantics. *)

  (* Keep ordered lexical names and declaration keys separate from
     semantic dispatch. Fallback keys need not manufacture syntax.
     Find callbacks signal absence with Redblackmap.NotFound, as expected
     by the existing fallback handlers. Callbacks preserve other primary
     exceptions without reclassifying them as absence. Ordinary and fallback
     keys identify cache entries; they do not establish theorem equality.
     Dependency arguments retain bound_items order. The legacy store uses
     Term.compare order here, rather than binder insertion order.
     Sort recording returns the term store so graph declaration metadata
     rolls back with the same persistent accumulator as its symbols.
     Encoding observations commit only after the encoder, rewritten operands
     and expression document succeed. input is the original encoder rator
     (possibly a whole literal); arity counts its ORIGINAL operand list. *)
  type ('term, 'bounds, 'terms, 'key) carrier_term_store_operations = {
    bound_find : 'bounds * 'term -> string,
    bound_peek : 'bounds * 'term -> string option,
    bound_insert : 'bounds * 'term * string -> 'bounds,
    bound_items : 'bounds -> ('term * string) list,
    bound_count : 'bounds -> int,
    ordinary_key : 'term * int -> 'key,
    fallback_key : 'term list * 'term -> 'key,
    term_find : 'terms * 'key -> string,
    term_peek : 'terms * 'key -> string option,
    term_insert : 'terms * 'key * string -> 'terms,
    term_count : 'terms -> int,
    record_sorts : 'terms * 'key * (string list * string) -> 'terms,
    record_encoding : 'terms *
      {input:'term,smt_symbol:string,arity:int} -> 'terms,
    reserve_helper : 'terms * string -> 'terms * bool
  }


  type ('bounds, 'terms, 'key) term_store_operations =
    (Term.term, 'bounds, 'terms, 'key) carrier_term_store_operations
  val legacy_term_store_operations :
      ((Term.term, string) Redblackmap.dict,
       (Term.term * int, string) Redblackmap.dict,
       Term.term * int) term_store_operations = {
    bound_find = Redblackmap.find,
    bound_peek = Redblackmap.peek,
    bound_insert = Redblackmap.insert,
    bound_items = Redblackmap.listItems,
    bound_count = Redblackmap.numItems,
    ordinary_key = Lib.I,
    fallback_key = fn (vars, expression) =>
      (Term.list_mk_abs (vars, expression), List.length vars),
    term_find = Redblackmap.find,
    term_peek = Redblackmap.peek,
    term_insert = Redblackmap.insert,
    term_count = Redblackmap.numItems,
    record_sorts = fn (terms, key, sorts) =>
      (record_emitted_term_sorts key sorts; terms),
    record_encoding = fn (terms,_) => terms,
    reserve_helper = fn (terms,name) =>
      if List.exists (fn saved => saved=name) (!current_bag_helpers)
      then (terms,false) else
        (current_bag_helpers := name :: !current_bag_helpers;(terms,true))
  }

  datatype 'term carrier_parser_case =
      CarrierSelector of {constructor : Term.term, selector_index : int,
                          scrutinee : 'term}
    | CarrierTester of {constructor : Term.term, scrutinee : 'term}

  (* The carrier is opaque throughout the shared dispatcher. Atomic HOL
     constants and types describe schemas, constructors, and declarations;
     every observation or construction of query syntax uses this record.
     Error predicates must classify only ordinary shape failures. In
     particular authentication, budget, and other primary failures must
     escape optional probes and fallback. metadata_error adapts only the
     isolated carrier-free library observations below. commit_error preserves
     its original payload and must not be classified as a fallback error. *)
  type 'term term_translation_operations = {
    type_of : 'term -> Type.hol_type,
    is_var : 'term -> bool,
    is_const : 'term -> bool,
    dest_comb : 'term -> 'term * 'term,
    dest_abs : 'term -> 'term * 'term,
    strip_abs : 'term -> 'term list * 'term,
    strip_comb : 'term -> 'term * 'term list,
    list_mk_abs : 'term list * 'term -> 'term,
    list_mk_comb : 'term * 'term list -> 'term,
    mk_comb : 'term * 'term -> 'term,
    apply_constant : Term.term * 'term -> 'term,
    free_vars : 'term -> 'term list,
    aconv : 'term -> 'term -> bool,
    genvar : Type.hol_type -> 'term,
    same_const : 'term -> Term.term -> bool,
    known_const_matches : Term.term -> 'term -> bool,
    declared_const_arity : 'term -> int,
    term_to_string : 'term -> string,
    is_forall : 'term -> bool,
    is_exists : 'term -> bool,
    strip_forall : 'term -> 'term list * 'term,
    strip_exists : 'term -> 'term list * 'term,
    dest_let : 'term -> ('term * 'term) list * 'term,
    beta_reduce : 'term -> 'term,
    is_marked_set_term : 'term -> bool,
    is_marked_bag_term : 'term -> bool,
    is_raw_number : 'term -> bool,
    set_element_type : 'term -> Type.hol_type,
    bag_element_type : 'term -> Type.hol_type,
    sequence_element_type : 'term -> Type.hol_type,
    contextual_collection_argument : 'term -> int -> 'term option,
    has_contextual_collection_argument : 'term -> bool,
    is_empty_set : 'term -> bool,
    is_univ_set : 'term -> bool,
    dest_set_card : 'term -> 'term,
    is_empty_bag : 'term -> bool,
    dest_bag_card : 'term -> 'term,
    is_nil : 'term -> bool,
    mk_cons : 'term * 'term -> 'term,
    mk_nil : Type.hol_type -> 'term,
    is_parsed_bag_literal : 'term -> bool,
    dest_parsed_bag_literal : 'term -> 'term * 'term,
    native_string_literal : 'term -> string,
    is_injected_string : 'term -> bool,
    dest_injected_string : 'term -> 'term,
    is_injected_float : 'term -> bool,
    dest_injected_float : 'term -> 'term,
    is_injected_string_operation : 'term -> bool,
    dest_injected_string_operation : 'term -> string * 'term list,
    hexadecimal_string : string -> 'term -> string,
    encode_builtin : 'term * 'term list -> string * 'term list,
    builtin_encoding : 'term -> (string * int) option,
    is_constructor : 'term -> bool,
    parser_case : 'term -> 'term carrier_parser_case option,
    datatype_selector_term : Type.hol_type -> Term.term -> int -> 'term ->
      'term,
    closed_constructor_destructor_residual : 'term -> bool,
    has_ranked_semantics : 'term -> bool,
    is_case : 'term -> bool,
    is_update_comb : 'term -> bool,
    dest_update_comb : 'term -> ('term * 'term) * 'term,
    reject_unsupported_smtfloat_constant : 'term -> unit,
    reject_invented_native_datatype_domain : 'term -> Type.hol_type list ->
      unit,
    collection_recognizers : 'term collection_recognizers,
    syntax_error : string -> string -> exn,
    is_fallback_error : exn -> bool,
    is_optional_error : exn -> bool,
    metadata_error : exn -> exn,
    commit_error : exn -> exn
  }

  val term_translation_operations : Term.term term_translation_operations = {
    type_of = (Term.type_of),
    is_var = (Term.is_var),
    is_const = (Term.is_const),
    dest_comb = (Term.dest_comb),
    dest_abs = (Term.dest_abs),
    strip_abs = (Term.strip_abs),
    strip_comb = (boolSyntax.strip_comb),
    list_mk_abs = (Term.list_mk_abs),
    list_mk_comb = (Term.list_mk_comb),
    mk_comb = (Term.mk_comb),
    apply_constant = (Term.mk_comb),
    free_vars = (Term.free_vars),
    aconv = (Term.aconv),
    genvar = (Term.genvar),
    same_const = (same_const),
    known_const_matches = (same_const),
    declared_const_arity = (declared_const_arity),
    term_to_string = (Hol_pp.term_to_string),
    is_forall = (boolSyntax.is_forall),
    is_exists = (boolSyntax.is_exists),
    strip_forall = (boolSyntax.strip_forall),
    strip_exists = (boolSyntax.strip_exists),
    dest_let = (dest_carrier_let),
    beta_reduce = (fn t => boolSyntax.rhs (Thm.concl (Drule.LIST_BETA_CONV t))
      handle Feedback.HOL_ERR _ => t),
    is_marked_set_term = (is_marked_set_term),
    is_marked_bag_term = (is_marked_bag_term),
    is_raw_number = (fn t => mem_aconv t (!current_raw_num_terms)),
    set_element_type = (set_element_type),
    bag_element_type = (bag_element_type),
    sequence_element_type = (sequence_element_type),
    contextual_collection_argument = (contextual_collection_argument),
    has_contextual_collection_argument = (has_contextual_collection_argument),
    is_empty_set = (pred_setSyntax.is_empty),
    is_univ_set = (pred_setSyntax.is_univ),
    dest_set_card = (pred_setSyntax.dest_card),
    is_empty_bag = (bagSyntax.is_empty),
    dest_bag_card = (bagSyntax.dest_card),
    is_nil = (listSyntax.is_nil),
    mk_cons = (listSyntax.mk_cons),
    mk_nil = (listSyntax.mk_nil),
    is_parsed_bag_literal = (is_parsed_bag_literal),
    dest_parsed_bag_literal = (dest_parsed_bag_literal),
    native_string_literal = (native_string_literal),
    is_injected_string = (is_injected_string),
    dest_injected_string = (dest_injected_string),
    is_injected_float = (is_injected_float),
    dest_injected_float = (dest_injected_float),
    is_injected_string_operation = (is_injected_string_operation),
    dest_injected_string_operation = (dest_injected_string_operation),
    hexadecimal_string = (hexadecimal_string),
    encode_builtin = (fn input as (rator, _) =>
      Lib.tryfind (fn parsefn => parsefn input)
        (Net.match rator builtin_symbols)),
    builtin_encoding = (builtin_encoding),
    is_constructor = (TypeBase.is_constructor),
    parser_case = (fn t =>
      case parser_datatype_case t of
        SOME (ParserSelector fields) => SOME (CarrierSelector fields)
      | SOME (ParserTester fields) => SOME (CarrierTester fields)
      | NONE => NONE),
    datatype_selector_term = (datatype_selector_term),
    closed_constructor_destructor_residual =
      (closed_constructor_destructor_residual),
    has_ranked_semantics = (fn c => TypeBase.is_constructor c orelse
      (Term.is_const c andalso
        let val {Thy, Name, ...} = Term.dest_thy_const c
        in Redblackset.member (builtin_const_names, (Thy, Name)) end)),
    is_case = (Lib.can TypeBase.dest_case),
    is_update_comb = (combinSyntax.is_update_comb),
    dest_update_comb = (combinSyntax.dest_update_comb),
    reject_unsupported_smtfloat_constant =
      (reject_unsupported_smtfloat_constant),
    reject_invented_native_datatype_domain =
      (reject_invented_native_datatype_domain),
    collection_recognizers = term_collection_recognizers,
    syntax_error = ERR,
    is_fallback_error = (fn Feedback.HOL_ERR _ => true | _ => false),
    is_optional_error = (fn Portable.Interrupt => false | _ => true),
    metadata_error = Lib.I,
    commit_error = NestedTranslation
  }

  (* returns an updated accumulator, a (possibly empty) list of
     SMT-LIB (type and term) declarations, and the SMT-LIB
     representation of the given term *)
  (* Keep semantic dispatch in one place. The recursive continuation
     carries the same declaration accumulator and lexical bounds,
     including terms synthesized by native encodings. A graph
     scheduler can reuse this step without a second operator table. *)
  fun translate_term_step_with_lexical_output
      (output : 'doc output_operations)
      (seal : 'terms * 'doc -> 'doc)
      (operations : 'term term_translation_operations)
      (store : ('term, 'bounds, 'terms, 'key) carrier_term_store_operations)
      translate translate_body regime apply_operator
      (acc as (tydict, tmdict), (bounds, tm)) =
  let
    val {text = output_text, concat = output_concat,
         join = output_join} = output
    exception DispatchFailure of exn
    fun expected thunk =
      thunk () handle primary =>
        if (#is_fallback_error operations) primary then
          raise DispatchFailure primary
        else raise primary
    fun optional f x =
      SOME (f x)
      handle DispatchFailure primary =>
        if (#is_optional_error operations) primary then NONE
        else raise DispatchFailure primary
      | primary =>
          if (#is_optional_error operations) primary then NONE
          else raise primary
    fun ERR function_name message =
      DispatchFailure ((#syntax_error operations) function_name message)
    (* Only these isolated, carrier-free metadata observations normalize
       library shape errors. Carrier callbacks execute outside this catch. *)
    fun metadata thunk = expected (fn () =>
      thunk () handle primary as Feedback.HOL_ERR _ =>
        raise (#metadata_error operations) primary)
    fun metadata_dom_rng ty = metadata (fn () => Type.dom_rng ty)
    fun metadata_translate_type regime input =
      let val (dict, (declarations, sort)) =
        metadata (fn () => translate_type regime input)
      in (dict, (List.map output_text declarations, sort)) end
    fun output_term_declaration regime name domains range =
      output_text (term_declaration_text regime name domains range)
    val output_generated_forall = generated_forall_with output
    fun metadata_constructor_infos ty name =
      metadata (fn () => datatype_constructor_infos ty name)
    fun metadata_smtfp_sort ty = metadata (fn () => smtfp_sort ty)
    fun metadata_datatype_excluded ty =
      metadata (fn () => datatype_translation_excluded ty)
    fun metadata_strip_fun ty = metadata (fn () => boolSyntax.strip_fun ty)
    fun metadata_fetch ty = metadata (fn () => TypeBase.fetch ty)
    fun metadata_case_const info =
      metadata (fn () => TypeBasePure.case_const_of info)
    fun metadata_constructors info =
      metadata (fn () => TypeBasePure.constructors_of info)
    fun carrier_type_of x =
      expected (fn () => (#type_of operations) x)
    fun carrier_is_var x =
      expected (fn () => (#is_var operations) x)
    fun carrier_is_const x =
      expected (fn () => (#is_const operations) x)
    fun carrier_dest_comb x =
      expected (fn () => (#dest_comb operations) x)
    fun carrier_dest_abs x =
      expected (fn () => (#dest_abs operations) x)
    fun carrier_strip_abs x =
      expected (fn () => (#strip_abs operations) x)
    fun carrier_strip_comb x =
      expected (fn () => (#strip_comb operations) x)
    fun carrier_list_mk_abs x =
      expected (fn () => (#list_mk_abs operations) x)
    fun carrier_list_mk_comb x =
      expected (fn () => (#list_mk_comb operations) x)
    fun carrier_mk_comb x =
      expected (fn () => (#mk_comb operations) x)
    fun carrier_apply_constant x =
      expected (fn () => (#apply_constant operations) x)
    fun carrier_free_vars x =
      expected (fn () => (#free_vars operations) x)
    fun carrier_aconv x y =
      expected (fn () => (#aconv operations) x y)
    fun carrier_genvar x =
      expected (fn () => (#genvar operations) x)
    fun carrier_same_const x y =
      expected (fn () => (#same_const operations) x y)
    fun carrier_known_const_matches x y =
      expected (fn () => (#known_const_matches operations) x y)
    fun carrier_declared_const_arity x =
      expected (fn () => (#declared_const_arity operations) x)
    fun carrier_term_to_string x =
      expected (fn () => (#term_to_string operations) x)
    fun carrier_is_forall x =
      expected (fn () => (#is_forall operations) x)
    fun carrier_is_exists x =
      expected (fn () => (#is_exists operations) x)
    fun carrier_strip_forall x =
      expected (fn () => (#strip_forall operations) x)
    fun carrier_strip_exists x =
      expected (fn () => (#strip_exists operations) x)
    fun carrier_dest_let x =
      expected (fn () => (#dest_let operations) x)
    fun carrier_beta_reduce x =
      expected (fn () => (#beta_reduce operations) x)
    fun carrier_is_marked_set_term x =
      expected (fn () => (#is_marked_set_term operations) x)
    fun carrier_is_marked_bag_term x =
      expected (fn () => (#is_marked_bag_term operations) x)
    fun carrier_is_raw_number x =
      expected (fn () => (#is_raw_number operations) x)
    fun carrier_set_element_type x =
      expected (fn () => (#set_element_type operations) x)
    fun carrier_bag_element_type x =
      expected (fn () => (#bag_element_type operations) x)
    fun carrier_sequence_element_type x =
      expected (fn () => (#sequence_element_type operations) x)
    fun carrier_contextual_collection_argument x y =
      expected (fn () => (#contextual_collection_argument operations) x y)
    fun carrier_has_contextual_collection_argument x =
      expected (fn () => (#has_contextual_collection_argument operations) x)
    fun carrier_is_empty_set x =
      expected (fn () => (#is_empty_set operations) x)
    fun carrier_is_univ_set x =
      expected (fn () => (#is_univ_set operations) x)
    fun carrier_dest_set_card x =
      expected (fn () => (#dest_set_card operations) x)
    fun carrier_is_empty_bag x =
      expected (fn () => (#is_empty_bag operations) x)
    fun carrier_dest_bag_card x =
      expected (fn () => (#dest_bag_card operations) x)
    fun carrier_is_nil x =
      expected (fn () => (#is_nil operations) x)
    fun carrier_mk_cons x =
      expected (fn () => (#mk_cons operations) x)
    fun carrier_mk_nil x =
      expected (fn () => (#mk_nil operations) x)
    fun carrier_is_parsed_bag_literal x =
      expected (fn () => (#is_parsed_bag_literal operations) x)
    fun carrier_dest_parsed_bag_literal x =
      expected (fn () => (#dest_parsed_bag_literal operations) x)
    fun carrier_native_string_literal x =
      expected (fn () => (#native_string_literal operations) x)
    fun carrier_is_injected_string x =
      expected (fn () => (#is_injected_string operations) x)
    fun carrier_dest_injected_string x =
      expected (fn () => (#dest_injected_string operations) x)
    fun carrier_is_injected_float x =
      expected (fn () => (#is_injected_float operations) x)
    fun carrier_dest_injected_float x =
      expected (fn () => (#dest_injected_float operations) x)
    fun carrier_is_injected_string_operation x =
      expected (fn () => (#is_injected_string_operation operations) x)
    fun carrier_dest_injected_string_operation x =
      expected (fn () => (#dest_injected_string_operation operations) x)
    fun carrier_hexadecimal_string x y =
      expected (fn () => (#hexadecimal_string operations) x y)
    fun carrier_encode_builtin x =
      expected (fn () => (#encode_builtin operations) x)
    fun carrier_builtin_encoding x =
      expected (fn () => (#builtin_encoding operations) x)
    fun carrier_is_constructor x =
      expected (fn () => (#is_constructor operations) x)
    fun carrier_parser_case x =
      expected (fn () => (#parser_case operations) x)
    fun carrier_datatype_selector_term x y z u =
      expected (fn () => (#datatype_selector_term operations) x y z u)
    fun carrier_closed_constructor_destructor_residual x =
      expected (fn () => (#closed_constructor_destructor_residual
        operations) x)
    fun carrier_has_ranked_semantics x =
      expected (fn () => (#has_ranked_semantics operations) x)
    fun carrier_is_case x =
      expected (fn () => (#is_case operations) x)
    fun carrier_is_update_comb x =
      expected (fn () => (#is_update_comb operations) x)
    fun carrier_dest_update_comb x =
      expected (fn () => (#dest_update_comb operations) x)
    fun carrier_reject_unsupported_smtfloat_constant x =
      expected (fn () => (#reject_unsupported_smtfloat_constant operations) x)
    fun carrier_reject_invented_native_datatype_domain x y =
      expected (fn () => (#reject_invented_native_datatype_domain
        operations) x y)
    fun carrier_string_nth_shape current = expected (fn () =>
      (#string_nth_shape (#collection_recognizers operations)) current)
    fun carrier_seq_extract_shape current = expected (fn () =>
      (#seq_extract_shape (#collection_recognizers operations)) current)
    fun carrier_seq_at_shape current = expected (fn () =>
      (#seq_at_shape (#collection_recognizers operations)) current)
    val translate = fn input => expected (fn () => translate input)
    val translate_body =
      fn input => expected (fn () => translate_body input)
  in
  let
    val {bound_find, bound_peek, bound_insert, bound_items, bound_count,
         ordinary_key, fallback_key, term_find, term_peek, term_insert,
         term_count, record_sorts, record_encoding, reserve_helper} = store
    val bound_find = fn input => expected (fn () => bound_find input)
    val bound_peek = fn input => expected (fn () => bound_peek input)
    val bound_insert = fn input => expected (fn () => bound_insert input)
    val bound_items = fn input => expected (fn () => bound_items input)
    val bound_count = fn input => expected (fn () => bound_count input)
    val ordinary_key = fn input => expected (fn () => ordinary_key input)
    val fallback_key = fn input => expected (fn () => fallback_key input)
    val term_find = fn input => expected (fn () => term_find input)
    val term_peek = fn input => expected (fn () => term_peek input)
    val term_insert = fn input => expected (fn () => term_insert input)
    val term_count = fn input => expected (fn () => term_count input)
    val record_sorts = fn input => expected (fn () => record_sorts input)
    val record_encoding = fn input => expected (fn () => record_encoding input)
    val reserve_helper = fn input => expected (fn () => reserve_helper input)
    val recognizers = #collection_recognizers operations
    val dispatch = native_dispatch_with
      {same_const=carrier_same_const,is_constant=carrier_is_const,
       declared_arity=carrier_declared_const_arity,type_of=carrier_type_of,
       is_raw_number=carrier_is_raw_number,
       syntax_error= #syntax_error operations} recognizers regime
    val native_dispatch = {
      whole_candidate = fn base => fn current =>
        expected (fn () => (#whole_candidate dispatch) base current),
      application_candidate = fn base => fn current => fn head => fn args =>
        expected (fn () =>
          (#application_candidate dispatch) base current head args),
      guard_builtin = fn current => fn head =>
        expected (fn () => (#guard_builtin dispatch) current head),
      equality_operands = fn head => fn args =>
        expected (fn () => (#equality_operands dispatch) head args)
    }
    fun sexpr x [] = output_text x
      | sexpr x xs =
          output_concat [output_text ("(" ^ x ^ " "),
            output_join " " xs, output_text ")"]
    fun expression_application function [] = function
      | expression_application function arguments =
          output_concat [output_text "(", function, output_text " ",
            output_join " " arguments, output_text ")"]
    fun explicit_apply function argument =
      case regime of
        HigherOrder Standard27 =>
          sexpr (case apply_operator of
              ApplyUnderscore => "_"
            | ApplyAt => "@") [function, argument]
      | _ => sexpr "select" [function, argument]
    (* Create a mapping from bound variables to their SMT-LIB names; if a
       variable is already mapped, return its existing SMT-LIB name. *)
    fun create_bound_name (bounds, v) =
      (bounds, bound_find (bounds, v))
      handle Redblackmap.NotFound =>
        let
          val name = bv_prefix ^ Int.toString (bound_count bounds)
        in
          (bound_insert (bounds, v, name), name)
        end
    fun builtin_symbol (rator, original_rands) =
      let
        val _ = (#guard_builtin native_dispatch) tm rator
        val original_arity = List.length original_rands
        val (name, rands) = carrier_encode_builtin (rator, original_rands)
        val (acc, declnames) = Lib.foldl_map
          (fn (a, t) =>
            translate (a, (bounds, t)))
          (acc, rands)
        val (declss, names) = Lib.split declnames
        val expression = sexpr name names
        val (tydict,terms) = acc
        val terms = record_encoding (terms,
          {input=rator,smt_symbol=name,arity=original_arity})
      in
        ((tydict,terms), (List.concat declss, expression))
      end
    (* Equality is a fully ranked Core operator at every HOL instantiation.
       Once its exact head and arity have been admitted, an operand failure
       must escape: falling through would eventually invent a function for
       polymorphic equality itself, and can obscure the actual unsupported
       operand (notably a residual function over a native datatype). *)
    fun builtin_equality (rator, rands) =
            let
              val (left,right) =
                (#equality_operands native_dispatch) rator rands
              fun translate_argument (a, argument) =
                translate
                  (a, (bounds, argument))
                handle DispatchFailure e =>
                  raise (#commit_error operations) e
              val (acc, declnames) =
                Lib.foldl_map translate_argument (acc, [left, right])
              val (declss, names) = Lib.split declnames
            in
              (acc, (List.concat declss, sexpr "=" names))
            end
    fun set_sort tydict set =
      let
        val element_ty = carrier_set_element_type set
        val (tydict, (decls, element_sort)) =
          metadata_translate_type regime (tydict, element_ty)
      in
        (tydict, (decls, "(Set " ^ element_sort ^ ")"))
      end
    fun set_array_sort tydict set =
      let
        val element_ty = carrier_set_element_type set
        val (tydict, (decls, element_sort)) =
          metadata_translate_type regime (tydict, element_ty)
      in
        (tydict, (decls, "(Array " ^ element_sort ^ " Bool)"))
      end
    fun selected_set_sort tydict set =
      case !current_set_backend of
        CVC5ArraySet => set_array_sort tydict set
      | _ => set_sort tydict set
    fun set_constant tydict set value =
      let
        val element_ty = carrier_set_element_type set
        val (tydict, (decls, element_sort)) =
          metadata_translate_type regime (tydict, element_ty)
        val sort = "(Set " ^ element_sort ^ ")"
        val text =
          case !current_set_backend of
            Z3Set => "((as const " ^ sort ^ ") " ^ value ^ ")"
          | CVC5NativeSet =>
              "(as set." ^ (if value = "true" then "universe" else "empty") ^
              " " ^ sort ^ ")"
          | CVC5ArraySet => "((as const (Array " ^ element_sort ^
              " Bool)) " ^ value ^ ")"
      in
        (tydict, (decls, output_text text))
      end
    fun bag_sort tydict bag =
      let
        val element_ty = carrier_bag_element_type bag
        val (tydict, (decls, element_sort)) =
          metadata_translate_type regime (tydict, element_ty)
      in
        (tydict, (decls, "(Bag " ^ element_sort ^ ")"))
      end
    fun bag_array_sort tydict bag =
      let
        val element_ty = carrier_bag_element_type bag
        val (tydict, (decls, element_sort)) =
          metadata_translate_type regime (tydict, element_ty)
      in
        (tydict, (decls, "(Array " ^ element_sort ^ " Int)"))
      end
    fun selected_bag_sort tydict bag =
      case !current_bag_backend of
        CVC5NativeBag => bag_sort tydict bag
      | _ => bag_array_sort tydict bag
    fun bound_variable_sort tydict var =
      if carrier_is_marked_set_term var then
        selected_set_sort tydict var
      else if carrier_is_marked_bag_term var then
        selected_bag_sort tydict var
      else
        metadata_translate_type regime (tydict, carrier_type_of var)
    (* Emit [(head ((v0 T0) ...) body)].  [nest_errors] re-raises a body
       failure as NestedTranslation, which stops an enclosing
       [handle Feedback.HOL_ERR _] fallback from swallowing it silently. *)
    fun emit_binder {head, nest_errors} (acc as (tydict, tmdict)) vars body =
      let
        val (binder_bounds, smtvars) =
          Lib.foldl_map create_bound_name (bounds, vars)
        fun variable_type (tydict, var) = bound_variable_sort tydict var
        val (tydict, vardecltys) =
          Lib.foldl_map variable_type (tydict, vars)
        val (vardeclss, vartys) = Lib.split vardecltys
        val binders = ListPair.mapEq
          (fn (smtvar, ty) => "(" ^ smtvar ^ " " ^ ty ^ ")")
          (smtvars, vartys)
        val (acc, (bodydecls, bodyname)) =
          translate_body
            ((tydict, tmdict), (binder_bounds, body))
          handle DispatchFailure e =>
            if nest_errors then raise (#commit_error operations) e
            else raise DispatchFailure e
      in
        (acc, (List.concat vardeclss @ bodydecls,
          output_concat
            [output_text ("(" ^ head ^ " (" ^
               String.concatWith " " binders ^ ") "),
             bodyname, output_text ")"]))
      end
    fun fallback_dependencies expression =
      let
        val free_vars = carrier_free_vars expression
      in
        List.filter
          (fn (var, _) => List.exists (carrier_aconv var) free_vars)
          (bound_items bounds)
      end
    fun fallback_application name dependencies =
      sexpr name (List.map (output_text o Lib.snd) dependencies)
    fun fallback_array_definition prefix range_sort element_type
        acc expression args body =
      let
        val dependencies = fallback_dependencies expression
        val dependency_vars = List.map Lib.fst dependencies
        val cache_key =
          fallback_key (dependency_vars, expression)
      in
        case term_peek (Lib.snd acc, cache_key) of
          SOME name =>
            (acc, ([], fallback_application name dependencies))
        | NONE =>
          let
            val (tydict, (typedecls, element_sort)) =
              metadata_translate_type regime (Lib.fst acc, element_type)
            val tmdict = Lib.snd acc
            val name = prefix ^ Int.toString (term_count tmdict)
            val tmdict = term_insert (tmdict, cache_key, name)
            val binder = prefix ^ "_x" ^
              Int.toString (term_count tmdict)
            val (tydict, dependency_declsorts) =
              Lib.foldl_map
                (fn (dict, (var, dependency_name)) =>
                  let
                    val (dict, (decls, sort)) =
                      bound_variable_sort dict var
                  in
                    (dict, ((decls, "(" ^ dependency_name ^ " " ^
                      sort ^ ")"), sort))
                  end)
                (tydict, dependencies)
            val (dependency_data, dependency_sorts) =
              Lib.split dependency_declsorts
            val (dependency_typedecls, dependency_decls) =
              Lib.split dependency_data
            val array_sort = "(Array " ^ element_sort ^ " " ^
              range_sort ^ ")"
            val tmdict = record_sorts
              (tmdict, cache_key, (dependency_sorts, array_sort))
            val declaration =
              if List.null dependency_sorts then
                "(declare-const " ^ name ^ " " ^ array_sort ^ ")\n"
              else
                "(declare-fun " ^ name ^ " (" ^
                String.concatWith " " dependency_sorts ^ ") " ^
                array_sort ^ ")\n"
            val application = fallback_application name dependencies
            val quantified_decls = dependency_decls @
              ["(" ^ binder ^ " " ^ element_sort ^ ")"]
            val definition = output_concat
              [output_text "(assert ",
               output_generated_forall quantified_decls
                 (seal (tmdict, output_concat
                   [output_text "(= (select ", application,
                    output_text (" " ^ binder ^ ") "),
                    body (output_text binder) args, output_text ")"])),
               output_text ")\n"]
          in
            ((tydict, tmdict),
             (typedecls @ List.concat dependency_typedecls @
                [output_text declaration, definition],
              application))
          end
      end
    (* cvc5's non-finite bridge deliberately stays in the ordinary array
       model.  Pointwise set operations are named arrays constrained by a
       quantified definition, rather than cvc5's finite set operators. *)
    fun fallback_set_definition acc set args body =
      fallback_array_definition "set" "Bool" (carrier_set_element_type set)
        acc set args body
    fun native_sequence_builtin (rator, rands) =
      let
        fun translate_args_from start args =
          let
            val (acc, declnames) = Lib.foldl_map
              (fn (a, arg) =>
                translate (a, (bounds, arg)))
              (start, args)
            val (declss, names) = Lib.split declnames
          in
            (acc, (List.concat declss, names))
          end
        fun translate_args args = translate_args_from acc args
        (* A function-valued fold callback must keep its own binders
           separate from the accumulator it returns, so the two callback
           arguments cannot be left to the single-binder lowering.  Unlike
           the two lambda sites, this one leaves a body failure as a plain
           HOL_ERR, so the enclosing fallback chain still gets to try the
           uninterpreted lowering. *)
        fun translate_fold_function function =
          case carrier_strip_abs function of
            (element :: accumulator :: rest, body) =>
              emit_binder {head = "lambda", nest_errors = false} acc
                [element, accumulator] (carrier_list_mk_abs (rest, body))
          | _ =>
              translate (acc, (bounds, function))
        fun emit name args =
          let val (acc, (decls, names)) = translate_args args
          in (acc, (decls, sexpr name names)) end
        fun emit_foldl args =
          case args of
            function :: rest =>
              let
                val (acc, (function_decls, function_name)) =
                  translate_fold_function function
                val (acc, (rest_decls, rest_names)) =
                  translate_args_from acc rest
              in
                (acc, (function_decls @ rest_decls,
                  sexpr "seq.foldl" (function_name :: rest_names)))
              end
          | [] => raise ERR "native_sequence_builtin" "wrong FOLDL arity"
        fun emit_extract (sequence, index, size) =
          emit "seq.extract" [sequence, index, size]
        fun emit_at (sequence, index) = emit "seq.at" [sequence, index]
      in
        if carrier_same_const rator intSyntax.int_injection orelse
           carrier_same_const rator int_of_num_tm then
          (case rands of
             [length] =>
               let val (head, args) = carrier_strip_comb length in
                 if carrier_same_const head seq_length_tm then emit
                   "seq.len" args
                 else raise ERR "native_sequence_builtin" "wrong length"
               end
           | _ => raise ERR "native_sequence_builtin" "wrong coercion")
        else
          (case optional carrier_string_nth_shape tm of
             SOME (string, index) => emit "seq.nth" [string, index]
           | NONE =>
          (case optional carrier_seq_extract_shape tm of
          SOME shape => emit_extract shape
        | NONE =>
          (case optional carrier_seq_at_shape tm of
             SOME shape => emit_at shape
           | NONE =>
             if carrier_is_nil tm then
               let
                 val (tydict, (decls, element_sort)) =
                   metadata_translate_type regime
                     (Lib.fst acc, carrier_sequence_element_type tm)
               in
                 ((tydict, Lib.snd acc), (decls,
                   output_text
                     ("(as seq.empty (Seq " ^ element_sort ^ "))")))
               end
             else if carrier_same_const rator seq_append_tm then emit
               "seq.++" rands
             else if carrier_same_const rator seq_length_tm then emit
               "seq.len" rands
             else if carrier_same_const rator seq_cons_tm then
               (case rands of
                  [element, tail] =>
                    let val (acc, (decls, names)) = translate_args rands in
                      case names of [element_name, tail_name] =>
                        if carrier_is_nil tail then
                          (acc, (decls, sexpr "seq.unit" [element_name]))
                        else
                          (acc, (decls, sexpr "seq.++"
                            [sexpr "seq.unit" [element_name], tail_name]))
                    | _ => raise ERR "native_sequence_builtin"
                        "wrong cons arity"
                    end
                | _ => raise ERR "native_sequence_builtin" "wrong cons arity")
             else if carrier_same_const rator seq_reverse_tm then emit
               "seq.rev" rands
             else if carrier_same_const rator seq_prefix_tm then
               emit "seq.prefixof" rands
             else if carrier_same_const rator seq_suffix_tm then
               (case rands of
                  [sequence, suffix] =>
                    emit "seq.suffixof" [suffix, sequence]
                | _ => raise ERR "native_sequence_builtin"
                    "wrong suffix arity")
             else if carrier_same_const rator seq_lupdate_tm then
               (case rands of [element, index, sequence] =>
                  emit "seq.update"
                    [sequence, carrier_apply_constant (int_of_num_tm, index),
                     carrier_mk_cons (element,
                       carrier_mk_nil (carrier_type_of element))]
                | _ => raise ERR "native_sequence_builtin"
                    "wrong LUPDATE arity")
             else if carrier_same_const rator seq_map_tm then emit "seq.map"
               rands
             else if carrier_same_const rator seq_foldl_tm then emit_foldl
               rands
             else if carrier_same_const rator seq_contains_tm then
               emit "seq.contains" rands
             else if carrier_same_const rator smt_seq_nth_tm then emit
               "seq.nth" rands
             else if carrier_same_const rator smt_seq_extract_tm then
               emit "seq.extract" rands
             else if carrier_same_const rator smt_seq_at_tm then emit
               "seq.at" rands
             else if carrier_same_const rator smt_seq_indexof_tm then
               emit "seq.indexof" rands
             else if carrier_same_const rator smt_seq_replace_tm then
               emit "seq.replace" rands
             else if carrier_same_const rator smt_seq_replace_all_tm then
               emit "seq.replace_all" rands
             else if carrier_same_const rator smt_seq_update_tm then
               emit "seq.update" rands
             else raise ERR "native_sequence_builtin"
               "unsupported native sequence term")))
      end
    fun native_set_builtin (rator, rands) =
      if carrier_same_const rator intSyntax.int_injection orelse
         carrier_same_const rator int_of_num_tm then
        (case rands of [card] =>
           let
             val set = carrier_dest_set_card card
             val (acc, (decls, name)) =
               translate (acc, (bounds, set))
           in
             case !current_set_backend of
               CVC5NativeSet => (acc, (decls, sexpr "set.card" [name]))
             | Z3Set => raise ERR "native_set_builtin"
                 "set.card is unavailable for solver Z3"
             | CVC5ArraySet => raise ERR "native_set_builtin"
                 "set.card requires a finiteness-entailing cvc5 goal"
           end
         | _ => raise ERR "native_set_builtin" "wrong card arity")
      else
      let
        val (acc, declnames) = Lib.foldl_map
          (fn (a, t) => translate (a, (bounds, t)))
          (acc, rands)
        val (declss, names) = Lib.split declnames
        val decls = List.concat declss
        fun binary z3 cvc5 fallback =
          case names of [left, right] =>
            (case !current_set_backend of
               Z3Set => (acc, (decls, sexpr z3 [left, right]))
             | CVC5NativeSet => (acc, (decls, sexpr cvc5 [left, right]))
             | CVC5ArraySet =>
                 let
                   fun body x [l, r] = fallback x l r
                     | body _ _ = raise ERR "native_set_builtin" "arity"
                   val (acc, (defs, name)) =
                     fallback_set_definition acc tm names body
                 in (acc, (decls @ defs, name)) end)
          | _ => raise ERR "native_set_builtin" "wrong binary set arity"
        fun unary z3 cvc5 =
          case names of [set] =>
            (case !current_set_backend of
               Z3Set => (acc, (decls, sexpr z3 [set]))
             | CVC5NativeSet => (acc, (decls, sexpr cvc5 [set]))
             | CVC5ArraySet =>
                 let
                   fun body x [s] = sexpr "not" [sexpr "select" [s, x]]
                     | body _ _ = raise ERR "native_set_builtin" "arity"
                   val (acc, (defs, name)) =
                     fallback_set_definition acc tm names body
                 in (acc, (decls @ defs, name)) end)
          | _ => raise ERR "native_set_builtin" "wrong unary set arity"
      in
        if carrier_same_const rator pred_setSyntax.in_tm then
          (case names of [element, set] =>
             (acc, (decls,
               case !current_set_backend of
                 CVC5NativeSet => sexpr "set.member" [element, set]
               | _ => sexpr "select" [set, element]))
           | _ => raise ERR "native_set_builtin" "wrong membership arity")
        else if carrier_same_const rator pred_setSyntax.insert_tm then
          (case (rands, names) of
             ([element, set], [element_name, set_name]) =>
               let
                 val singleton = carrier_is_empty_set set
                 val text =
                   case !current_set_backend of
                     Z3Set => sexpr "store" [set_name, element_name,
                       output_text "true"]
                   | CVC5NativeSet =>
                       if singleton then sexpr "set.singleton" [element_name]
                       else sexpr "set.insert" [element_name, set_name]
                   | CVC5ArraySet =>
                       sexpr "store" [set_name, element_name, output_text
                         "true"]
               in (acc, (decls, text)) end
           | _ => raise ERR "native_set_builtin" "wrong insert arity")
        else if carrier_same_const rator pred_setSyntax.delete_tm then
          (case names of [set, element] =>
             (case !current_set_backend of
                CVC5NativeSet => (acc, (decls,
                  sexpr "set.minus" [set, sexpr "set.singleton" [element]]))
              | _ => (acc, (decls, sexpr "store" [set, element, output_text
                "false"])))
           | _ => raise ERR "native_set_builtin" "wrong delete arity")
        else if carrier_same_const rator pred_setSyntax.union_tm then
          binary "union" "set.union"
            (fn x => fn left => fn right =>
              sexpr "or" [sexpr "select" [left, x], sexpr "select" [right, x]])
        else if carrier_same_const rator pred_setSyntax.inter_tm then
          binary "intersection" "set.inter"
            (fn x => fn left => fn right =>
              sexpr "and" [sexpr "select" [left, x], sexpr "select" [right,
                x]])
        else if carrier_same_const rator pred_setSyntax.diff_tm then
          binary "setminus" "set.minus"
            (fn x => fn left => fn right =>
              let
                val in_left = sexpr "select" [left, x]
                val in_right = sexpr "select" [right, x]
              in
                sexpr "and" [in_left, sexpr "not" [in_right]]
              end)
        else if carrier_same_const rator pred_setSyntax.compl_tm then
          unary "complement" "set.complement"
        else if carrier_same_const rator pred_setSyntax.subset_tm then
          (case names of [left, right] =>
             (case !current_set_backend of
                Z3Set => (acc, (decls, sexpr "subset" [left, right]))
              | CVC5NativeSet => (acc, (decls, sexpr "set.subset" [left,
                right]))
              | CVC5ArraySet =>
                  let
                    val element_ty = carrier_set_element_type (List.hd rands)
                    val (tydict, (typedecls, element_sort)) =
                      metadata_translate_type regime (Lib.fst acc, element_ty)
                    val tmdict = Lib.snd acc
                    val binder = "set_x" ^ Int.toString
                      (term_count tmdict)
                  in
                    ((tydict, tmdict), (decls @ typedecls,
                      output_generated_forall
                        ["(" ^ binder ^ " " ^ element_sort ^ ")"]
                        (output_concat
                          [output_text "(=> (select ", left,
                           output_text (" " ^ binder ^ ") (select "), right,
                           output_text (" " ^ binder ^ "))")])))
                  end)
           | _ => raise ERR "native_set_builtin" "wrong subset arity")
        else if carrier_is_empty_set tm then
          let val (tydict, (constant_decls, text)) =
            set_constant (Lib.fst acc) tm "false"
          in ((tydict, Lib.snd acc), (constant_decls, text)) end
        else if carrier_is_univ_set tm then
          let val (tydict, (constant_decls, text)) =
            set_constant (Lib.fst acc) tm "true"
          in ((tydict, Lib.snd acc), (constant_decls, text)) end
        else
          raise ERR "native_set_builtin" "unsupported native set term"
      end
    fun bag_constant tydict bag =
      let
        val element_ty = carrier_bag_element_type bag
        val (tydict, (decls, element_sort)) =
          metadata_translate_type regime (tydict, element_ty)
        val text =
          case !current_bag_backend of
            CVC5NativeBag => "(as bag.empty (Bag " ^ element_sort ^ "))"
          | _ => "((as const (Array " ^ element_sort ^ " Int)) 0)"
      in
        (tydict, (decls, output_text text))
      end
    fun translate_parsed_bag_literal acc =
      let
        val (element, count) = carrier_dest_parsed_bag_literal tm
        val (acc, (element_decls, element_name)) =
          translate (acc, (bounds, element))
        val (acc, (count_decls, count_name)) =
          translate (acc, (bounds, count))
        val (tydict, (type_decls, element_sort)) =
          metadata_translate_type regime (Lib.fst acc, carrier_type_of element)
        val text =
          case !current_bag_backend of
            CVC5NativeBag => sexpr "bag" [element_name, count_name]
          | _ =>
              let
                val array_count =
                  sexpr "ite"
                    [sexpr "<=" [output_text "0", count_name],
                     count_name, output_text "0"]
              in
                sexpr "store"
                  [output_text ("((as const (Array " ^ element_sort ^
                    " Int)) 0)"),
                   element_name, array_count]
              end
      in
        ((tydict, Lib.snd acc),
         (element_decls @ count_decls @ type_decls, text))
      end
    fun fallback_bag_definition acc bag args body =
      fallback_array_definition "bag" "Int" (carrier_bag_element_type bag)
        acc bag args body
    fun z3_bag_helper terms name definition =
      let val (terms,fresh) = reserve_helper (terms,name)
      in (terms,if fresh then [output_text definition] else []) end
    val native_bag_count_application =
      fn head => fn args => expected (fn () =>
        (#bag_count_application recognizers) head args)
    fun native_bag_builtin (rator, rands) =
      if carrier_same_const rator intSyntax.int_injection orelse
         carrier_same_const rator int_of_num_tm then
        (case rands of [card] =>
           (case native_bag_count_application
               (Lib.fst (carrier_strip_comb card))
               (Lib.snd (carrier_strip_comb card)) of
              SOME (bag, element) =>
                let
                  val (acc, (bag_decls, bag_name)) =
                    translate (acc, (bounds, bag))
                  val (acc, (element_decls, element_name)) =
                    translate
                      (acc, (bounds, element))
                  val count =
                    case !current_bag_backend of
                      CVC5NativeBag =>
                        sexpr "bag.count" [element_name, bag_name]
                    | _ => sexpr "select" [bag_name, element_name]
                in
                  (acc, (bag_decls @ element_decls, count))
                end
            | NONE =>
                let
                  val bag = carrier_dest_bag_card card
                  val (acc, (decls, name)) =
                    translate (acc, (bounds, bag))
                in
                  case !current_bag_backend of
                    CVC5NativeBag => (acc, (decls, sexpr "bag.card" [name]))
                  | Z3ArrayBag => raise ERR "native_bag_builtin"
                      "bag.card is unavailable for solver Z3"
                  | CVC5ArrayBag => raise ERR "native_bag_builtin"
                      "bag.card requires a finiteness-entailing cvc5 goal"
                end)
         | _ => raise ERR "native_bag_builtin" "wrong card arity")
      else if carrier_same_const rator bagSyntax.BAG_CARD_tm then
        (case rands of [bag] =>
           let
             val (acc, (decls, name)) =
               translate (acc, (bounds, bag))
           in
             case !current_bag_backend of
               CVC5NativeBag => (acc, (decls, sexpr "bag.card" [name]))
             | Z3ArrayBag => raise ERR "native_bag_builtin"
                 "bag.card is unavailable for solver Z3"
             | CVC5ArrayBag => raise ERR "native_bag_builtin"
                 "bag.card requires a finiteness-entailing cvc5 goal"
           end
         | _ => raise ERR "native_bag_builtin" "wrong card arity")
      else
      let
        fun translate_bag_arg (a, t) =
          translate (a, (bounds, t))
        val (acc, declnames) = Lib.foldl_map translate_bag_arg (acc, rands)
        val (declss, names) = Lib.split declnames
        val decls = List.concat declss
        fun fallback body =
          let
            val (acc, (defs, name)) =
              fallback_bag_definition acc tm names body
          in (acc, (decls @ defs, name)) end
        fun binary native z3 fallback_body =
          case names of [left, right] =>
            (case !current_bag_backend of
               CVC5NativeBag => (acc, (decls, sexpr native [left, right]))
             | Z3ArrayBag =>
                 let val (terms,map_decls,map_name) = z3 (Lib.snd acc) in
                   ((Lib.fst acc,terms), (decls @ map_decls,
                     output_concat
                       [output_text ("((_ map " ^ map_name ^ ") "), left,
                        output_text " ", right, output_text ")"]))
                 end
             | CVC5ArrayBag => fallback fallback_body)
          | _ => raise ERR "native_bag_builtin" "wrong binary bag arity"
      in
        if carrier_same_const rator bag_in_tm then
          (case names of [element, bag] =>
             (acc, (decls,
               case !current_bag_backend of
                 CVC5NativeBag => sexpr "bag.member" [element, bag]
               | _ => sexpr "<" [output_text "0", sexpr "select" [bag,
                 element]]))
           | _ => raise ERR "native_bag_builtin" "wrong membership arity")
        else if carrier_same_const rator bagSyntax.BAG_INSERT_tm then
          (case names of [element, bag] =>
             (acc, (decls,
               case !current_bag_backend of
                 CVC5NativeBag => sexpr "bag.union_disjoint"
                   [sexpr "bag" [element, output_text "1"], bag]
               | _ => sexpr "store" [bag, element,
                   sexpr "+" [sexpr "select" [bag, element], output_text
                     "1"]]))
           | _ => raise ERR "native_bag_builtin" "wrong insert arity")
        else if carrier_same_const rator bagSyntax.BAG_UNION_tm then
          binary "bag.union_disjoint"
            (fn terms => (terms,[], "(+ (Int Int) Int)"))
            (fn x => fn [left, right] =>
              sexpr "+" [sexpr "select" [left, x],
                sexpr "select" [right, x]]
              | _ => raise ERR "native_bag_builtin" "wrong fallback arity")
        else if carrier_same_const rator bagSyntax.BAG_DIFF_tm then
          binary "bag.difference_subtract"
            (fn terms => let val (terms,declarations) =
              z3_bag_helper terms "holsmt_bag_nat_sub"
              ("(define-fun holsmt_bag_nat_sub ((x Int) (y Int)) Int " ^
               "(ite (< x y) 0 (- x y)))\n")
              in (terms,declarations,"holsmt_bag_nat_sub") end)
            (fn x => fn [left, right] =>
              sexpr "ite" [sexpr "<" [sexpr "select" [left, x],
                sexpr "select" [right, x]], output_text "0",
                sexpr "-" [sexpr "select" [left, x],
                  sexpr "select" [right, x]]]
              | _ => raise ERR "native_bag_builtin" "wrong fallback arity")
        else if carrier_same_const rator bag_merge_tm then
          binary "bag.union_max"
            (fn terms => let val (terms,declarations) =
              z3_bag_helper terms "holsmt_bag_max"
              ("(define-fun holsmt_bag_max ((x Int) (y Int)) Int " ^
               "(ite (< x y) y x))\n")
              in (terms,declarations,"holsmt_bag_max") end)
            (fn x => fn [left, right] =>
              sexpr "ite" [sexpr "<" [sexpr "select" [left, x],
                sexpr "select" [right, x]], sexpr "select" [right, x],
                sexpr "select" [left, x]]
              | _ => raise ERR "native_bag_builtin" "wrong fallback arity")
        else if carrier_same_const rator bag_inter_tm then
          binary "bag.inter_min"
            (fn terms => let val (terms,declarations) =
              z3_bag_helper terms "holsmt_bag_min"
              ("(define-fun holsmt_bag_min ((x Int) (y Int)) Int " ^
               "(ite (< x y) x y))\n")
              in (terms,declarations,"holsmt_bag_min") end)
            (fn x => fn [left, right] =>
              sexpr "ite" [sexpr "<" [sexpr "select" [left, x],
                sexpr "select" [right, x]], sexpr "select" [left, x],
                sexpr "select" [right, x]]
              | _ => raise ERR "native_bag_builtin" "wrong fallback arity")
        else if carrier_same_const rator bagSyntax.SUB_BAG_tm then
          (case names of [left, right] =>
             (case !current_bag_backend of
                CVC5NativeBag =>
                  (acc, (decls, sexpr "bag.subbag" [left, right]))
              | _ =>
                  let
                    val element_ty = carrier_bag_element_type (List.hd rands)
                    val (tydict, (typedecls, element_sort)) =
                      metadata_translate_type regime (Lib.fst acc, element_ty)
                    val binder = "bag_x" ^ Int.toString
                      (term_count (Lib.snd acc))
                  in
                    ((tydict, Lib.snd acc), (decls @ typedecls,
                      output_generated_forall
                        ["(" ^ binder ^ " " ^ element_sort ^ ")"]
                        (output_concat
                          [output_text "(<= (select ", left,
                           output_text (" " ^ binder ^ ") (select "), right,
                           output_text (" " ^ binder ^ "))")])))
                  end)
           | _ => raise ERR "native_bag_builtin" "wrong subbag arity")
        else if carrier_is_empty_bag tm then
          let val (tydict, (constant_decls, text)) =
            bag_constant (Lib.fst acc) tm
          in ((tydict, Lib.snd acc), (constant_decls, text)) end
        else
          raise ERR "native_bag_builtin" "unsupported native bag term"
      end
    fun ensure_type ((tydict, tmdict), ty) =
      let val (tydict, (decls, name)) = metadata_translate_type regime
        (tydict, ty)
      in (((tydict, tmdict), decls), name) end
    fun translate_closed_destructor_residual acc =
      let
        val _ = carrier_closed_constructor_destructor_residual tm orelse
          raise ERR "translate_closed_destructor_residual"
            "not a closed constructor-headed destructor residue"
        val (((tydict, tmdict), typedecls), sort) =
          ensure_type (acc, carrier_type_of tm)
      in
        case term_peek (tmdict, (ordinary_key (tm, 0))) of
          SOME name => ((tydict, tmdict), (typedecls, output_text name))
        | NONE =>
            let
              val name = tm_prefix ^
                Int.toString (term_count tmdict)
              val tmdict = term_insert (tmdict, (ordinary_key (tm, 0)), name)
              val declaration = output_term_declaration regime name [] sort
              val tmdict = record_sorts
                (tmdict, ordinary_key (tm, 0), ([], sort))
            in
              ((tydict, tmdict), (typedecls @ [declaration], output_text name))
            end
      end
    fun translate_injected_string acc =
      let
        val string = carrier_dest_injected_string tm
      in
        case bound_peek (bounds, string) of
          SOME name => (acc, ([], output_text name))
        | NONE =>
          let
            val depends_on_bound =
              List.exists
                (fn v => Option.isSome (bound_peek (bounds, v)))
                (carrier_free_vars string)
            val _ =
              if depends_on_bound then
                raise ERR "translate_injected_string"
                  "non-atomic injected term depends on a bound variable"
              else
                ()
          in
            case term_peek (tmdict, (ordinary_key (tm, 0))) of
              SOME name => (acc, ([], output_text name))
            | NONE =>
              let
                val name =
                  tm_prefix ^ Int.toString (term_count tmdict)
                val tmdict = term_insert (tmdict, (ordinary_key (tm, 0)), name)
                val declaration =
                  output_term_declaration regime name [] "String"
              in
                ((tydict, tmdict), ([declaration], output_text name))
              end
          end
      end
    fun translate_injected_float acc =
      let
        val float = carrier_dest_injected_float tm
        val sort = metadata_smtfp_sort (carrier_type_of tm)
      in
        case bound_peek (bounds, float) of
          SOME _ =>
            raise ERR "translate_injected_float"
              "injected float binder was not transferred"
        | NONE =>
          let
            val depends_on_bound =
              List.exists
                (fn v => Option.isSome (bound_peek (bounds, v)))
                (carrier_free_vars float)
            val _ =
              if depends_on_bound then
                raise ERR "translate_injected_float"
                  "non-atomic injected term depends on a bound variable"
              else
                ()
          in
            case term_peek (tmdict, (ordinary_key (tm, 0))) of
              SOME name => (acc, ([], output_text name))
            | NONE =>
              let
                val name =
                  tm_prefix ^ Int.toString (term_count tmdict)
                val tmdict = term_insert (tmdict, (ordinary_key (tm, 0)), name)
                val declaration =
                  output_term_declaration regime name [] sort
              in
                ((tydict, tmdict), ([declaration], output_text name))
              end
          end
      end
    fun translate_injected_string_operation acc =
      let
        val (name, rands) = carrier_dest_injected_string_operation tm
        val (acc, declnames) = Lib.foldl_map
          (fn (a, t) =>
            translate (a, (bounds, t)))
          (acc, rands)
        val (declss, names) = Lib.split declnames
      in
        (acc, (List.concat declss, sexpr name names))
      end
    fun translate_lambda acc =
      let val (v, body) = carrier_dest_abs tm in
        emit_binder {head = "lambda", nest_errors = true} acc [v] body
      end
    fun eta_expand_ranked_constant acc applied rator rank rands_count =
      let
        fun drop 0 ty = ty
          | drop n ty = drop (n - 1) (Lib.snd (metadata_dom_rng ty))
        fun take_doms 0 _ acc = List.rev acc
          | take_doms n ty acc =
              let val (dom, rng) = metadata_dom_rng ty
              in take_doms (n - 1) rng (dom :: acc) end
        val residual_ty = drop rands_count (carrier_type_of rator)
        val missing_doms =
          take_doms (rank - rands_count) residual_ty []
        val vars = List.map carrier_genvar missing_doms
        val expanded = carrier_list_mk_abs
          (vars, carrier_list_mk_comb (applied, vars))
      in
        translate (acc, (bounds, expanded))
        handle DispatchFailure e => raise (#commit_error operations) e
      end
    fun constructor_info_for tydict ty constructor =
      let
        val type_name =
          case Redblackmap.peek (tydict, ty) of
            SOME name => name
          | NONE => raise ERR "translate_term" "datatype type not registered"
        val infos = metadata_constructor_infos ty type_name
      in
        case List.find (fn (constructor', _, _) =>
            carrier_same_const constructor constructor') infos of
          SOME info => info
        | NONE => raise ERR "translate_term" "constructor name not found"
      end
    fun translate_constructor_application acc rator rands =
      let
        val _ = carrier_is_constructor rator
        val (doms, data_ty) = metadata_strip_fun (carrier_type_of rator)
        val _ = not (metadata_datatype_excluded data_ty) orelse
          raise ERR "translate_term" "excluded datatype constructor"
        val arity = List.length doms
        val _ =
          if List.length rands = arity then ()
          else raise ERR "translate_term" "partial constructor application"
        val (((tydict, tmdict), typedecls), _) = ensure_type (acc, data_ty)
        val (_, cname, _) = constructor_info_for tydict data_ty rator
        val tmdict = term_insert (tmdict, (ordinary_key (rator, arity)), cname)
        val acc = (tydict, tmdict)
        val (acc, declnames) = Lib.foldl_map
          (fn (a, t) =>
            translate (a, (bounds, t)))
          (acc, rands)
        val (declss, names) = Lib.split declnames
      in
        (acc, (typedecls @ List.concat declss, sexpr cname names))
      end
    fun translate_selector_case acc =
      let
        val {constructor, selector_index, scrutinee} =
          case carrier_parser_case tm of
            SOME (CarrierSelector fields) => fields
          | _ => raise ERR "translate_term" "not a selector case"
        val data_ty = carrier_type_of scrutinee
        val (((tydict, tmdict), typedecls), _) =
          ensure_type (acc, data_ty)
        val type_name = Redblackmap.find (tydict, data_ty)
        val infos = metadata_constructor_infos data_ty type_name
        val selector_name =
          case List.find
              (fn (constructor', _, _) =>
                Term.same_const constructor constructor') infos of
            SOME (_, _, selectors) =>
              Lib.fst (List.nth (selectors, selector_index))
          | NONE => raise ERR "translate_term" "selector constructor missing"
        val acc = (tydict, tmdict)
        val (acc, (elemdecls, elemname)) =
          translate (acc, (bounds, scrutinee))
      in
        (acc, (typedecls @ elemdecls, sexpr selector_name [elemname]))
      end
    fun translate_tester_case acc =
      let
        val {constructor, scrutinee} =
          case carrier_parser_case tm of
            SOME (CarrierTester fields) => fields
          | _ => raise ERR "translate_term" "not a tester case"
        val data_ty = carrier_type_of scrutinee
        val (((tydict, tmdict), typedecls), _) = ensure_type (acc, data_ty)
        val type_name = Redblackmap.find (tydict, data_ty)
        val infos = metadata_constructor_infos data_ty type_name
        val constructor_name =
          case List.find
              (fn (constructor', _, _) =>
                Term.same_const constructor constructor') infos of
            SOME (_, name, _) => name
          | NONE => raise ERR "translate_term" "tester constructor missing"
        val acc = (tydict, tmdict)
        val (acc, (elemdecls, elemname)) =
          translate (acc, (bounds, scrutinee))
      in
        (acc, (typedecls @ elemdecls,
          sexpr ("(_ is " ^ constructor_name ^ ")") [elemname]))
      end
    fun translate_case_constant acc rator rands =
      let
        val (elem, cases) =
          case rands of
            elem :: cases => (elem, cases)
          | [] => raise ERR "translate_term" "case constant without scrutinee"
        val data_ty = carrier_type_of elem
        val tyinfo =
          case metadata_fetch data_ty of
            SOME info => info
          | NONE => raise ERR "translate_term" "case scrutinee not datatype"
        val _ =
          if carrier_same_const rator (metadata_case_const tyinfo) then ()
          else raise ERR "translate_term" "not datatype case constant"
        val _ =
          if List.length cases = List.length (metadata_constructors tyinfo)
          then ()
          else raise ERR "translate_term" "wrong number of case branches"
        val (((tydict, tmdict), typedecls), _) = ensure_type (acc, data_ty)
        val type_name = Redblackmap.find (tydict, data_ty)
        val infos = metadata_constructor_infos data_ty type_name
        fun selector_terms (constructor, _, selectors) =
          List.map (fn n => carrier_datatype_selector_term data_ty
            constructor n elem)
            (List.tabulate (List.length selectors, fn n => n))
        fun branch_term (casefn, info) =
          carrier_beta_reduce (carrier_list_mk_comb (casefn, selector_terms
            info))
        val branch_terms = ListPair.mapEq branch_term (cases, infos)
        val acc = (tydict, tmdict)
        val (acc, (elemdecls, elemname)) =
          translate (acc, (bounds, elem))
        val (acc, declbranches) = Lib.foldl_map
          (fn (a, t) =>
            translate (a, (bounds, t)))
          (acc, branch_terms)
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
    fun emit_native_candidate candidate =
      case candidate of
        NativeSequence input => native_sequence_builtin input
      | NativeSet input => native_set_builtin input
      | NativeBag input => native_bag_builtin input
      | NativeBuiltin input => builtin_symbol input
      | NativeEquality input => builtin_equality input
      | NativeBagCount (bag,element) =>
          let
            val (acc, (bag_decls, bag_name)) =
              translate (acc, (bounds, bag))
            val (acc, (element_decls, element_name)) =
              translate (acc, (bounds, element))
            val count = case !current_bag_backend of
                CVC5NativeBag => sexpr "bag.count" [element_name, bag_name]
              | _ => sexpr "select" [bag_name, element_name]
          in (acc, (bag_decls @ element_decls, count)) end
    fun has_semantic_function_prefix head rands =
      let
        fun loop _ [] = false
          | loop applied (rand :: rands) =
              let val applied = carrier_mk_comb (applied, rand)
              in
                (is_function_type (carrier_type_of applied) andalso
                 (carrier_is_case applied orelse
                  carrier_is_update_comb applied orelse
                  Option.isSome (carrier_builtin_encoding applied))) orelse
                loop applied rands
              end
      in
        loop head rands
      end
      handle DispatchFailure _ => false
    val tm_has_base_type = not (Lib.can Type.dom_rng (carrier_type_of tm))
    val _ =
      (case optional carrier_dest_comb tm of
         SOME (head, code) =>
           if carrier_known_const_matches smtstr_char_tm head then
             ignore
               (carrier_hexadecimal_string
                 "<builtin_symbols.smtstr_char>" code)
           else ()
       | NONE => ())
      handle DispatchFailure e => raise (#commit_error operations) e
    val literal = optional carrier_native_string_literal tm
  in
    case literal of
      SOME text => (acc, ([], output_text text))
    | NONE =>
    (* binders *)
    let
      val (binder, vars, body) =
        if carrier_is_forall tm then
          let val (vars, body) = carrier_strip_forall tm
          in ("forall", vars, body) end
        else if carrier_is_exists tm then
          let val (vars, body) = carrier_strip_exists tm
          in ("exists", vars, body) end
        else
          raise ERR "translate_term" "not a binder"
    in
      emit_binder {head = binder, nest_errors = true} acc vars body
    end
    handle DispatchFailure _ =>

    (* let binder - somewhat similar to quantifiers *)
    let
      val (bindings, body) = carrier_dest_let tm
      val (vars, bodies) = ListPair.unzip bindings
      (* we should translate the bodies without first creating the bound
        names *)
      val bounds_bodies = List.map (fn body => (bounds, body)) bodies
      val (acc, decls_bodies) =
        Lib.foldl_map
          (fn (a, bound_body) =>
            translate (a, bound_body))
          (acc, bounds_bodies)
      (* now we can create the bound names *)
      val (bounds, smtvars) = Lib.foldl_map create_bound_name (bounds, vars)
      val decls_bodies_smtvars = ListPair.zipEq (decls_bodies, smtvars)
      val (decls, smtbinds) = List.foldl (fn (((d, b), v), (decls,
        smtbinds)) =>
        (d @ decls,
         output_concat [output_text ("(" ^ v ^ " "), b, output_text ")"] ::
           smtbinds)) ([], [])
          decls_bodies_smtvars
      val bindings = output_join " " (List.rev smtbinds)
      val (acc, (bodydecls, body)) =
        translate_body (acc, (bounds, body))
    in
      (acc, (decls @ bodydecls,
        output_concat
          [output_text "(let (", bindings, output_text ") ", body,
           output_text ")"]))
    end
    handle DispatchFailure _ =>

    (* bound variables may shadow built-in symbols etc. *)
    (acc, ([], output_text (bound_find (bounds, tm))))
    handle Redblackmap.NotFound =>

    (* Each str_inj image is generalized to an SMT String value.  Proving the
       strengthened SMT formula over every Unicode string and then using the
       tactic validation at this image is the sound direction. *)
    (if carrier_is_injected_string tm then
       translate_injected_string acc
       handle DispatchFailure e => raise (#commit_error operations) e
     else
       raise ERR "translate_term" "not an injected string")
    handle e as NestedTranslation _ => raise e
         | DispatchFailure _ =>

    (* Each smtfp_intro image is generalized to an SMT FloatingPoint value.
       The carrier theorem proves surjectivity, while the preprocessing
       homomorphisms ensure that only intro-invariant native operations reach
       this branch. *)
    (if carrier_is_injected_float tm then
       translate_injected_float acc
       handle DispatchFailure e => raise (#commit_error operations) e
     else
       raise ERR "translate_term" "not an injected float")
    handle e as NestedTranslation _ => raise e
         | DispatchFailure _ =>

    (* Terms produced by HOL_STRING_TO_SMT_CONV use this transfer-specific
       path.  Dedicated smtstr terms use the ordinary builtin table above. *)
    (if carrier_is_injected_string_operation tm then
       translate_injected_string_operation acc
       handle DispatchFailure e => raise (#commit_error operations) e
     else
       raise ERR "translate_term" "not an injected string operation")
    handle e as NestedTranslation _ => raise e
         | DispatchFailure _ =>

    (* A closed partial-destructor residue is one fixed HOL value.  Emit the
       whole residual as a reusable zero-arity symbol; never decompose it into
       a function whose domain is the native datatype/sequence sort. *)
    (if carrier_closed_constructor_destructor_residual tm then
       translate_closed_destructor_residual acc
       handle DispatchFailure e => raise (#commit_error operations) e
     else
       raise ERR "translate_term" "not a closed destructor residue")
    handle e as NestedTranslation _ => raise e
         | DispatchFailure _ =>

    (* cvc5 parses a bag literal as a lambda, but retransmission must retain
       the Bag operation rather than send that lambda to Array consumers. *)
    (if carrier_is_parsed_bag_literal tm then translate_parsed_bag_literal acc
     else
       case regime of
         FirstOrder => raise ERR "translate_term" "not first-order"
       | HigherOrder _ => translate_lambda acc)
    handle DispatchFailure _ =>

    (* translate the entire term (e.g., for numerals), using the dictionary of
       built-in symbols; however, only do this if 'tm' has base type *)
    emit_native_candidate
      ((#whole_candidate native_dispatch) tm_has_base_type tm)
    handle DispatchFailure _ =>

    (* split the term into rator and rands *)
    let
      val (rator, rands) = carrier_strip_comb tm
    in
      (* In an HO regime a fully ranked built-in may itself return a map.
         Translate that ranked prefix before any remaining map applications. *)
      emit_native_candidate ((#application_candidate native_dispatch)
        tm_has_base_type tm rator rands)
    handle DispatchFailure _ =>

      translate_constructor_application acc rator rands
    handle DispatchFailure _ =>

      translate_selector_case acc
    handle DispatchFailure _ =>

      translate_tester_case acc
    handle DispatchFailure _ =>

      translate_case_constant acc rator rands
    handle DispatchFailure _ =>

      (* FO functions and the Z3 dialect are arrays.  Standard 2.7 maps have
         no store operator, so preserve HOL UPDATE with a native lambda. *)
      let
        val ((index, value), array) = carrier_dest_update_comb tm
      in
        case regime of
          HigherOrder Standard27 =>
            let
              val v = carrier_genvar (carrier_type_of index)
              val (lambda_bounds, smtvar) = create_bound_name (bounds, v)
              val (((tydict, tmdict), typedecls), tyname) =
                ensure_type (acc, carrier_type_of v)
              val old_value = carrier_mk_comb (array, v)
              val (acc, (arraydecls, oldname)) =
                translate_body
                  ((tydict, tmdict), (lambda_bounds, old_value))
              val (acc, (indexdecls, indexname)) =
                translate (acc, (bounds, index))
              val (acc, (valuedecls, valuename)) =
                translate (acc, (bounds, value))
              val body = sexpr "ite"
                [sexpr "=" [output_text smtvar, indexname], valuename, oldname]
            in
              (acc, (typedecls @ arraydecls @ indexdecls @ valuedecls,
                output_concat
                  [output_text ("(lambda ((" ^ smtvar ^ " " ^ tyname ^ ")) "),
                   body, output_text ")"]))
            end
        | _ =>
            let
              val (acc, (arraydecls, arrayname)) =
                translate (acc, (bounds, array))
              val (acc, (indexdecls, indexname)) =
                translate (acc, (bounds, index))
              val (acc, (valuedecls, valuename)) =
                translate (acc, (bounds, value))
            in
              (acc, (arraydecls @ indexdecls @ valuedecls,
                sexpr "store" [arrayname, indexname, valuename]))
            end
      end
    handle DispatchFailure _ =>

      let
        val (function, argument) = carrier_dest_comb tm
        (* Defer curried applications with native collection arguments to the
           full-application path, which retains every declaration sort. *)
        val _ =
          if carrier_is_var rator andalso List.length rands > 1 andalso
             ((!current_set_backend = CVC5NativeSet andalso
               List.exists carrier_is_marked_set_term rands) orelse
              (!current_bag_backend = CVC5NativeBag andalso
               List.exists carrier_is_marked_bag_term rands))
          then raise ERR "translate_term" "native collection application"
          else ()
        val _ = metadata_dom_rng (carrier_type_of function)
        val native_set_argument =
          !current_set_backend = CVC5NativeSet andalso
          carrier_is_marked_set_term argument
        val native_bag_argument =
          !current_bag_backend = CVC5NativeBag andalso
          carrier_is_marked_bag_term argument
        val native_collection_argument =
          carrier_is_var function andalso
          (native_set_argument orelse native_bag_argument)
        val _ =
          if !current_bag_backend = CVC5NativeBag andalso
             carrier_is_marked_bag_term function andalso
             carrier_is_raw_number tm then
            raise (#commit_error operations)
              ((#syntax_error operations) "translate_term"
              "native cvc5 bag.count requires an Int coercion")
          else ()
        val semantically_ranked_partial =
          carrier_is_const rator andalso
          let val rank = carrier_declared_const_arity rator
          in
            List.length rands < rank andalso
            carrier_has_ranked_semantics rator
          end
        val symbol_head =
          (carrier_is_const rator orelse carrier_is_var rator) andalso
          (semantically_ranked_partial orelse
           not (has_semantic_function_prefix rator rands))
        val _ =
          case regime of
            HigherOrder Standard27 =>
              if symbol_head then
                raise ERR "translate_term" "symbol-headed application"
              else
                ()
          | _ =>
              if carrier_is_const rator andalso
                 not (carrier_is_update_comb function) then
                (case regime of
                   FirstOrder =>
                     raise ERR "translate_term"
                       "HOL constants are emitted as functions"
                 | HigherOrder _ =>
                     if List.length rands >
                          carrier_declared_const_arity rator orelse
                        has_semantic_function_prefix rator rands then
                       ()
                     else
                       raise ERR "translate_term"
                         "ranked HOL constant application")
              else
                ()
        val (acc, (functiondecls, functionname)) =
          if native_collection_argument then
            (case term_peek (tmdict, (ordinary_key (function, 1))) of
               SOME name => (acc, ([], output_text name))
             | NONE =>
                 let
                   val (_, range) = metadata_dom_rng (carrier_type_of function)
                   val (tydict, (domdecls, domain_sort)) =
                     if native_set_argument then selected_set_sort tydict
                       argument
                     else selected_bag_sort tydict argument
                   val (tydict, (rngdecls, range_sort)) =
                     metadata_translate_type regime (tydict, range)
                   val name = tm_prefix ^
                     Int.toString (term_count tmdict)
                   val tmdict = term_insert
                     (tmdict, (ordinary_key (function, 1)), name)
                   val declaration = output_term_declaration regime name
                     [domain_sort] range_sort
                   val tmdict = record_sorts
                     (tmdict, ordinary_key (function, 1),
                      ([domain_sort], range_sort))
                 in
                   ((tydict, tmdict),
                    (domdecls @ rngdecls @ [declaration], output_text name))
                 end)
          else
            translate (acc, (bounds, function))
            handle DispatchFailure e => raise (#commit_error operations) e
        val (acc, (argumentdecls, argumentname)) =
          translate (acc, (bounds, argument))
          handle DispatchFailure e => raise (#commit_error operations) e
      in
        (acc, (functiondecls @ argumentdecls,
          if native_collection_argument then
            expression_application functionname [argumentname]
          else if !current_set_backend = CVC5ArraySet andalso
                  carrier_is_marked_set_term function then
            sexpr "select" [functionname, argumentname]
          else if !current_bag_backend = CVC5ArrayBag andalso
                  carrier_is_marked_bag_term function then
            sexpr "select" [functionname, argumentname]
          else
            case !current_set_backend of
              CVC5NativeSet =>
                if carrier_is_marked_set_term function then
                  sexpr "set.member" [argumentname, functionname]
                else if !current_bag_backend = CVC5NativeBag andalso
                        carrier_is_marked_bag_term function then
                  sexpr "bag.count" [argumentname, functionname]
                else explicit_apply functionname argumentname
            | _ =>
                if !current_bag_backend = CVC5NativeBag andalso
                   carrier_is_marked_bag_term function then
                  sexpr "bag.count" [argumentname, functionname]
                else explicit_apply functionname argumentname))
      end
    handle DispatchFailure _ =>

      let
        val rands_count = List.length rands
        val _ =
          if carrier_is_const rator orelse carrier_is_var rator then ()
          else
            raise ERR "translate_term"
              ("unsupported higher-order rator expression: " ^
               carrier_term_to_string rator)
        val declaration_arity =
          case regime of
            FirstOrder => rands_count
          | HigherOrder _ =>
              if carrier_is_const rator then carrier_declared_const_arity
                rator else 0
      in
        if declaration_arity > rands_count andalso
           (regime = HigherOrder Z3LambdaArray orelse
            regime = HigherOrder Standard27 andalso
              carrier_has_ranked_semantics rator) then
          eta_expand_ranked_constant acc tm rator declaration_arity
            rands_count
        else
          let
            (* All preceding rungs preserve official SMT operators,
               constructors, carrier injections, and ranked eta expansion.
               Only the generic invented-symbol boundary is closed here. *)
            val _ = carrier_reject_unsupported_smtfloat_constant rator
            val (acc, (decls, name)) =
              (* A function-valued binder is a symbol head too. *)
              (acc, ([], bound_find (bounds, rator)))
              handle Redblackmap.NotFound =>
              (* translate the rator as a previously defined symbol *)
              (acc, ([], term_find
                (tmdict, (ordinary_key (rator, declaration_arity)))))
              handle Redblackmap.NotFound =>

              (* translate the rator as a new (i.e., uninterpreted) symbol *)
              let
                (* translate 'rator' types required for the rator's
                   SMT-LIB declaration *)
                fun doms_rng acc 0 ty =
                  (List.rev acc, ty)
                  | doms_rng acc n ty =
                  let
                    val (dom, rng) = metadata_dom_rng ty
                  in
                    doms_rng (dom :: acc) (n - 1) rng
                  end
                (* In the HO regime constants use their declared rank, not
                   their occurrence arity.  This canonical key prevents
                   partial and full applications from splitting one symbol. *)
                val (domtys, rngty) = doms_rng [] declaration_arity
                  (carrier_type_of rator)
                (* A native collection argument determines the corresponding
                   declaration position.  Translating its HOL function type
                   alone would otherwise erase the selected Set/Bag sort. *)
                fun translate_domain (tydict, (index, ty)) =
                  let
                    val argument =
                      if index < List.length rands then
                        SOME (List.nth (rands, index))
                      else carrier_contextual_collection_argument rator index
                  in
                    case argument of
                      SOME arg =>
                        if carrier_is_marked_set_term arg then
                          selected_set_sort tydict arg
                        else if carrier_is_marked_bag_term arg then
                          selected_bag_sort tydict arg
                        else
                          metadata_translate_type regime (tydict, ty)
                    | NONE => metadata_translate_type regime (tydict, ty)
                  end
                val (tydict, domdecltys) =
                  Lib.foldl_map translate_domain (tydict,
                    ListPair.zip (List.tabulate (List.length domtys, Lib.I),
                      domtys))
                val _ = carrier_reject_invented_native_datatype_domain rator
                  domtys
                val (domdeclss, domtys) = Lib.split domdecltys
                val domdecls = List.concat domdeclss
                fun translate_variable_function_type (tydict, index, ty) =
                  if Type.compare (ty, carrier_type_of tm) = EQUAL andalso
                     carrier_is_marked_set_term tm then
                    selected_set_sort tydict tm
                  else if Type.compare (ty, carrier_type_of tm) = EQUAL andalso
                          carrier_is_marked_bag_term tm then
                    selected_bag_sort tydict tm
                  else
                    case Lib.total Type.dom_rng ty of
                      SOME (domain, range) =>
                        let
                          val (tydict, (ddecls, dsort)) =
                            translate_domain (tydict, (index, domain))
                          val (tydict, (rdecls, rsort)) =
                            translate_variable_function_type
                              (tydict, index + 1, range)
                        in
                          (tydict, (ddecls @ rdecls,
                            "(-> " ^ dsort ^ " " ^ rsort ^ ")"))
                        end
                    | NONE => metadata_translate_type regime (tydict, ty)
                val (tydict, (rngdecls, rngty)) =
                  if declaration_arity = 0 andalso
                     (case regime of
                        HigherOrder Standard27 =>
                          carrier_is_var rator andalso
                          (carrier_is_marked_set_term tm orelse
                           carrier_is_marked_bag_term tm orelse
                           carrier_has_contextual_collection_argument rator
                             orelse
                           List.exists (fn argument =>
                             carrier_is_marked_set_term argument orelse
                             carrier_is_marked_bag_term argument) rands)
                      | _ => false) then
                    translate_variable_function_type
                      (tydict, 0, carrier_type_of rator)
                  else if carrier_is_marked_set_term tm then
                    selected_set_sort tydict tm
                  else if carrier_is_marked_bag_term tm then
                    selected_bag_sort tydict tm
                  else
                    metadata_translate_type regime (tydict, rngty)
                (* invent new name for 'rator' *)
                val name = tm_prefix ^
                  Int.toString (term_count tmdict)
                val _ = if !Library.trace > 0 andalso carrier_is_const rator
                  then
                  WARNING "translate_term"
                    ("uninterpreted constant " ^ carrier_term_to_string rator)
                  else
                    ();
                val _ = if !Library.trace > 2 then
                    Feedback.HOL_MESG
                      ("HolSmtLib (SmtLib): inventing name '" ^ name ^
                       "' for HOL term '" ^ carrier_term_to_string rator ^
                       "' (declared at rank " ^
                       Int.toString declaration_arity ^ ")")
                  else
                    ()
                val tmdict = term_insert
                  (tmdict, (ordinary_key (rator, declaration_arity)), name)
                val decl =
                  output_term_declaration regime name domtys rngty
                val tmdict = record_sorts
                  (tmdict, ordinary_key (rator, declaration_arity),
                   (domtys, rngty))
              in
                ((tydict, tmdict),
                 (domdecls @ rngdecls @ [decl], name))
              end
            (* translate 'rands' *)
            val (acc, declnames) = Lib.foldl_map
              (fn (a, t) =>
                translate (a, (bounds, t)))
              (acc, rands)
            val (declss, names) = Lib.split declnames
          in
            (acc, (decls @ List.concat declss,
              case regime of
                HigherOrder Standard27 =>
                  if carrier_is_var rator andalso
                     (carrier_is_marked_set_term tm orelse
                      carrier_is_marked_bag_term tm orelse
                      List.exists (fn argument =>
                        carrier_is_marked_set_term argument orelse
                        carrier_is_marked_bag_term argument) rands) andalso
                     not (Option.isSome
                       (bound_peek (bounds, rator))) then
                    List.foldl (fn (argument, function) =>
                      explicit_apply function argument)
                      (output_text name) names
                  else sexpr name names
              | _ => sexpr name names))
          end
      end
    end
  end
  handle DispatchFailure primary => raise primary
  end

  (* Lexical BODY entry is explicit even when the body reuses the same
     bound variable IDs and names. Ordinary children, including LET RHS,
     remain in the incoming lexical region. The legacy continuation is
     identical at both kinds of recursive call. *)
  fun translate_term_step_with_scoped_output output seal operations store
      translate regime apply_operator input =
    translate_term_step_with_lexical_output output seal operations store
      translate translate regime apply_operator input

  (* Generated definitions are global commands. A graph instance closes
     their expression references INSIDE their own quantified dependencies;
     unrelated definitions or enclosing lexical names must not escape.
     The string instance has no local reference graph to close. *)
  fun translate_term_step_with_output output operations store translate
      regime apply_operator input =
    translate_term_step_with_scoped_output output
      (fn (_,document) => document) operations store translate
      regime apply_operator input

  fun translate_term_step_with_carrier operations store translate regime
      apply_operator input =
    translate_term_step_with_output string_output_operations operations
      store translate regime apply_operator input

  fun translate_term_step_with_store store translate regime
      apply_operator input =
    translate_term_step_with_carrier term_translation_operations store
      translate regime apply_operator input

  fun translate_term_step translate regime apply_operator input =
    translate_term_step_with_store legacy_term_store_operations translate
      regime apply_operator input

  fun translate_term regime apply_operator input =
    translate_term_step (translate_term regime apply_operator)
      regime apply_operator input

  datatype datatype_case_scan =
      NotDatatypeCase
    | DatatypeCase of string option

  fun first_reason scan [] = NONE
    | first_reason scan (tm :: tms) =
      (case scan tm of
         SOME reason => SOME reason
       | NONE => first_reason scan tms)

  (* Report higher-order shapes that the first-order translator rejects or
     would encode without preserving a built-in's semantics.  Binder, let,
     datatype-case, and update abstractions are encoding scaffolding rather
     than first-class function values. *)
  type 'term regime_operations =
    {syntax:'term term_translation_operations,
     is_abstraction:'term -> bool,
     constant_name:'term -> string * string,
     datatype_case:'term ->
       {scrutinee:'term,clauses:((unit -> 'term list) * 'term) list} option,
     is_syntax_error:exn -> bool,
     is_optional_error:exn -> bool,
     memoize:'term list -> 'term -> (unit -> string option) -> string option}

  fun goal_ho_reason_with (algebra:'term regime_operations) =
    let
      val {syntax,is_abstraction,constant_name,datatype_case,
           is_syntax_error,is_optional_error,memoize} = algebra
      val {type_of,is_var,is_const,dest_comb,dest_abs,strip_comb,list_mk_comb,
           same_const,declared_const_arity,aconv,is_forall,is_exists,dest_let,
           dest_update_comb,metadata_error,...} = syntax
      fun optional thunk = SOME (thunk ()) handle primary =>
        if is_optional_error primary then NONE else raise primary
      (* Native Lib.total probes and HOL_ERR-only shape probes have distinct
         exception policies; graph probes admit only private mismatches. *)
      fun syntax_optional thunk = SOME (thunk ()) handle primary =>
        if is_syntax_error primary then NONE else raise primary
      fun metadata thunk = thunk ()
        handle primary as Feedback.HOL_ERR _ => raise metadata_error primary
      fun function_valued_conditional current =
        case syntax_optional (fn () =>
          let
            val (head,arguments) = strip_comb current
            val conditional = case arguments of test::left::right::_ =>
                list_mk_comb (head,[test,left,right])
              | _ => raise (#syntax_error syntax) "goal_ho_reason"
                  "partial conditional"
          in same_const head boolSyntax.conditional andalso
            is_function_type (type_of conditional) end) of
          SOME result => result | NONE => false
      fun case_reason scan inherited current =
        (case datatype_case current of
           NONE => NotDatatypeCase
         | SOME {scrutinee,clauses} =>
             let fun clause (variables,body) =
                   let val selectors = List.filter
                         (is_function_type o type_of) (variables ())
                   in scan (selectors @ inherited) body end
             in DatatypeCase (case scan inherited scrutinee of
                  SOME reason => SOME reason
                | NONE => Lib.get_first clause clauses) end)
        handle primary =>
          if is_syntax_error primary then NotDatatypeCase else raise primary
      fun record_update current = syntax_optional (fn () =>
        let
          val (prefix,record) = dest_comb current
          val (update,updater) = dest_comb prefix
          fun dest_k term =
            let val (head,value) = dest_comb term in
              if same_const head combinSyntax.K_tm then value else
                raise (#syntax_error syntax) "goal_ho_reason"
                  "not record update"
            end
          val value = case syntax_optional (fn () => dest_k updater) of
              SOME value => value
            | NONE =>
                let val (variable,body) = dest_abs updater
                    val (function,argument) = dest_comb body
                    val _ = if aconv variable argument then () else
                      raise (#syntax_error syntax) "goal_ho_reason"
                        "not record update"
                in dest_k function end
          val record_ty = type_of record val value_ty = type_of value
          val fields = metadata (fn () => TypeBase.fields_of record_ty)
          fun matches (_, {ty,fupd,...}:TypeBasePure.rcd_fieldinfo) =
            same_const update fupd andalso
            metadata (fn () => Lib.can (Type.match_type ty) value_ty)
          val _ = case List.find matches fields of SOME _ => ()
            | NONE => raise (#syntax_error syntax) "goal_ho_reason"
                "not record update"
        in [record,value] end)
      fun sequence_ho current =
        case optional (fn () => strip_comb current) of
          SOME (head,_) => same_const head seq_map_tm orelse
            same_const head seq_foldl_tm
        | NONE => false
      fun partial_ranked head arguments = is_const head andalso
        let val (theory,name) = constant_name head in
          length arguments < declared_const_arity head andalso
          Redblackset.member (builtin_const_names,(theory,name)) end
      fun scan inherited current = memoize inherited current (fn () =>
        if sequence_ho current then SOME "automatic:seq-ho-combinator"
        else if is_forall current then
          scan inherited (#2 (dest_abs (#2 (dest_comb current))))
        else if is_exists current then
          scan inherited (#2 (dest_abs (#2 (dest_comb current))))
        else case optional (fn () => dest_let current) of
          SOME (bindings,body) => first_reason (scan inherited)
            (List.map #2 bindings @ [body])
        | NONE =>
            if function_valued_conditional current then
              SOME "automatic:function-valued-conditional"
            else case case_reason scan inherited current of
              DatatypeCase reason => reason
            | NotDatatypeCase =>
                (case optional (fn () => dest_update_comb current) of
                   SOME ((index,value),array) =>
                     first_reason (scan inherited) [array,index,value]
                 | NONE => (case record_update current of
                     SOME operands => first_reason (scan inherited) operands
                   | NONE =>
                       if is_abstraction current then
                         SOME "automatic:surviving-abstraction"
                       else case optional (fn () => strip_comb current) of
                         SOME (head,arguments) =>
                           if List.exists (aconv head) inherited then
                             SOME
                               "automatic:non-constant/non-variable-rator"
                           else if partial_ranked head arguments then
                             SOME "automatic:partial-ranked-builtin"
                           else if is_const head orelse is_var head then
                             first_reason (scan inherited) arguments
                           else SOME
                             "automatic:non-constant/non-variable-rator"
                       | NONE => NONE)))
    in fn (assumptions,goal) =>
      first_reason (scan []) (assumptions @ [goal]) end

  val term_regime_operations : Term.term regime_operations =
    {syntax=term_translation_operations,is_abstraction=Term.is_abs,
     constant_name=fn current =>
       let val {Thy,Name,...} = Term.dest_thy_const current in (Thy,Name) end,
     datatype_case=fn current =>
       let val (_,scrutinee,clauses) = TypeBase.dest_case current in
         SOME {scrutinee=scrutinee,clauses=List.map (fn (pattern,body) =>
           (fn () => #2 (boolSyntax.strip_comb pattern),body)) clauses} end,
     is_syntax_error=fn Feedback.HOL_ERR _ => true | _ => false,
     is_optional_error=fn Portable.Interrupt => false | _ => true,
     memoize=fn _ => fn _ => fn compute => compute ()}
  val goal_ho_reason = goal_ho_reason_with term_regime_operations

  fun goal_requires_ho_aux goal = Option.isSome (goal_ho_reason goal)

  datatype regime_request =
      AutomaticRegime of ho_dialect
    | RegimeOverride of regime

  fun select_regime_with algebra request goal =
    case request of
      RegimeOverride regime => (regime, "explicit override")
    | AutomaticRegime dialect =>
        (case goal_ho_reason_with algebra goal of
           NONE => (FirstOrder, "automatic:no-ho-trigger")
         | SOME reason => (HigherOrder dialect, reason))
  val select_regime = select_regime_with term_regime_operations

  (* Returns the selected translation and SMT-LIB text for the input goal;
     the conclusion is negated before emission.  A term-dictionary integer is
     the occurrence arity in FirstOrder.  HigherOrder uses a constant's
     declared rank, or zero for a function-valued variable, so partial and
     full applications share one symbol. *)
  (* Native and graph query boundaries use the same final logic policy. *)
  fun outbound_select_logic regime (policy:logic_selection_policy) features =
    let
      val (feature_logic, feature_reason) =
        infer_logic_from_features_for_regime regime features
      (* Z3's array-lambda extension is accepted uniformly under ALL, while
       narrower FO array logics reject lambda as quantified syntax on some
       supported Z3 versions.  The C1 replay corpus also uses ALL, so keeping
       that logic in the translation record gives proof parsing the same broad
       dictionaries as the solver.  Caller overrides still take precedence. *)
      val (inferred_logic, reason) =
        case regime of
          HigherOrder Z3LambdaArray =>
            ("ALL", "Z3 array-lambda lowering requires logic ALL; " ^
              feature_reason)
        | _ => (feature_logic, feature_reason)
      val (selected_logic, reason) =
        case policy {features = features, inferred_logic = inferred_logic,
                     reason = reason} of
          NONE => (inferred_logic, reason)
        | SOME {logic, reason} => (logic, reason)
    in {logic=selected_logic,reason=reason} end

  (* Only command assembly is parameterized. Semantic translation remains
     the existing shared dispatcher; declarations stay interleaved with
     their assertion, with identical native chunk and byte order. *)
  fun outbound_query_script (output:'doc output_operations)
      {logic,assertions:('doc list * 'doc) list} =
    let val text = #text output val concat = #concat output
        fun assertion (declarations,expression) = declarations @
          [concat [text "(assert ",expression,text ")\n"]]
    in [text ("(set-logic " ^ logic ^ ")\n"),
      text ("(set-info :source |Automatically generated from HOL4 by " ^
        "SmtLib.goal_to_SmtLib.\n"),
      text "Copyright (c) 2011 Tjark Weber. All rights reserved.|)\n",
      text "(set-info :smt-lib-version 2.7)\n"] @
      List.concat (List.map assertion assertions) @ [text "(check-sat)\n"]
    end

  fun outbound_query_tail (output:'doc output_operations) get_proof =
    let val text = #text output in
      if get_proof then [text "(get-proof)\n",text "(exit)\n"]
      else [text "(exit)\n"] end

  fun goal_to_SmtLib_aux_inner request apply_operator
      (policy : logic_selection_policy) target emit_sequences
      (goal as (original_ts, t)) : translation * string list =
  let
    val _ = current_native_sequence_emission := emit_sequences
    val _ = current_generated_forall_emissions := 0
    val _ = emitted_term_sorts := []
    val {sets = set_terms, bags = bag_terms} =
      collect_query_collection_markers (t :: original_ts)
    (* Num is an Int-valued SMT abs only beneath its integer coercion.  In an
       opaque HOL-num position it must remain an uninterpreted function. *)
    val raw_num_terms = SmtLib_RawNumAnalysis.collect
      raw_num_operations bag_terms (t :: original_ts)
    (* A symbol has one fixed SMT domain sort.  A collection argument is
       ambiguous only if that same function position is also used as an
       ordinary array argument. *)
    val subterms = List.concat (List.map Library.subterms (t :: original_ts))
    val collection_operations :
        Term.term SmtLib_CollectionApplicationAnalysis.operations =
      {same = fn (left, right) => Term.aconv left right,
       type_of = Term.type_of,
       is_variable = Term.is_var,
       is_constant = Term.is_const,
       declared_const_arity = declared_const_arity,
       strip_comb = boolSyntax.strip_comb,
       dest_comb = Term.dest_comb,
       is_abstraction = Term.is_abs,
       dest_abs = Term.dest_abs,
       free_variables = Term.free_vars}
    val computed_set_applications =
      SmtLib_CollectionApplicationAnalysis.computed_applications
        collection_operations set_terms subterms
    val computed_bag_applications =
      SmtLib_CollectionApplicationAnalysis.computed_applications
        collection_operations bag_terms subterms
    fun has_mixed_collection_argument collection_terms =
      SmtLib_CollectionApplicationAnalysis.has_mixed_argument
        collection_operations collection_terms subterms
    (* Keep lexical binder context separate from the supplied inventory. *)
    fun bound_collection_application collection_terms =
      SmtLib_CollectionApplicationAnalysis.has_bound_application
        collection_operations collection_terms (t :: original_ts)
    val {set_backend=backend,bag_backend} =
      (#select term_backend_selection) target
        {goal=goal,sets=set_terms,bags=bag_terms,
         computed_set=not (List.null computed_set_applications),
         computed_bag=not (List.null computed_bag_applications),
         bound_set=fn () => bound_collection_application set_terms,
         bound_bag=fn () => bound_collection_application bag_terms,
         mixed_set=fn () => has_mixed_collection_argument set_terms,
         mixed_bag=fn () => has_mixed_collection_argument bag_terms}
    val _ = current_set_backend := backend
    val _ = current_set_terms := set_terms
    val _ = current_raw_num_terms := raw_num_terms
    val _ = current_bag_backend := bag_backend
    val _ = current_bag_terms := bag_terms
    val _ = current_collection_function_arguments :=
      computed_set_applications @ computed_bag_applications
    val _ = current_bag_helpers := []
    (* FINITE hypotheses are the evidence selecting cvc5's finite Set/Bag
       models; once selected they are semantic facts of those models and must
       not be serialized as unsupported HOL predicates. *)
    val finite_sets = List.mapPartial finite_set_hypothesis original_ts
    val finite_bags = List.mapPartial finite_bag_hypothesis original_ts
    (* In cvc5's native finite collection models, finiteness evidence is a
       semantic fact, including beneath Boolean connectives. *)
    fun replace_finite tm =
      case finite_set_hypothesis tm of
        SOME set =>
          if backend = CVC5NativeSet andalso finite_set_term finite_sets set
          then boolSyntax.T else descend tm
      | NONE =>
          (case finite_bag_hypothesis tm of
             SOME bag =>
               if bag_backend = CVC5NativeBag andalso
                  finite_bag_term finite_bags bag then boolSyntax.T
               else descend tm
           | NONE => descend tm)
    and descend tm =
      if Term.is_comb tm then
        let val (rator, rand) = Term.dest_comb tm
        in Term.mk_comb (replace_finite rator, replace_finite rand) end
      else if Term.is_abs tm then
        let val (var, body) = Term.dest_abs tm
        in Term.mk_abs (var, replace_finite body) end
      else tm
    val ts = List.map replace_finite (List.filter (fn tm =>
      not (backend = CVC5NativeSet andalso
           Option.isSome (finite_set_hypothesis tm)) andalso
      not (bag_backend = CVC5NativeBag andalso
           Option.isSome (finite_bag_hypothesis tm))) original_ts)
    val t = replace_finite t
    val (regime, regime_reason) = select_regime request (ts, t)
    val tydict = Redblackmap.mkDict Type.compare
    val tmdict = Redblackmap.mkDict
      (Lib.pair_compare (Term.compare, Int.compare))
    val bounds = Redblackmap.mkDict Term.compare
    val terms = ts @ [boolSyntax.mk_neg t]
    val _ = reject_uninterpreted_native_destructors terms
    val (acc, smtlibs) = Lib.foldl_map
      (fn (acc, tm) =>
        translate_term regime apply_operator (acc, (bounds, tm)))
      ((tydict, tmdict), terms)
      handle NestedTranslation e => raise e
    val (tydict, tmdict) = acc
    val features =
      infer_features regime terms tydict tmdict
    val {logic=selected_logic,reason} =
      outbound_select_logic regime policy features
    (* Metadata is public lazily, so retain the query's collection state for
       its eventual construction instead of consulting the restored ambient
       state. *)
    val record_sequence_emission = !current_native_sequence_emission
    val record_generated_forall_emissions =
      !current_generated_forall_emissions
    val record_set_backend = !current_set_backend
    val record_bag_backend = !current_bag_backend
    val record_emitted_term_sorts = !emitted_term_sorts
    fun records () =
      let
        val restorers = [
          save_cell current_backend_installation,
          save_cell current_native_sequence_emission,
          save_cell current_generated_forall_emissions,
          save_cell current_set_backend,
          save_cell current_bag_backend,
          save_cell emitted_term_sorts
        ]
        fun work () =
          (current_backend_installation := NONE;
           current_native_sequence_emission := record_sequence_emission;
           current_generated_forall_emissions :=
             record_generated_forall_emissions;
           current_set_backend := record_set_backend;
           current_bag_backend := record_bag_backend;
           emitted_term_sorts := record_emitted_term_sorts;
           build_translation_records regime regime_reason terms
             selected_logic reason features tydict tmdict)
        fun restore () = restore_cells restorers
      in
        Portable.finally restore work ()
      end
    val translation = {logic = selected_logic, regime = regime,
      tydict = tydict, tmdict = tmdict, records = records}
  in
    (translation,outbound_query_script string_output_operations
      {logic=selected_logic,assertions=smtlibs})
  end

  fun with_saved_translation_context work =
  let
    val restorers = [
      save_cell current_backend_installation,
      save_cell current_native_sequence_emission,
      save_cell current_generated_forall_emissions,
      save_cell emitted_term_sorts,
      save_cell current_set_backend,
      save_cell current_set_terms,
      save_cell current_raw_num_terms,
      save_cell current_bag_backend,
      save_cell current_bag_terms,
      save_cell current_bag_helpers,
      save_cell current_collection_function_arguments
    ]
    fun restore () = restore_cells restorers
  in
    Portable.finally restore
      (fn () => (current_backend_installation := NONE;work ())) ()
  end

  type backend_context_options =
    {sequence_emission:bool,set_backend:set_backend,bag_backend:bag_backend,
     has_set_terms:bool,has_bag_terms:bool}
  type backend_snapshot =
    {sequence_emission:bool,set_backend:set_backend,bag_backend:bag_backend,
     generated_forall:bool,has_set_terms:bool,has_bag_terms:bool}
  type backend_context =
    {state:feature_state,snapshot:unit -> backend_snapshot,
     translate_type:regime ->
       (Type.hol_type,string) Redblackmap.dict * Type.hol_type ->
       (Type.hol_type,string) Redblackmap.dict * (string list * string),
     sort_of_type:regime -> (Type.hol_type,string) Redblackmap.dict ->
       Type.hol_type -> string}

  (* The store, dispatcher and metadata producer run inside one fixed
     installation. No raw marker Terms are fabricated for graph syntax.
     Returned scalar snapshots are DATA; guarded operations cannot escape
     this installation or consult a later query's restored ambient state. *)
  fun with_backend_context (options:backend_context_options)
      (action:backend_context -> 'a) =
    with_saved_translation_context (fn () =>
      let
        val {sequence_emission,set_backend,bag_backend,has_set_terms,
             has_bag_terms} = options
        val identity = ref ()
        val _ = current_backend_installation := SOME identity
        val _ = current_native_sequence_emission := sequence_emission
        val _ = current_generated_forall_emissions := 0
        val _ = emitted_term_sorts := []
        val _ = current_set_backend := set_backend
        val _ = current_set_terms := []
        val _ = current_raw_num_terms := []
        val _ = current_bag_backend := bag_backend
        val _ = current_bag_terms := []
        val _ = current_bag_helpers := []
        val _ = current_collection_function_arguments := []
        val active = ref true
        fun live () =
          if not (!active) then
            raise ERR "backend_context" "backend installation expired"
          else case !current_backend_installation of
              SOME current => if Portable.pointer_eq (current,identity)
                then () else raise ERR "backend_context"
                  "backend installation suspended"
            | NONE => raise ERR "backend_context"
                "backend installation suspended"
        fun observe thunk = (live ();thunk ())
        val state : feature_state =
          {generated_forall=fn () => observe
             (fn () => !current_generated_forall_emissions > 0),
           sequence_emission=fn () => observe (fn () => sequence_emission),
           has_set_terms=fn () => observe (fn () => has_set_terms),
           native_set_backend=fn () => observe
             (fn () => set_backend=CVC5NativeSet),
           has_bag_terms=fn () => observe (fn () => has_bag_terms),
           native_bag_backend=fn () => observe
             (fn () => bag_backend=CVC5NativeBag)}
        fun snapshot () = observe (fn () =>
          {sequence_emission=sequence_emission,set_backend=set_backend,
           bag_backend=bag_backend,
           generated_forall= !current_generated_forall_emissions > 0,
           has_set_terms=has_set_terms,has_bag_terms=has_bag_terms})
        val outcome = Exn.capture action
          {state=state,snapshot=snapshot,
           translate_type=fn regime => fn input =>
             observe (fn () => translate_type regime input),
           sort_of_type=fn regime => fn dictionary => fn ty =>
             observe (fn () => smt_sort_of_type regime dictionary ty)}
        val _ = active := false
      in Exn.release outcome end)

  fun goal_to_SmtLib_aux request apply_operator policy target
      emit_sequences goal =
    with_saved_translation_context (fn () =>
      goal_to_SmtLib_aux_inner request apply_operator policy target
        (emit_sequences andalso native_sequence_goal goal) goal)

  fun num_binder_to_int_once_conv tm =
  let
    fun is_num_var v = Type.compare (Term.type_of v, numSyntax.num) = EQUAL
    fun is_bag_var v =
      case Lib.total Type.dom_rng (Term.type_of v) of
        SOME (_, rng) => Type.compare (rng, numSyntax.num) = EQUAL
      | NONE => false
    val is_num_forall =
      boolSyntax.is_forall tm andalso
      is_num_var (Lib.fst (boolSyntax.dest_forall tm))
    val is_num_exists =
      boolSyntax.is_exists tm andalso
      is_num_var (Lib.fst (boolSyntax.dest_exists tm))
    val is_bag_forall =
      boolSyntax.is_forall tm andalso
      is_bag_var (Lib.fst (boolSyntax.dest_forall tm))
    val is_bag_exists =
      boolSyntax.is_exists tm andalso
      is_bag_var (Lib.fst (boolSyntax.dest_exists tm))
  in
    if is_num_forall then
      Conv.HO_REWR_CONV HolSmtTheory.NUM_FORALL_TO_INT tm
    else if is_num_exists then
      Conv.HO_REWR_CONV HolSmtTheory.NUM_EXISTS_TO_INT tm
    else if is_bag_forall then
      Conv.HO_REWR_CONV HolSmtTheory.BAG_FORALL_TO_INT tm
    else if is_bag_exists then
      Conv.HO_REWR_CONV HolSmtTheory.BAG_EXISTS_TO_INT tm
    else
      Conv.NO_CONV tm
  end

  fun NUM_BINDERS_TO_INT_CONV tm =
    (* TOP_DEPTH_CONV uses SUB_CONV/ABS_CONV, so surviving first-class
       abstractions are traversed as well as quantifier binders. *)
    Conv.THENC
      (Conv.TOP_DEPTH_CONV num_binder_to_int_once_conv,
       Conv.TOP_DEPTH_CONV Thm.BETA_CONV) tm
    handle Conv.UNCHANGED => Thm.REFL tm

  val exp_one_rewrites = SmtLib_GraphNumericStock.exp_one_rewrites
  val INT_EXP_1 = SmtLib_GraphNumericStock.INT_EXP_1
  val INT_EXP_BASE_1 = SmtLib_GraphNumericStock.INT_EXP_BASE_1
  val INT_EXP_2 = SmtLib_GraphNumericStock.INT_EXP_2
  val INT_EXP_3 = SmtLib_GraphNumericStock.INT_EXP_3

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

  val num_transfer_rewrites = SmtLib_GraphNumericStock.rewrites

  fun NUM_TO_INT_CONV tm =
    Conv.THENC
      (NUM_BINDERS_TO_INT_CONV,
       simpLib.SIMP_CONV pureSimps.pure_ss num_transfer_rewrites) tm
    handle Conv.UNCHANGED => Thm.REFL tm

  type native_float_transfer_info = {
    surface : string list,
    theorem : Thm.thm
  }

  (* The complete audited surface of the native binary_ieee transfer kit.
     Keep names and proofs together so extending preprocessing cannot silently
     outrun its coverage record. *)
  val native_float_transfer_infos : native_float_transfer_info list = [
    {surface = ["float record constructor"],
     theorem = smtfloatTheory.native_float_bits_transfer},
    {surface = ["universal float binder"],
     theorem = smtfloatTheory.native_float_forall_transfer},
    {surface = ["existential float binder"],
     theorem = smtfloatTheory.native_float_exists_transfer},
    {surface = ["float_plus_zero", "float_minus_zero",
                "float_plus_infinity", "float_minus_infinity",
                "float_some_qnan"],
     theorem = smtfloatTheory.native_float_special_transfer},
    {surface = ["float_is_nan", "float_is_infinite", "float_is_normal",
                "float_is_subnormal", "float_is_zero"],
     theorem = smtfloatTheory.native_float_classification_transfer},
    {surface = ["float_is_finite", "float_is_integral"],
     theorem = smtfloatTheory.native_float_finite_integral_transfer},
    {surface = ["float_is_signalling at canonical representative"],
     theorem = smtfloatTheory.native_float_signalling_transfer},
    {surface = ["negative sign predicate", "positive sign predicate"],
     theorem = smtfloatTheory.native_float_sign_transfer},
    {surface = ["float_abs"],
     theorem = smtfloatTheory.native_float_abs_transfer},
    {surface = ["float_negate"],
     theorem = smtfloatTheory.native_float_neg_transfer},
    {surface = ["float_less_than", "float_less_equal",
                "float_greater_than", "float_greater_equal",
                "float_equal", "float_unordered"],
     theorem = smtfloatTheory.native_float_comparison_transfer},
    {surface = ["float_add"],
     theorem = smtfloatTheory.native_float_add_transfer},
    {surface = ["float_sub"],
     theorem = smtfloatTheory.native_float_sub_transfer},
    {surface = ["float_mul"],
     theorem = smtfloatTheory.native_float_mul_transfer},
    {surface = ["float_div"],
     theorem = smtfloatTheory.native_float_div_transfer},
    {surface = ["float_sqrt"],
     theorem = smtfloatTheory.native_float_sqrt_transfer},
    {surface = ["float_mul_add"],
     theorem = smtfloatTheory.native_float_fma_transfer},
    {surface = ["float_to_real on finite input"],
     theorem = smtfloatTheory.native_float_to_real_transfer},
    {surface = ["float_to_ubv", "float_to_sbv"],
     theorem = smtfloatTheory.native_float_word_conversion_transfer},
    {surface = ["float_from_ieee_bv", "float_pack_ieee_bv at canon"],
     theorem = smtfloatTheory.native_float_ieee_bv_transfer},
    {surface = ["float_min"],
     theorem = smtfloatTheory.native_float_min_transfer},
    {surface = ["float_max"],
     theorem = smtfloatTheory.native_float_max_transfer},
    {surface = ["float_rem"],
     theorem = smtfloatTheory.native_float_rem_transfer},
    {surface = ["float_round with nonzero result or matching zero sign"],
     theorem = smtfloatTheory.native_float_round_transfer},
    {surface = ["real_to_float with nonzero result or matching zero sign"],
     theorem = smtfloatTheory.native_real_to_float_transfer},
    {surface = ["float_round_to_integral with nonzero result"],
     theorem = smtfloatTheory.native_float_round_to_integral_transfer}
  ]

  val native_float_transfer_surface =
    List.concat (List.map #surface native_float_transfer_infos)

  val native_float_transfer_theorems =
    List.map #theorem native_float_transfer_infos

  val native_float_transfer_rewrites =
    native_float_transfer_theorems @
    [smtfloatTheory.smtfp_is_finite_expansion,
     smtfloatTheory.smtfp_unordered_expansion,
     smtfloatTheory.smtfp_is_signalling_expansion,
     smtfloatTheory.smtfp_is_integral_expansion,
     smtfloatTheory.smtfp_rounding_of_binary_def,
     binary_ieeeTheory.rounding_case_def]

  (* Conditional transfers must see their native guards before the general
     pass lowers those guards to the smtfp surface. *)
  val native_float_guarded_context_rewrites =
    [smtfloatTheory.native_float_to_real_guarded_transfer,
     smtfloatTheory.native_float_round_sign_guarded_transfer,
     smtfloatTheory.native_float_round_guarded_transfer,
     smtfloatTheory.native_real_to_float_sign_guarded_transfer,
     smtfloatTheory.native_real_to_float_guarded_transfer,
     smtfloatTheory.native_float_round_to_integral_guarded_transfer]

  val native_float_guarded_transfer_rewrites =
    [smtfloatTheory.native_float_to_real_transfer,
     smtfloatTheory.native_float_round_transfer,
     smtfloatTheory.native_real_to_float_transfer,
     smtfloatTheory.native_float_round_to_integral_transfer]

  val native_float_ground_guard_transfers =
    [smtfloatTheory.native_float_round_transfer,
     smtfloatTheory.native_real_to_float_transfer]

  fun guarded_context_pattern theorem =
    let
      val (lhs, _) = boolSyntax.dest_eq (Thm.concl theorem)
      val (_, predicate_application) = boolSyntax.dest_imp lhs
      val (predicate, arguments) =
        boolSyntax.strip_comb predicate_application
      val _ = List.length arguments = 1 orelse
        raise ERR "guarded_context_pattern"
          "guarded transfer predicate is not unary"
    in
      (predicate, List.hd arguments)
    end

  (* HO_REWR_CONV deliberately does not guess an arbitrary surrounding
     predicate from an implication.  Match the raw result first, abstract
     its actual consequent context, and only then invoke the theorem-backed
     higher-order rewrite. *)
  fun instantiate_guarded_context theorem consequent occurrence =
    let
      val (_, raw_pattern) = guarded_context_pattern theorem
      val theorem = Drule.INST_TY_TERM
        (Term.match_term raw_pattern occurrence) theorem
      val (predicate, _) = guarded_context_pattern theorem
      val hole = Term.variant (Term.free_vars consequent)
        (Term.mk_var ("guarded_float_result", Term.type_of occurrence))
      val context = Term.mk_abs (hole,
        Term.subst [{redex = occurrence, residue = hole}] consequent)
    in
      Conv.BETA_RULE
        (Thm.INST [{redex = predicate, residue = context}] theorem)
    end

  val raw_float_result_predicates =
    [binary_ieeeSyntax.is_float_to_real,
     binary_ieeeSyntax.is_float_round,
     binary_ieeeSyntax.is_real_to_float,
     binary_ieeeSyntax.is_float_round_to_integral]

  fun count_raw_float_results tm =
    let
      val here = if List.exists (fn pred => pred tm)
        raw_float_result_predicates then 1 else 0
      val below =
        if Term.is_comb tm then
          let val (rator, rand) = Term.dest_comb tm in
            count_raw_float_results rator + count_raw_float_results rand
          end
        else if Term.is_abs tm then
          count_raw_float_results (Lib.snd (Term.dest_abs tm))
        else
          0
    in
      here + below
    end

  fun recognize_native_float_guarded_context tm =
    let
      fun guarded_implication () =
        if not (boolSyntax.is_imp tm) then NONE
        else
          let
            val (_, consequent) = boolSyntax.dest_imp tm
            val occurrences = Library.subterms consequent
            fun first_instantiation _ [] = NONE
              | first_instantiation theorem (occurrence :: rest) =
                  let
                    val (_, raw_pattern) = guarded_context_pattern theorem
                  in
                    if FCNet.can_match_term raw_pattern occurrence then
                      let
                        val instantiated = instantiate_guarded_context
                          theorem consequent occurrence
                        val (lhs, _) =
                          boolSyntax.dest_eq (Thm.concl instantiated)
                      in
                        if FCNet.can_match_term lhs tm then
                          SOME (Drule.INST_TY_TERM
                            (Term.match_term lhs tm) instantiated)
                        else
                          first_instantiation theorem rest
                      end
                    else
                      first_instantiation theorem rest
                  end
            fun first_theorem [] = NONE
              | first_theorem (theorem :: rest) =
                  (case first_instantiation theorem occurrences of
                     SOME instantiated => SOME instantiated
                   | NONE => first_theorem rest)
          in
            first_theorem native_float_guarded_context_rewrites
          end

      fun ground_pattern theorem =
        let
          val (_, transfer) = boolSyntax.dest_imp (Thm.concl theorem)
        in
          Lib.fst (boolSyntax.dest_eq transfer)
        end

      fun lift_transfer consequent occurrence transfer =
        let
          val hole = Term.variant (Term.free_vars consequent)
            (Term.mk_var
              ("ground_guarded_float_result", Term.type_of occurrence))
          val context = Term.mk_abs (hole,
            Term.subst [{redex = occurrence, residue = hole}] consequent)
        in
          Conv.BETA_RULE (Thm.AP_TERM context transfer)
        end

      fun ground_instantiation _ [] = NONE
        | ground_instantiation theorem (occurrence :: rest) =
            let
              val pattern = ground_pattern theorem
            in
              if FCNet.can_match_term pattern occurrence then
                let
                  val instantiated = Drule.INST_TY_TERM
                    (Term.match_term pattern occurrence) theorem
                  val (guard, _) =
                    boolSyntax.dest_imp (Thm.concl instantiated)
                in
                  if List.null (Term.free_vars guard) then
                    let
                      val evaluated = bossLib.EVAL guard
                      val (_, verdict) =
                        boolSyntax.dest_eq (Thm.concl evaluated)
                    in
                      if Term.aconv verdict boolSyntax.T then
                        let
                          val transfer = Drule.MATCH_MP instantiated
                            (Drule.EQT_ELIM evaluated)
                        in
                          SOME (lift_transfer tm occurrence transfer)
                        end
                      else
                        ground_instantiation theorem rest
                    end
                  else
                    ground_instantiation theorem rest
                end
              else
                ground_instantiation theorem rest
            end

      fun ground_theorem _ [] = NONE
        | ground_theorem occurrences (theorem :: rest) =
            (case ground_instantiation theorem occurrences of
               SOME instantiated => SOME instantiated
             | NONE => ground_theorem occurrences rest)
    in
      case guarded_implication () of
        SOME instantiated => SOME instantiated
      | NONE =>
      let
        val occurrences = Library.subterms tm
      in
        ground_theorem occurrences native_float_ground_guard_transfers
      end
    end

  fun native_float_guarded_context_match_conv_with prove tm =
    case recognize_native_float_guarded_context tm of
      NONE => raise Conv.UNCHANGED
    | SOME instantiated =>
    let
      val result = prove instantiated tm
      val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl result)
      val _ = Term.aconv lhs tm orelse
        raise ERR "native_float_guarded_context_match_conv_with"
          "admitted proof theorem has the wrong left-hand side"
      val count_before = count_raw_float_results tm
      val count_after = count_raw_float_results rhs
      val _ = count_after < count_before orelse
        raise ERR "native_float_guarded_context_match_conv_with"
          "admitted proof theorem does not strictly reduce raw FP results"
    in
      result
    end

  fun native_float_guarded_context_match_conv tm =
    native_float_guarded_context_match_conv_with
      (fn theorem => Conv.HO_REWR_CONV theorem) tm

  fun native_float_guarded_postorder_conv root_conversion tm =
    let
      fun theorem_rhs theorem =
        Lib.snd (boolSyntax.dest_eq (Thm.concl theorem))
      fun descend input =
        let
          val children =
            if Term.is_comb input then
              let val (rator, rand) = Term.dest_comb input
              in Thm.MK_COMB (descend rator, descend rand) end
            else if Term.is_abs input then
              let val (variable, body) = Term.dest_abs input
              in Thm.ABS variable (descend body) end
            else
              Thm.REFL input
          val current = theorem_rhs children
          val root = root_conversion current
            handle Conv.UNCHANGED => Thm.REFL current
          val revisited =
            if Term.aconv current (theorem_rhs root) then root
            else Thm.TRANS root (descend (theorem_rhs root))
        in
          Thm.TRANS children revisited
        end
      val result = descend tm
      val (lhs, _) = boolSyntax.dest_eq (Thm.concl result)
      val _ = Term.aconv lhs tm orelse
        raise ERR "native_float_guarded_postorder_conv"
          "recursive traversal produced a theorem for the wrong input"
    in
      result
    end

  val native_float_transfer_ss =
    simpLib.++
      (simpLib.++ (pureSimps.pure_ss, wordsLib.SIZES_ss),
       numSimps.REDUCE_ss)

  val native_float_guarded_transfer_ss =
    simpLib.++ (native_float_transfer_ss, realSimps.REAL_ARITH_ss)

  fun NATIVE_FLOAT_TO_SMT_CONV tm =
    let
      fun apply_or_refl conversion input = conversion input
        handle Conv.UNCHANGED => Thm.REFL input
      val guarded = native_float_guarded_postorder_conv
        native_float_guarded_context_match_conv tm
      val guarded_rhs = Lib.snd (boolSyntax.dest_eq (Thm.concl guarded))
      val lowered_guards = apply_or_refl
        (simpLib.SIMP_CONV native_float_guarded_transfer_ss
          native_float_guarded_transfer_rewrites) guarded_rhs
      val lowered_guards_rhs =
        Lib.snd (boolSyntax.dest_eq (Thm.concl lowered_guards))
      val lowered = apply_or_refl
        (simpLib.SIMP_CONV native_float_transfer_ss
          native_float_transfer_rewrites) lowered_guards_rhs
    in
      Thm.TRANS guarded (Thm.TRANS lowered_guards lowered)
    end

  val hol_string_transfer_rewrites = [
    Conv.GSYM smtstringTheory.str_inj_11,
    smtstringTheory.str_inj_STRCAT,
    smtstringTheory.str_inj_isPREFIX,
    smtstringTheory.str_inj_string_lt,
    smtstringTheory.str_inj_string_le
  ]

  fun HOL_STRING_TO_SMT_CONV tm =
    simpLib.SIMP_CONV pureSimps.pure_ss hol_string_transfer_rewrites tm
    handle Conv.UNCHANGED => Thm.REFL tm

  (* Boolean cases are already SMT's native `ite`; treating COND as a
     datatype case would recursively lower each generated conditional. *)
  fun datatype_normalization_excluded ty =
    datatype_translation_excluded ty orelse same_type (ty, Type.bool)

  fun explicit_depth_conv conversion tm =
    let
      fun changed theorem =
        let val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl theorem)
        in not (Term.aconv lhs rhs) end
      fun descend input =
        let
          val children =
            if Term.is_comb input then
              let val (rator, rand) = Term.dest_comb input
              in Thm.MK_COMB (descend rator, descend rand) end
            else if Term.is_abs input then
              let val (variable, body) = Term.dest_abs input
              in Thm.ABS variable (descend body) end
            else Thm.REFL input
          val (_, current) = boolSyntax.dest_eq (Thm.concl children)
          val root = conversion current
            handle Conv.UNCHANGED => Thm.REFL current
        in
          if changed children then Thm.TRANS children root else root
        end
    in
      descend tm
    end

  fun admitted_beta_conv tm =
    if Term.is_comb tm andalso Term.is_abs (Lib.fst (Term.dest_comb tm)) then
      Thm.BETA_CONV tm
    else
      raise Conv.UNCHANGED

  fun admitted_k_conv tm =
    if combinSyntax.is_K tm then Conv.REWR_CONV combinTheory.K_THM tm
    else raise Conv.UNCHANGED

  fun admitted_eta_conv tm =
    if Term.is_abs tm then
      let
        val (variable, body) = Term.dest_abs tm
      in
        if Term.is_comb body then
          let
            val (function, argument) = Term.dest_comb body
          in
            if Term.aconv argument variable andalso
               not (Term.free_in variable function) then
              Drule.ETA_CONV tm
            else
              raise Conv.UNCHANGED
          end
        else
          raise Conv.UNCHANGED
      end
    else
      raise Conv.UNCHANGED

  fun eta_expansion_reduction label function domains =
    let
      val variables = List.map Term.genvar domains
      val expanded = Term.list_mk_abs
        (variables, Term.list_mk_comb (function, variables))
      fun contract_introduced [] tm = Thm.REFL tm
        | contract_introduced (_ :: remaining) tm =
            if Term.is_abs tm then
              let
                val (variable, body) = Term.dest_abs tm
                val children = Thm.ABS variable
                  (contract_introduced remaining body)
                val (_, current) = boolSyntax.dest_eq (Thm.concl children)
                val step = admitted_eta_conv current
                val (step_lhs, step_rhs) =
                  boolSyntax.dest_eq (Thm.concl step)
                val _ = Term.aconv step_lhs current orelse
                  raise ERR label
                    "eta step theorem has the wrong left-hand side"
                val _ = not (Term.aconv step_lhs step_rhs) orelse
                  raise ERR label "eta step theorem made no progress"
              in
                Thm.TRANS children step
              end
            else
              raise ERR label "introduced eta binder was lost"
      val reduction = contract_introduced variables expanded
      val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl reduction)
      val _ = Term.aconv lhs expanded orelse
        raise ERR label "eta theorem has the wrong left-hand side"
      val _ = not (Term.aconv lhs rhs) orelse
        raise ERR label "eta theorem made no progress"
      val _ = Term.aconv rhs function orelse
        raise ERR label "eta proof did not reduce to the admitted function"
    in
      reduction
    end

  fun datatype_case_equality ty scrutinee extra_rewrites lhs_for rhs_for =
    let
      val tyinfo =
        case TypeBase.fetch ty of
          SOME info => info
        | NONE => raise ERR "datatype_case_equality"
            "missing TypeBase entry"
      val x = Term.genvar ty
      val equality = boolSyntax.mk_eq (lhs_for x, rhs_for x)
      val predicate = Term.mk_abs (x, equality)
      val type_subst = Type.match_type (TypeBasePure.ty_of tyinfo) ty
      val forall_cases = Thm.INST_TYPE type_subst
        (DatatypeSimps.mk_type_forall_thm_tyinfo tyinfo)
      val expanded = Thm.SPEC predicate forall_cases
      val rewrites = TypeBasePure.case_def_of tyinfo :: extra_rewrites tyinfo
      val constructor_cases =
        Lib.snd (boolSyntax.dest_eq (Thm.concl expanded))
      val beta = explicit_depth_conv admitted_beta_conv constructor_cases
      val beta_cases = Lib.snd (boolSyntax.dest_eq (Thm.concl beta))
      val simplified = simpLib.SIMP_CONV pureSimps.pure_ss
        (boolTheory.COND_CLAUSES :: boolTheory.REFL_CLAUSE ::
         boolTheory.FORALL_SIMP :: boolTheory.AND_CLAUSES :: rewrites)
        beta_cases
      val constructor_theorem =
        if boolSyntax.is_eq (Thm.concl simplified) then
          let
            val closed = Thm.TRANS beta simplified
            val closed_rhs = Lib.snd (boolSyntax.dest_eq (Thm.concl closed))
          in
            if Term.aconv closed_rhs boolSyntax.T then
              Drule.EQT_ELIM closed
            else
              raise ERR "datatype_case_equality"
                ("constructor cases did not close: " ^
                 Library.thm_to_string closed)
          end
        else
          Thm.EQ_MP (Thm.SYM beta) simplified
      val theorem = Thm.EQ_MP (Thm.SYM expanded) constructor_theorem
      val specialized0 = Thm.SPEC scrutinee theorem
      val specialized = Conv.CONV_RULE
        (explicit_depth_conv admitted_beta_conv) specialized0
    in
      Conv.CONV_RULE
        (Conv.RAND_CONV (explicit_depth_conv
          admitted_k_conv))
        specialized
    end

  (* A partial HOL destructor has no theorem fixing its value on constructors
     outside the owning branch.  Preserve such constructor applications
     literally: replacing them by the parser selector's ARB choice would be
     stronger than the registered theorem.  The resulting outer case is the
     parser's exact generic case form, and no destructor remains applied to a
     symbolic native-datatype value. *)
  fun datatype_destructor_case destructor theorem data_ty scrutinee =
    let
      fun clause constructor =
        let
          val (domains, _) = boolSyntax.strip_fun (Term.type_of constructor)
          val arguments = List.map Term.genvar domains
          val pattern = Term.list_mk_comb (constructor, arguments)
          val application = Term.mk_comb (destructor, pattern)
          val result =
            Lib.snd (boolSyntax.dest_eq (Thm.concl
              (simpLib.SIMP_CONV pureSimps.pure_ss [theorem] application)))
            handle Conv.UNCHANGED => application
        in
          (pattern, result)
        end
      val raw_case = TypeBase.mk_case
        (scrutinee, List.map clause (datatype_constructors data_ty))
    in
      datatype_case_normal_form raw_case
    end

  fun recognize_datatype_destructor tm =
    if not (Term.is_comb tm) then raise Conv.UNCHANGED
    else let
      val (destructor, scrutinee) = Term.dest_comb tm
      val data_ty = Term.type_of scrutinee
      val _ = not (datatype_normalization_excluded data_ty) orelse
        raise Conv.UNCHANGED
      val tyinfo =
        case TypeBase.fetch data_ty of
          SOME info => info
        | NONE => raise Conv.UNCHANGED
      val constructors = List.map (TypeBasePure.cinst data_ty)
        (TypeBasePure.constructors_of tyinfo)
      val theorem =
        case datatype_destructor_theorem tyinfo destructor of
          SOME theorem => theorem
        | NONE => raise Conv.UNCHANGED
      val (scrutinee_head, _) = boolSyntax.strip_comb scrutinee
      val constructor_headed = Term.is_const scrutinee_head andalso
        List.exists (Term.same_const scrutinee_head) constructors
      val constructor_reduces =
        not constructor_headed orelse
        theorem_reduces_exact_application theorem tm
      val _ = constructor_reduces orelse
        raise Conv.UNCHANGED
    in
      (destructor, theorem, scrutinee, data_ty)
    end

  fun datatype_destructor_normalize_conv_with proof tm =
    let
      val admitted = recognize_datatype_destructor tm
      val theorem = proof admitted
      val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl theorem)
      val _ = Term.aconv lhs tm orelse
        raise ERR "datatype_destructor_normalize_conv"
          "admitted proof theorem has the wrong left-hand side"
      val _ = not (Term.aconv lhs rhs) orelse
        raise ERR "datatype_destructor_normalize_conv"
          "admitted proof theorem is alpha-unchanged"
    in
      theorem
    end

  fun prove_datatype_destructor
      (destructor, theorem, scrutinee, data_ty) =
    let
      fun lhs x = Term.mk_comb (destructor, x)
      fun rhs x = datatype_destructor_case destructor theorem data_ty x
    in
      (* Recognition is complete above.  A failure here is a malformed
         registered family member and must remain a named proof error,
         never be relabelled as an inapplicable rung. *)
      datatype_case_equality data_ty scrutinee
        (fn _ => [theorem]) lhs rhs
    end

  val datatype_destructor_normalize_conv =
    datatype_destructor_normalize_conv_with prove_datatype_destructor

  fun record_accessor_normalize_conv tm =
    let
      val recognized =
        SOME (let
          val (accessor, record) = Term.dest_comb tm
          val record_ty = Term.type_of record
          val _ = not (datatype_normalization_excluded record_ty) orelse
            raise ERR "record_accessor_normalize_conv" "excluded datatype"
          val fields = TypeBase.fields_of record_ty
          val _ = if List.null fields then
              raise ERR "record_accessor_normalize_conv" "not a record"
            else ()
          val selector_index = Lib.index
            (fn (_, {accessor = candidate, ...} :
                     TypeBasePure.rcd_fieldinfo) =>
              Term.same_const accessor candidate) fields
          val constructor =
            case datatype_constructors record_ty of
              [constructor] => constructor
            | _ => raise ERR "record_accessor_normalize_conv"
                "record constructor count"
        in
          (accessor, record, record_ty, constructor, selector_index)
        end)
        handle Feedback.HOL_ERR _ => NONE
    in
      case recognized of
        NONE => raise Conv.UNCHANGED
      | SOME (accessor, record, record_ty, constructor, selector_index) =>
          let
            fun lhs x = Term.mk_comb (accessor, x)
            fun rhs x = datatype_selector_term record_ty constructor
              selector_index x
          in
            datatype_case_equality record_ty record
              TypeBasePure.accessors_of lhs rhs
          end
    end

  fun record_update_normalize_conv tm =
    let
      val recognized =
        SOME (let
          val (update_f, record) = Term.dest_comb tm
          val (update, updater) = Term.dest_comb update_f
          val record_ty = Term.type_of record
          val result_ty = Term.type_of tm
          val _ = not (datatype_normalization_excluded record_ty) andalso
                  not (datatype_normalization_excluded result_ty) orelse
            raise ERR "record_update_normalize_conv" "excluded datatype"
          val input_fields = TypeBase.fields_of record_ty
          val result_fields = TypeBase.fields_of result_ty
          val _ = if List.null input_fields orelse
                     List.length input_fields <> List.length result_fields then
              raise ERR "record_update_normalize_conv" "not matching records"
            else ()
          val update_index = Lib.index
            (fn (_, {fupd, ...} : TypeBasePure.rcd_fieldinfo) =>
              Term.same_const update fupd) input_fields
          val input_constructor =
            case datatype_constructors record_ty of
              [constructor] => constructor
            | _ => raise ERR "record_update_normalize_conv"
                "input record constructor count"
          val result_constructor =
            case datatype_constructors result_ty of
              [constructor] => constructor
            | _ => raise ERR "record_update_normalize_conv"
                "result record constructor count"
        in
          (update, updater, record, record_ty, result_fields, update_index,
           input_constructor, result_constructor)
        end)
        handle Feedback.HOL_ERR _ => NONE
    in
      case recognized of
        NONE => raise Conv.UNCHANGED
      | SOME (update, updater, record, record_ty, result_fields,
              update_index, input_constructor, result_constructor) =>
        let
      fun lhs x = Term.list_mk_comb (update, [updater, x])
      fun rhs x =
        let
          fun field selector_index =
            let
              val selected = datatype_selector_term record_ty
                input_constructor selector_index x
            in
              if selector_index = update_index then
                Term.mk_comb (updater, selected)
              else
                selected
            end
          val values = List.map field
            (List.tabulate (List.length result_fields, fn n => n))
        in
          Term.list_mk_comb (result_constructor, values)
        end
        in
          datatype_case_equality record_ty record
            (fn tyinfo => TypeBasePure.accessors_of tyinfo @
              TypeBasePure.updates_of tyinfo) lhs rhs
        end
    end

  (* Once the term has been admitted as a case over a constructor, proof
     construction is no longer a recognition probe.  In particular, never
     turn a proof-conversion failure into [UNCHANGED]: it is a checked-path
     failure and must retain its original diagnostic. *)
  fun admitted_datatype_constructor_case_reduce_conv proof_conv tm =
    let
      val theorem = proof_conv tm
      val (_, rhs) = boolSyntax.dest_eq (Thm.concl theorem)
    in
      if Term.aconv tm rhs then
        raise ERR "datatype_constructor_case_reduce_conv"
          "admitted proof conversion returned an alpha-unchanged result"
      else
        theorem
    end

  (* Reduce every TypeBase case whose scrutinee is already a constructor.
     Parser selectors and testers are cases too, so the datatype's own case
     theorem is the single generic proof source for all three forms. *)
  fun datatype_constructor_case_reduce_conv_with proof_conv tm =
    let
      val recognized =
        SOME (let
          val (_, scrutinee, _) = TypeBase.dest_case tm
          val data_ty = Term.type_of scrutinee
          val _ = not (datatype_normalization_excluded data_ty) orelse
            raise ERR "datatype_constructor_case_reduce_conv"
              "excluded datatype"
          val tyinfo =
            case TypeBase.fetch data_ty of
              SOME info => info
            | NONE => raise ERR "datatype_constructor_case_reduce_conv"
                "missing TypeBase entry"
          val (head, _) = boolSyntax.strip_comb scrutinee
          val constructors = List.map (TypeBasePure.cinst data_ty)
            (TypeBasePure.constructors_of tyinfo)
          val _ = List.exists (Term.same_const head) constructors orelse
            raise ERR "datatype_constructor_case_reduce_conv"
              "case scrutinee is not a constructor application"
        in
          tyinfo
        end)
        handle Feedback.HOL_ERR _ => NONE
    in
      case recognized of
        NONE => raise Conv.UNCHANGED
      | SOME tyinfo =>
          admitted_datatype_constructor_case_reduce_conv
            (proof_conv tyinfo) tm
    end

  val datatype_constructor_case_reduce_conv =
    datatype_constructor_case_reduce_conv_with (fn tyinfo =>
      simpLib.SIMP_CONV pureSimps.pure_ss
        [TypeBasePure.case_def_of tyinfo])

  (* [TypeBase.dest_case] requires every constructor branch to be presented
     as a syntactic lambda.  Direct uses of a case constant may instead pass
     a function-valued branch (for example option_CASE ... n s).  Eta-expand
     those branches from the current TypeBase constructor arities, with a
     kernel theorem, so the generic case normalizer below sees the same case
     rather than letting the emitter lower an unnormalized source term. *)
  fun recognize_datatype_case_branch_eta tm =
    let
      val (case_const, arguments) = boolSyntax.strip_comb tm
      fun candidate [] = NONE
        | candidate (scrutinee :: branches) =
            let
              val data_ty = Term.type_of scrutinee
            in
              if datatype_normalization_excluded data_ty then NONE
              else
                case TypeBase.fetch data_ty of
                  NONE => NONE
                | SOME tyinfo =>
                    let
                      val constructors = List.map
                        (TypeBasePure.cinst data_ty)
                        (TypeBasePure.constructors_of tyinfo)
                    in
                      if List.null constructors then NONE
                      else
                      let
                        val registered_case = TypeBasePure.cinst data_ty
                          (TypeBasePure.case_const_of tyinfo)
                      in
                      if not (Term.same_const case_const registered_case) then
                        NONE
                      else if List.length branches < List.length constructors
                      then NONE
                      else if List.length branches > List.length constructors
                      then NONE (* normalize the saturated rator prefix *)
                      else
                        let
                          fun needs_eta (constructor, branch) =
                            let
                              val (domains, _) = boolSyntax.strip_fun
                                (Term.type_of constructor)
                              val (variables, _) = Term.strip_abs branch
                            in
                              List.length variables < List.length domains
                            end
                        in
                          if List.exists needs_eta
                              (ListPair.zipEq (constructors, branches)) then
                            SOME (case_const, scrutinee,
                              constructors, branches)
                          else NONE
                        end
                      end
                    end
            end
    in
      case candidate arguments of
        NONE => raise Conv.UNCHANGED
      | SOME admitted => admitted
    end

  fun eta_expand_branch (constructor, branch) =
    let
      val (domains, _) = boolSyntax.strip_fun (Term.type_of constructor)
      val (existing_variables, body) = Term.strip_abs branch
      val constructor_arity = List.length domains
      val existing_arity = List.length existing_variables
    in
      if existing_arity >= constructor_arity then Thm.REFL branch
      else
        let
          val missing_domains = List.drop (domains, existing_arity)
          val body_expansion = Thm.SYM (eta_expansion_reduction
            "datatype_case_branch_eta_conv" body missing_domains)
        in
          List.foldr (fn (variable, theorem) =>
            Thm.ABS variable theorem) body_expansion existing_variables
        end
    end

  fun prove_datatype_case_branch_eta
      (case_const, scrutinee, constructors, branches) =
    let
      val branch_theorems = ListPair.mapEq eta_expand_branch
        (constructors, branches)
      val changed = List.exists (fn theorem =>
        let val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
        in not (Term.aconv left right) end) branch_theorems
      val _ = changed orelse raise ERR "datatype_case_branch_eta_conv"
        "admitted case had no eta-expandable branch"
    in
      List.foldl (fn (argument, application) =>
        Thm.MK_COMB (application, argument))
        (Thm.MK_COMB (Thm.REFL case_const, Thm.REFL scrutinee))
        branch_theorems
    end

  fun datatype_case_branch_eta_conv_with proof tm =
    let
      val admitted = recognize_datatype_case_branch_eta tm
      val theorem = proof admitted
      val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl theorem)
      val _ = Term.aconv lhs tm orelse
        raise ERR "datatype_case_branch_eta_conv"
          "admitted proof theorem has the wrong left-hand side"
      val _ = not (Term.aconv lhs rhs) orelse
        raise ERR "datatype_case_branch_eta_conv"
          "admitted proof theorem is alpha-unchanged"
    in
      theorem
    end

  val datatype_case_branch_eta_conv =
    datatype_case_branch_eta_conv_with prove_datatype_case_branch_eta

  fun datatype_case_normalize_conv tm =
    let
      val recognized =
        SOME (let
          val (_, scrutinee, clauses) = TypeBase.dest_case tm
          val data_ty = Term.type_of scrutinee
          val _ = not (datatype_normalization_excluded data_ty) orelse
            raise ERR "datatype_case_normalize_conv" "excluded datatype"
          val _ =
            case parser_datatype_case tm of
              SOME _ => raise ERR "datatype_case_normalize_conv"
                "already in parser normal form"
            | NONE => ()
        in
          (scrutinee, clauses, data_ty)
        end)
        handle Feedback.HOL_ERR _ => NONE
    in
      case recognized of
        NONE => raise Conv.UNCHANGED
      | SOME (scrutinee, clauses, data_ty) =>
          let
            fun lhs x = TypeBase.mk_case (x, clauses)
            fun rhs x = datatype_case_normal_form (lhs x)
          in
            datatype_case_equality data_ty scrutinee (fn _ => []) lhs rhs
          end
    end

  val datatype_normalization_rungs = [
    datatype_destructor_normalize_conv,
    record_accessor_normalize_conv,
    record_update_normalize_conv,
    datatype_case_branch_eta_conv,
    datatype_constructor_case_reduce_conv,
    datatype_case_normalize_conv
  ]

  fun first_datatype_normalization_rung [] _ = raise Conv.UNCHANGED
    | first_datatype_normalization_rung (rung :: rungs) tm =
        rung tm
        handle Conv.UNCHANGED =>
          first_datatype_normalization_rung rungs tm

  fun DATATYPE_TO_SMT_CONV tm =
    let
      fun changed theorem =
        let val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl theorem)
        in not (Term.aconv lhs rhs) end
      fun validate input theorem =
        let
          val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl theorem)
          val _ = Term.aconv lhs input orelse
            raise ERR "DATATYPE_TO_SMT_CONV"
              "normalization theorem has the wrong left-hand side"
          val _ = not (Term.aconv lhs rhs) orelse
            raise ERR "DATATYPE_TO_SMT_CONV"
              "normalization theorem made no progress"
        in rhs end
      fun normalize ancestors input =
        let
          val children =
            if Term.is_comb input then
              let
                val (rator, rand) = Term.dest_comb input
              in
                Thm.MK_COMB
                  (normalize ancestors rator, normalize ancestors rand)
              end
            else if Term.is_abs input then
              let val (variable, body) = Term.dest_abs input
              in Thm.ABS variable (normalize ancestors body) end
            else
              Thm.REFL input
          val (_, current) = boolSyntax.dest_eq (Thm.concl children)
          val root =
            (let
               val step = first_datatype_normalization_rung
                 datatype_normalization_rungs current
               val rhs = validate current step
               val _ = not (List.exists (Term.aconv rhs) ancestors) orelse
                 raise ERR "DATATYPE_TO_SMT_CONV"
                   "normalization revisited an earlier alpha-equivalent term"
             in
               Thm.TRANS step (normalize (current :: ancestors) rhs)
             end
             handle Conv.UNCHANGED => Thm.REFL current)
        in
          if changed children then Thm.TRANS children root else root
        end
    in
      normalize [] tm
    end

  fun num_free_concl_vars (asms, concl) =
  let
    fun is_num_var v =
      Term.is_var v andalso
      Type.compare (Term.type_of v, numSyntax.num) = EQUAL
    fun is_bag_var v =
      Term.is_var v andalso
      (case Lib.total Type.dom_rng (Term.type_of v) of
         SOME (_, rng) => Type.compare (rng, numSyntax.num) = EQUAL
       | NONE => false)
    val asm_fvs = List.concat (List.map Term.free_vars asms)
    fun free_in_asms v = List.exists (fn w => Term.aconv v w) asm_fvs
  in
    List.filter (fn v => (is_num_var v orelse is_bag_var v) andalso
      not (free_in_asms v)) (Term.free_vars concl)
  end

  fun SPEC_NUM_FREE_VARS_TAC_EXCEPT exclude g =
  let
    val vars = List.filter (not o exclude) (num_free_concl_vars g)
  in
    Tactical.MAP_EVERY (fn v => Tactic.SPEC_TAC (v, v)) vars g
  end

  val SPEC_NUM_FREE_VARS_TAC =
    SPEC_NUM_FREE_VARS_TAC_EXCEPT (fn _ => false)

  val thms_per_const = SmtLib_GraphNumericStock.for_head

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
  fun translation_regime ({regime, ...} : translation) = regime
  fun translation_records ({records, ...} : translation) = records ()

  (* The immutable Task06 view, also used by bounded checked adapters. *)
  val replay_datatype_destructor_theorems = datatype_destructor_theorems

  val outbound_type_declaration_records = type_declaration_records
  val outbound_term_declaration_text = term_declaration_text
  type 'term outbound_term_declaration_operations =
    'term term_declaration_operations
  val outbound_term_declaration_metadata = term_declaration_metadata_with
  val outbound_term_declaration_operations = term_declaration_operations
  val outbound_advanced_encoding_records =
    advanced_encoding_records_with_presence
  type 'term outbound_string_presence_operations =
    'term string_presence_operations
  val outbound_string_presence = string_presence_with
  val outbound_term_string_presence_operations =
    term_string_presence_operations
  val outbound_native_string_presence = native_string_presence

  (* Graph query analysis supplies an actual constant leaf here. Use the
     same generic declaration rank as emission: an instantiated result type
     can itself be a function without increasing that constant's rank. *)
  val outbound_constant_arity = declared_const_arity

  datatype outbound_regime_request = datatype regime_request
  type 'term outbound_regime_operations = 'term regime_operations
  val outbound_goal_ho_reason = goal_ho_reason_with
  val outbound_select_regime = select_regime_with
  val outbound_term_regime_operations = term_regime_operations

  datatype outbound_set_backend = datatype set_backend
  datatype outbound_bag_backend = datatype bag_backend
  datatype outbound_backend_view = datatype backend_view
  type 'term outbound_backend_selection_operations =
    'term backend_selection_operations
  datatype outbound_finite_family = datatype finite_family
  datatype outbound_finite_branch = datatype finite_branch
  type 'term outbound_finite_report = 'term finite_report
  val outbound_backend_selection_with_finite_trace =
    backend_selection_with_finite_trace
  val outbound_backend_selection = backend_selection_with
  val outbound_term_backend_selection_operations =
    term_backend_selection_operations
  type outbound_backend_context_options = backend_context_options
  type outbound_backend_snapshot = backend_snapshot
  type outbound_backend_context = backend_context
  val outbound_with_backend_context = with_backend_context

  exception NestedTranslation = NestedTranslation

  datatype outbound_carrier_parser_case = datatype carrier_parser_case
  type 'term outbound_term_translation_operations =
    'term term_translation_operations
  type ('term, 'bounds, 'terms, 'key) outbound_term_store_operations =
    ('term, 'bounds, 'terms, 'key) carrier_term_store_operations
  val outbound_term_translation_operations = term_translation_operations
  val outbound_term_store_operations = legacy_term_store_operations
  type 'doc outbound_output_operations = 'doc output_operations
  val outbound_string_output_operations = string_output_operations
  val outbound_select_logic = outbound_select_logic
  val outbound_query_script = outbound_query_script
  val outbound_query_tail = outbound_query_tail
  val outbound_translate_term_step_with_output =
    translate_term_step_with_output
  val outbound_translate_term_step_with_scoped_output =
    translate_term_step_with_scoped_output
  val outbound_translate_term_step_with_lexical_output =
    translate_term_step_with_lexical_output
  val outbound_translate_term_step = translate_term_step_with_carrier

  type 'term outbound_carrier_literal_operations =
    'term literal_recognition_operations
  type 'term outbound_carrier_literal_recognizers = 'term literal_recognizers
  val outbound_carrier_literal_recognizers = carrier_literal_recognizers_with
  val outbound_term_carrier_literal_operations =
    term_literal_recognition_operations

  val outbound_term_carrier_literal_recognizers = term_literal_recognizers

  type 'term outbound_native_datatype_policy_operations =
    'term native_datatype_policy_operations
  type 'term outbound_native_datatype_policy = 'term native_datatype_policy
  val outbound_native_datatype_policy = native_datatype_policy_with
  val outbound_term_native_datatype_policy_operations =
    term_native_datatype_policy_operations

  type 'term outbound_carrier_residual_operations =
    'term carrier_residual_operations
  val outbound_carrier_residual =
    closed_constructor_destructor_residual_with
  val outbound_term_carrier_residual_operations =
    term_carrier_residual_operations
  val outbound_term_carrier_residual =
    closed_constructor_destructor_residual

  type 'term outbound_builtin_operations = 'term builtin_operations
  val outbound_term_builtin_operations = term_builtin_operations
  val outbound_builtin_symbol_encodings = builtin_symbol_encodings_with

  type 'term outbound_collection_recognition_operations =
    'term collection_recognition_operations
  type 'term outbound_collection_recognizers = 'term collection_recognizers
  val outbound_collection_recognizers = collection_recognizers_with
  type outbound_feature_state = feature_state
  type 'term outbound_feature_operations = 'term feature_operations
  val outbound_feature_analysis = feature_analysis_with
  val outbound_term_feature_operations = term_feature_operations
  val outbound_infer_features = infer_features
  val outbound_infer_features_with_state = infer_features_with_state

  type 'term outbound_sequence_eligibility_operations =
    'term sequence_eligibility_operations
  val outbound_sequence_eligibility = sequence_eligibility_with
  val outbound_native_sequence_goal = native_sequence_goal
  val outbound_term_collection_recognition_operations =
    term_collection_recognition_operations
  val outbound_is_native_set_head = is_native_set_head
  val outbound_is_native_sequence_type = is_native_sequence_type

  datatype outbound_native_candidate = datatype native_candidate
  type 'term outbound_native_dispatch_operations =
    'term native_dispatch_operations
  val outbound_native_dispatch = native_dispatch_with

  (* Carrier callbacks preserve the existing ordered native head registry.
     Only the caller's syntax and type observations vary with the carrier. *)
  val outbound_set_marker_role = classify_set_marker_with
  val outbound_bag_marker_role = classify_bag_marker_with
  val outbound_is_set_type = is_set_result_type
  val outbound_is_bag_type = bagSyntax.is_bag_ty

  fun outbound_collection_markers (assumptions, goal) =
    collect_query_collection_markers (goal :: assumptions)

  val outbound_is_integer_coercion = #is_integer_coercion raw_num_operations
  val outbound_is_num_head = #is_num_head raw_num_operations
  val outbound_is_bag_card_head = #is_bag_card_head raw_num_operations
  val outbound_number_type = #number_type raw_num_operations

  fun outbound_raw_number_markers (assumptions, goal) =
    let
      val roots = goal :: assumptions
      val {bags, ...} = collect_query_collection_markers roots
    in SmtLib_RawNumAnalysis.collect raw_num_operations bags roots end

  fun outbound_pair_constant (left, right) =
    Term.inst [{redex = Type.alpha, residue = left},
               {redex = Type.beta, residue = right}] pairSyntax.comma_tm

  (* Solver command policies consume the feature scan recorded for this exact
     HOL translation, rather than trying to recognize syntax in printed
     SMT-LIB. *)
  fun translation_has_quantifiers translation =
    case List.find
      (fn LogicSelection _ => true | _ => false)
      (translation_records translation) of
      SOME (LogicSelection {
        features = LogicFeatures {quantifiers, ...}, ...}) => quantifiers
    | _ => raise ERR "translation_has_quantifiers"
        "translation has no LogicSelection record"

  (* This is the closed registry of unconditional definitions for HOL heads
     that checked proof parsers use to represent emitted SMT operators.  An
     entry is enabled only by an EncodedSymbol from the current translation.
     Matching uses HOL constant identity and arity, never an SMT or HOL name.

     Integer div/mod illustrate why [emitted_head] and [replay_head] may
     differ: translation emits HOL ediv/emod as SMT div/mod, while CPC parses
     their specified total semantics as smt_ediv_total/smt_emod_total.  Their
     compute theorems are the unconditional unfolding identities: they also
     expose the underlying HOL div/mod operation in one mechanically selected
     rewrite.  Real smt_rdiv is deliberately absent because its zero-divisor
     value is underspecified and therefore has no sound unconditional
     unfolding. *)
  type emitted_definition_spec = {
    emitted_head : Term.term,
    arity : int,
    replay_head : Term.term,
    unfolding : Thm.thm
  }

  val emitted_definition_specs : emitted_definition_spec list = [
    {emitted_head = wordsSyntax.word_compare_tm, arity = 2,
     replay_head = wordsSyntax.word_compare_tm,
     unfolding = wordsTheory.word_compare_def},
    {emitted_head = int_ediv_tm, arity = 2,
     replay_head = Term.prim_mk_const
       {Thy = "HolSmt", Name = "smt_ediv_total"},
     unfolding = HolSmtTheory.smt_ediv_total_compute},
    {emitted_head = int_emod_tm, arity = 2,
     replay_head = Term.prim_mk_const
       {Thy = "HolSmt", Name = "smt_emod_total"},
     unfolding = HolSmtTheory.smt_emod_total_compute}
  ]

  fun definition_for_record record =
    let
      fun matches ({emitted_head, arity, ...} : emitted_definition_spec) =
        case record of
          EncodedSymbol {hol_term, arity = emitted_arity, ...} =>
            arity = emitted_arity andalso
            Term.same_const emitted_head hol_term
        | _ => false
      fun attach ({replay_head, unfolding, ...} : emitted_definition_spec) =
        EmittedDefinition {emitted_symbol = record,
          replay_head = replay_head, unfolding = unfolding}
    in
      case List.filter matches emitted_definition_specs of
        [] => NONE
      | [spec] => SOME (attach spec)
      | _ => raise ERR "definition_for_record"
          "duplicate emitted-definition registry entry"
    end

  fun emitted_definitions_for_records records =
    List.mapPartial definition_for_record records

  fun translation_definitions translation =
    emitted_definitions_for_records (translation_records translation)

  fun emitted_definition_key (EmittedDefinition {emitted_symbol, ...}) =
    emitted_symbol
  fun emitted_definition_head (EmittedDefinition {replay_head, ...}) =
    replay_head
  fun emitted_definition_theorem (EmittedDefinition {unfolding, ...}) =
    unfolding

  (* TASK_12's completeness audit may inspect the closed registry, but replay
     must use [translation_definitions] so an absent per-run emission cannot
     enable an unfolding. *)
  fun all_emitted_definition_specs () = emitted_definition_specs

  fun translation_dicts ({tydict, tmdict, ...} : translation) = (tydict, tmdict)
  val parser_dicts_for_translation = parser_dicts_for_translation_aux NONE
  val parser_datatype_term_dictionary_from_types =
    parser_datatype_term_dictionary_from_types

  (* Graph parsers retain these exact TypeBase declarations and emitted
     spellings. Testers/selectors may only be called with admitted schematic
     operands by a graph adapter; their case branches contain local binders. *)
  type parser_datatype_constructor =
    {constructor : Term.term, token : string,
     selectors : (string * Type.hol_type) list}
  type parser_datatype_declaration =
    {hol_type : Type.hol_type,
     constructors : parser_datatype_constructor list}
  fun parser_datatype_declarations_from_types tydict
      : parser_datatype_declaration list =
    Redblackmap.foldl (fn (ty, name, declarations) =>
      case datatype_family ty of NONE => declarations
      | SOME _ =>
          {hol_type = ty, constructors = List.map
            (fn (constructor, token, selectors) =>
              {constructor = constructor, token = token,
               selectors = selectors})
            (datatype_constructor_infos ty name)} :: declarations)
      [] tydict
  fun parser_datatype_declarations ({tydict,...}:translation) =
    parser_datatype_declarations_from_types tydict
  val parser_datatype_tester_template = datatype_tester_term
  val parser_datatype_selector_template = datatype_selector_term
  fun parser_dicts_for_solver_translation solver =
    parser_dicts_for_translation_aux (SOME solver)
  fun infer_logic_from_features features =
    infer_logic_from_features_for_regime FirstOrder features
  val infer_logic_from_features_with_regime =
    infer_logic_from_features_for_regime
  val goal_requires_ho = goal_requires_ho_aux
  fun regime_for_goal dialect goal =
    select_regime (AutomaticRegime dialect) goal

  local
    fun ignore sequence_emission head = not sequence_emission andalso
      List.exists (fn sequence_head => Term.same_const head sequence_head
        handle Feedback.HOL_ERR _ => false)
        [smt_seq_update_tm,smt_seq_replace_all_tm,seq_lupdate_tm,
         seq_reverse_tm,seq_map_tm,seq_foldl_tm]
  in
    (* The fixed Seq decision belongs to the caller's emission context.
       The registry, version matching and diagnostic order remain shared. *)
    fun outbound_check_operator_availability {sequence_emission} target
        occurs =
      check_operator_availability_unless (ignore sequence_emission)
        occurs target
    fun check_goal_operator_availability_for_sequence sequence_emission
        target goal =
      check_goal_operator_availability_unless (ignore sequence_emission)
        target goal
  end

  fun option_logic_policy logic
      ({features, inferred_logic, reason} : {
        features : logic_features, inferred_logic : string, reason : string}) =
    case logic of
      NONE => NONE
    | SOME selected_logic =>
        SOME {logic = selected_logic, reason = "caller override"}

  type smtlib_emit_options = {
    request : regime_request,
    apply_operator : standard27_apply_operator,
    policy : logic_selection_policy,
    get_proof : bool,
    target : {solver : string, version : string option} option
  }

  (* The same head/first-argument grammar rejects intensional RegLan
     equality before either native or graph serialization. *)
  fun outbound_check_reglan_equality {strip_comb,known_const_matches,type_of}
      current =
    let val (head,arguments) = strip_comb current in
      case arguments of left::_ =>
        if known_const_matches boolSyntax.equality head andalso
            same_type (type_of left,reglan_ty) then
          raise ERR "reject_reglan_hol_equalities"
            ("HOL equality on smtstring$reglan is intensional; " ^
             "SMT-LIB RegLan equality is language equivalence")
        else ()
      | [] => ()
    end

  fun reject_reglan_hol_equalities (assumptions, conclusion) =
    let
      fun children term pending =
        if Term.is_comb term then
          let val (operator, operand) = Term.dest_comb term
          in operator :: operand :: pending end
        else if Term.is_abs term then
          Lib.snd (Term.dest_abs term) :: pending
        else pending
      fun visit _ [] = ()
        | visit seen (term :: pending) =
            if HOLset.member (seen, term) then visit seen pending
            else
              let
                val seen = HOLset.add (seen, term)
                val _ = outbound_check_reglan_equality
                  {strip_comb=boolSyntax.strip_comb,type_of=Term.type_of,
                   known_const_matches=fn expected => fn actual =>
                     same_const actual expected} term
              in
                visit seen (children term pending)
              end
    in
      visit (HOLset.empty Term.compare) (conclusion :: assumptions)
    end

  fun goal_to_SmtLib_translation_gen
      ({request, apply_operator, policy, get_proof, target} : smtlib_emit_options)
      goal =
    let
      val _ = reject_reglan_hol_equalities goal
      val tail = outbound_query_tail string_output_operations get_proof
    in
      Lib.apsnd (fn xs => xs @ tail)
        (goal_to_SmtLib_aux request apply_operator policy target
           true goal)
    end

  fun goal_to_SmtLib_gen opts goal =
    Lib.apfst translation_dicts
      (goal_to_SmtLib_translation_gen opts goal)

  local

    (* Generic callers emit for the automatic Standard27 regime, with the `_`
       apply spelling used by our parser and corpus, no logic override and no
       proof request.  Each entry point below is these defaults plus the
       overrides it names, so a newly added option cannot be forgotten in all
       but one of them. *)
    val default_emit_options : smtlib_emit_options = {
      request = AutomaticRegime Standard27,
      apply_operator = ApplyUnderscore,
      policy = option_logic_policy NONE,
      get_proof = false,
      target = NONE
    }

    fun with_request request ({apply_operator, policy, get_proof, target, ...}
        : smtlib_emit_options) : smtlib_emit_options =
      {request = request, apply_operator = apply_operator, policy = policy,
       get_proof = get_proof, target = target}

    fun with_apply_operator apply_operator ({request, policy, get_proof, target, ...}
        : smtlib_emit_options) : smtlib_emit_options =
      {request = request, apply_operator = apply_operator, policy = policy,
       get_proof = get_proof, target = target}

    fun with_policy policy ({request, apply_operator, get_proof, target, ...}
        : smtlib_emit_options) : smtlib_emit_options =
      {request = request, apply_operator = apply_operator, policy = policy,
       get_proof = get_proof, target = target}

    fun with_get_proof get_proof ({request, apply_operator, policy, target, ...}
        : smtlib_emit_options) : smtlib_emit_options =
      {request = request, apply_operator = apply_operator, policy = policy,
       get_proof = get_proof, target = target}

    fun with_target target ({request, apply_operator, policy, get_proof, ...}
        : smtlib_emit_options) : smtlib_emit_options =
      {request = request, apply_operator = apply_operator, policy = policy,
       get_proof = get_proof, target = target}

    fun emit_options overrides =
      List.foldl (fn (override, opts) => override opts) default_emit_options
        overrides

  in

    (* A solver boundary that pins every emission dimension.  It takes a
       dialect rather than a full regime request: overriding the regime and
       asking for a proof are not combinations any boundary needs. *)
    fun goal_to_SmtLib_translation_for_solver
        {policy, dialect, apply_operator, get_proof, target} goal =
      let
        val _ =
          case target of
            NONE => ()
          | SOME solver_target =>
              check_goal_operator_availability_for_sequence
                (native_sequence_goal goal) solver_target goal
      in
        goal_to_SmtLib_translation_gen
          (emit_options [with_request (AutomaticRegime dialect),
                         with_apply_operator apply_operator,
                         with_policy policy, with_get_proof get_proof,
                         with_target target]) goal
      end

    fun goal_to_SmtLib_translation_with_policy_and_dialect policy dialect =
      goal_to_SmtLib_translation_gen
        (emit_options [with_request (AutomaticRegime dialect),
                       with_policy policy])

    fun goal_to_SmtLib_translation_with_regime_and_apply_operator
        regime apply_operator logic =
      goal_to_SmtLib_translation_gen
        (emit_options [with_request (RegimeOverride regime),
                       with_apply_operator apply_operator,
                       with_policy (option_logic_policy logic)])

    fun goal_to_SmtLib_translation_with_regime regime logic =
      goal_to_SmtLib_translation_gen
        (emit_options [with_request (RegimeOverride regime),
                       with_policy (option_logic_policy logic)])

    fun goal_to_SmtLib_translation_with_dialect dialect logic =
      goal_to_SmtLib_translation_gen
        (emit_options [with_request (AutomaticRegime dialect),
                       with_policy (option_logic_policy logic)])

    fun goal_to_SmtLib_translation logic =
      goal_to_SmtLib_translation_gen
        (emit_options [with_policy (option_logic_policy logic)])

    fun goal_to_SmtLib_with_get_proof_translation_with_policy_and_dialect
        policy dialect =
      goal_to_SmtLib_translation_gen
        (emit_options [with_request (AutomaticRegime dialect),
                       with_policy policy, with_get_proof true])

    fun goal_to_SmtLib_with_get_proof_translation logic =
      goal_to_SmtLib_translation_gen
        (emit_options [with_policy (option_logic_policy logic),
                       with_get_proof true])

    fun goal_to_SmtLib logic =
      goal_to_SmtLib_gen
        (emit_options [with_policy (option_logic_policy logic)])

  end  (* local *)

  (* cvc5 alone supplies finite-set cardinality.  Keep this at the solver
     boundary rather than in the printer so every Z3 entry point gets the
     same structured availability diagnostic before serialization begins. *)
  val _ = register_operator_availability {
    hol_head = pred_setSyntax.card_tm, operator = "set.card", solver = "cvc5",
    versions = ["1.3.4"]
  }

  val _ = register_operator_availability {
    hol_head = bagSyntax.BAG_CARD_tm, operator = "bag.card", solver = "cvc5",
    versions = ["1.3.4"]
  }

  (* These spellings are cvc5-only even though the rest of the first-order
     Seq surface is shared.  Check them at the solver boundary, before any
     serializer can accidentally emit a Z3-rejected operator. *)
  val _ = register_operator_availability {
    hol_head = smt_seq_update_tm, operator = "seq.update", solver = "cvc5",
    versions = ["1.3.4"]
  }

  val _ = register_operator_availability {
    hol_head = smt_seq_replace_all_tm, operator = "seq.replace_all",
    solver = "cvc5", versions = ["1.3.4"]
  }

  val _ = register_operator_availability {
    hol_head = seq_lupdate_tm, operator = "seq.update", solver = "cvc5",
    versions = ["1.3.4"]
  }

  val _ = register_operator_availability {
    hol_head = seq_reverse_tm, operator = "seq.rev", solver = "cvc5",
    versions = ["1.3.4"]
  }

  val _ = register_operator_availability {
    hol_head = smtstr_update_tm, operator = "str.update", solver = "cvc5",
    versions = ["1.3.4"]
  }

  val _ = register_operator_availability {
    hol_head = smtstr_rev_tm, operator = "str.rev", solver = "cvc5",
    versions = ["1.3.4"]
  }

  (* Z3 accepts these higher-order Seq combinators at every supported anchor;
     cvc5 accepts neither.  The printer deliberately uses only `seq.foldl`:
     `seq.fold_left` is a version-gated parser alias, never an output name. *)
  val z3_seq_ho_versions = ["4.11.2", "4.12.4", "4.13.0", "4.14.1",
                            "4.15.3", "4.16.0"]

  val _ = register_operator_availability {
    hol_head = seq_map_tm, operator = "seq.map", solver = "Z3",
    versions = z3_seq_ho_versions
  }

  val _ = register_operator_availability {
    hol_head = seq_foldl_tm, operator = "seq.foldl", solver = "Z3",
    versions = z3_seq_ho_versions
  }

  val NUM_TO_INT_CONV = NUM_TO_INT_CONV
  val NUM_BINDERS_TO_INT_CONV = NUM_BINDERS_TO_INT_CONV
  val HOL_STRING_TO_SMT_CONV = HOL_STRING_TO_SMT_CONV
  val NATIVE_FLOAT_TO_SMT_CONV = NATIVE_FLOAT_TO_SMT_CONV
  val DATATYPE_TO_SMT_CONV = DATATYPE_TO_SMT_CONV
  val invented_uf_native_datatype_domain_diagnostic =
    invented_uf_native_datatype_domain_diagnostic
  val uninterpreted_native_datatype_destructor_diagnostic =
    uninterpreted_native_datatype_destructor_diagnostic
  val unsupported_smtfloat_constant_diagnostic =
    unsupported_smtfloat_constant_diagnostic
  val smtfloat_opaque_replay_constants_for_test =
    Redblackset.listItems smtfloat_opaque_replay_constants
  val reject_unsupported_smtfloat_constant_for_test =
    reject_unsupported_smtfloat_constant
  fun datatype_destructor_theorems_for_test ty =
    case TypeBase.fetch ty of
      SOME tyinfo => datatype_destructor_theorems tyinfo
    | NONE => []
  val datatype_destructor_head_for_test = datatype_destructor_head
  val datatype_destructor_case_for_test = datatype_destructor_case
  val recognize_datatype_destructor_for_test = recognize_datatype_destructor
  val datatype_destructor_normalize_conv_for_test =
    datatype_destructor_normalize_conv
  val datatype_destructor_normalize_conv_with_for_test =
    datatype_destructor_normalize_conv_with
  val datatype_constructors_for_test = datatype_constructors
  val datatype_selector_term_for_test = datatype_selector_term
  val datatype_case_normal_form_for_test = datatype_case_normal_form
  val datatype_constructor_case_reduce_conv_with_for_test =
    datatype_constructor_case_reduce_conv_with
  val datatype_case_branch_eta_conv_with_for_test =
    datatype_case_branch_eta_conv_with
  val datatype_case_branch_eta_conv_for_test =
    datatype_case_branch_eta_conv
  val closed_constructor_destructor_residual_for_test =
    closed_constructor_destructor_residual
  val reject_uninterpreted_native_destructors_for_test =
    reject_uninterpreted_native_destructors
  val native_float_guarded_context_match_conv_with_for_test =
    native_float_guarded_context_match_conv_with
  val native_float_guarded_postorder_conv_for_test =
    native_float_guarded_postorder_conv
  val native_float_transfer_surface = native_float_transfer_surface
  val native_float_transfer_theorems = native_float_transfer_theorems

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
      | SOME {Thy = "pred_set", Name = "CARD", ...} => true
      | SOME {Thy = "bag", Name = "BAG_CARD", ...} => true
      | _ => false

  fun atom_needs_num_transfer atom =
    (Term.is_var atom andalso type_mentions_num (Term.type_of atom)) orelse
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
    let
      (* LENGTH is transferred as an integer coercion around the whole list;
         word elements beneath it are not word-theory operands or indices. *)
      fun word_below_num tm =
        let val (rator, rands) = boolSyntax.strip_comb tm in
          if same_const rator seq_length_tm then false
          else type_contains_word (Term.type_of tm) orelse
            List.exists word_below_num rands
        end
        handle Feedback.HOL_ERR _ => type_contains_word (Term.type_of tm)
    in
    (term_is_num tm andalso word_below_num tm)
    orelse
    let
      val (rator, rands) = boolSyntax.strip_comb tm
    in
      type_contains_word (Term.type_of rator) andalso
      List.exists term_is_num rands
    end
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

  (* STRIP_ALL_THEN minus DISJ_CASES_THEN: flattens conjunctions and
     skolemizes existentials but never case-splits, because preprocessing
     must produce at most one subgoal (SolverSpec.simplify). *)
  val NO_SPLIT_STRIP_ASSUME_TAC =
    Thm_cont.REPEAT_TCL
      (Thm_cont.ORELSE_TCL (Thm_cont.CONJUNCTS_THEN, Thm_cont.CHOOSE_THEN))
      (fn th =>
        Tactical.FIRST [Tactic.CONTR_TAC th, Tactic.ACCEPT_TAC th,
                        Tactic.ASSUME_TAC th])

  fun NO_SPLIT_STRIP_ASSUMS_TAC g =
    Tactical.MAP_EVERY (fn _ => Tactical.POP_ASSUM NO_SPLIT_STRIP_ASSUME_TAC)
      (#1 g) g

  (* Runs the proved num-to-int transfer on the whole goal.  Assumptions are
     first moved into the conclusion so free num variables anywhere in the
     sequent are made explicit and get a non-negativity guard. *)
  fun NUM_TO_INT_TAC_EXCEPT exclude g =
  let
    open Tactic Tactical
    val undisch_assums = MAP_EVERY UNDISCH_TAC (#1 g)
  in
    if goal_mentions_num g andalso not (goal_entangles_num_and_word g) then
      (undisch_assums THEN
       SPEC_NUM_FREE_VARS_TAC_EXCEPT exclude THEN
       CONV_TAC NUM_TO_INT_CONV THEN
       REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
       (* The STRIP_ASSUME_TAC re-introduction inside REV_FULL_SIMP_TAC
          would case-split disjunctive assumptions into several subgoals. *)
       simpLib.NO_STRIP_REV_FULL_SIMP_TAC pureSimps.pure_ss
         num_transfer_rewrites THEN
       NO_SPLIT_STRIP_ASSUMS_TAC) g
    else
      ALL_TAC g
  end

  val NUM_TO_INT_TAC = NUM_TO_INT_TAC_EXCEPT (fn _ => false)

  (* Relativizes num-typed binders to guarded int-typed binders. *)
  val NUM_BINDERS_TO_INT_TAC =
  let
    open Tactic Tactical
  in
    RULE_ASSUM_TAC (Conv.CONV_RULE NUM_BINDERS_TO_INT_CONV) THEN
    CONV_TAC NUM_BINDERS_TO_INT_CONV
  end

  val HOL_STRING_TO_SMT_TAC =
    Tactical.THEN
      (Tactic.RULE_ASSUM_TAC (Conv.CONV_RULE HOL_STRING_TO_SMT_CONV),
       Tactic.CONV_TAC HOL_STRING_TO_SMT_CONV)

  val NATIVE_FLOAT_TO_SMT_TAC =
    Tactical.THEN
      (Tactic.RULE_ASSUM_TAC (Conv.CONV_RULE NATIVE_FLOAT_TO_SMT_CONV),
       Tactic.CONV_TAC NATIVE_FLOAT_TO_SMT_CONV)

  val DATATYPE_TO_SMT_TAC =
    Tactical.THEN
      (Tactic.RULE_ASSUM_TAC (Conv.CONV_RULE DATATYPE_TO_SMT_CONV),
       Tactic.CONV_TAC DATATYPE_TO_SMT_CONV)

  (* Exact stock theorem selector for checked graph preprocessing. Unlike
     get_thms this does not run a recursive expanded CONV_RULE pipeline.
     The caller must admit original constructor/type and each returned law;
     selector-internal fixed theorem operations remain explicit prerequisites. *)
  val graph_preprocessing_theorems_for_head = thms_per_const

  (* Ordered ordinary stages, including the unlabelled conversion passes.
     This is an inventory, not an implementation or a completion flag. *)
  fun graph_preprocessing_stage_inventory z3 =
    ["hol-string","native-float","real-pow-positive","num-algebra",
     "num-to-int-1","let-simp","real-pow-numeral","polymorphic-simp",
     "real-div-simp","refl-simp","function-equality","word-simp",
     "set-simp","int-divides-assumptions","int-divides-goal","beta",
     "num-to-int-2","add-theorems","cleanup-assumptions-1",
     "num-to-int-3","cleanup-assumptions-2","datatype-to-smt"] @
    (if z3 then ["z3-assertion-roundtrip-assumptions",
                 "z3-assertion-roundtrip-goal"] else [])

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

  (* Expand just an atom whose set operand is outside the printer's native
     grammar.  Applying SET_SIMP_TAC to the entire goal would also erase an
     unrelated UNION/INTER atom, defeating native-by-default emission. *)
  fun set_atom_needs_predicate_expansion tm =
  let
    val (rator, rands) = boolSyntax.strip_comb tm
    fun unsupported set = is_set_type set andalso not (native_set_term set)
  in
    if same_const rator pred_setSyntax.in_tm then
      (case rands of [_, set] => unsupported set | _ => false)
    else if same_const rator pred_setSyntax.subset_tm then
      (case rands of [left, right] => unsupported left orelse unsupported right
       | _ => false)
    else if same_const rator boolSyntax.equality then
      (case rands of [left, right] =>
         is_set_type left andalso is_set_type right andalso
         (unsupported left orelse unsupported right)
       | _ => false)
    else
      false
  end

  fun native_set_preprocess_conv tm =
    if set_atom_needs_predicate_expansion tm then
      simpLib.SIMP_CONV
        (simpLib.mk_simpset [pred_setSimps.SET_SPEC_ss])
        [pred_setTheory.SPECIFICATION, pred_setTheory.GSPEC_ETA,
         pred_setTheory.EMPTY_DEF, pred_setTheory.UNIV_DEF,
         pred_setTheory.UNION_DEF, pred_setTheory.INTER_DEF] tm
    else
      raise Conv.UNCHANGED

  val NATIVE_SET_SIMP_TAC =
    Tactic.CONV_TAC (Conv.TOP_DEPTH_CONV native_set_preprocess_conv)

  fun CHECKED_SET_SIMP_TAC g =
    let
      fun has_complement tm =
        List.exists (fn subterm =>
          Option.isSome (Lib.total pred_setSyntax.dest_compl subterm))
          (Library.subterms tm)
    in
      if List.exists has_complement (#1 g @ [#2 g]) then
        NATIVE_SET_SIMP_TAC g
      else
        Library.SET_SIMP_TAC g
    end

  (* Preserve equality on native collections.  FUN_EQ_THM would turn it into
     a predicate equality before collection discovery can select Set or Bag. *)
  fun fun_eq_preprocess_conv preserve_native_collections tm =
    let
      val (left, right) = boolSyntax.dest_eq tm
      val collection_equality =
        (is_set_type left andalso is_set_type right) orelse
        (is_bag_type left andalso is_bag_type right)
    in
      if preserve_native_collections andalso collection_equality then
        raise Conv.UNCHANGED
      else
        Conv.REWR_CONV boolTheory.FUN_EQ_THM tm
    end
    handle Feedback.HOL_ERR _ => raise Conv.UNCHANGED

  fun cvc_native_bag_goal goal =
  let
    val bag_terms = List.foldl
      (fn (term, terms) => collect_native_bag_terms term terms) []
      (Lib.fst goal @ [Lib.snd goal])
  in
    cvc5_native_bags goal bag_terms
  end

  (* Eliminates some HOL terms that are not supported by the SMT-LIB
     translation. It also adds some useful theorems to the list of assumptions
     so that SMT solvers can reason about some symbols defined in HOL4 theories. *)
  (* Every preprocessing stage must keep the goal in at most one subgoal
     (SolverSpec.simplify consumes a single goal); name the stage that
     splits, instead of failing opaquely far from the cause. *)
  fun one_subgoal_stage name (tac : Tactical.tactic) : Tactical.tactic =
    fn g =>
      fn c =>
        let
          val (goals, validation) = tac g c
        in
          if List.length goals > 1 then
            raise Feedback.mk_HOL_ERR "SmtLib" "SIMP_TAC"
              ("preprocessing stage '" ^ name ^ "' produced " ^
               Int.toString (List.length goals) ^ " subgoals")
          else
            (goals, validation)
        end

  fun SIMP_TAC_WITH_NATIVE_BAGS preserve_native_bags simp_let =
  let
    open Tactical simpLib
    fun num_to_int g =
      if preserve_native_bags andalso cvc_native_bag_goal g then
        NUM_TO_INT_TAC_EXCEPT is_bag_type g
      else NUM_TO_INT_TAC g
    val stage = one_subgoal_stage
  in
    stage "hol-string" HOL_STRING_TO_SMT_TAC THEN
    stage "native-float" NATIVE_FLOAT_TO_SMT_TAC THEN
    (* This must precede num transfer: the native real numeral form lets the
       closed positivity proof erase the whole pow term, including its nat
       exponent. *)
    Tactic.CONV_TAC (Conv.DEPTH_CONV REAL_POW_POS_LITERAL_CONV) THEN
    (* Close algebraic natural identities while their saturated subtraction
       is still in its native form, before lowering introduces nested ites. *)
    stage "num-algebra" (SIMP_TAC pureSimps.pure_ss
      [HolSmtTheory.num_sub_assoc, HolSmtTheory.num_floor_zero,
       HolSmtTheory.num_ceiling_zero, arithmeticTheory.MAX_0,
       arithmeticTheory.MIN_0, boolTheory.REFL_CLAUSE]) THEN
    stage "num-to-int" num_to_int THEN
    stage "let-simp"
      (if simp_let then Library.LET_SIMP_TAC else ALL_TAC) THEN
    Tactic.CONV_TAC (Conv.DEPTH_CONV REAL_POW_NUMERAL_CONV) THEN
    stage "polymorphic-simp" (SIMP_TAC pureSimps.pure_ss [
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
    ]) THEN
    stage "real-div-simp" (SIMP_TAC realSimps.real_ss
      [HolSmtTheory.smt_rdiv_zero, HolSmtTheory.smt_rdiv_refl,
       HolSmtTheory.smt_rdiv_one, HolSmtTheory.smt_rdiv_neg_refl,
       HolSmtTheory.smt_rdiv_neg_one]) THEN
    stage "refl-simp" (SIMP_TAC pureSimps.pure_ss [boolTheory.REFL_CLAUSE])
      THEN
    Tactic.CONV_TAC
      (Conv.DEPTH_CONV (fun_eq_preprocess_conv preserve_native_bags)) THEN
    stage "word-simp" Library.WORD_SIMP_TAC THEN
    (* Checked set simplification normally uses the predicate encoding, but
       must retain complements: SET_SIMP_TAC lowers their membership to NOTIN,
       which does not have a native SMT Set translation. *)
    stage "set-simp"
      (if simp_let then CHECKED_SET_SIMP_TAC else NATIVE_SET_SIMP_TAC) THEN
    Tactic.RULE_ASSUM_TAC
      (Conv.CONV_RULE (Conv.DEPTH_CONV INT_DIVIDES_LITERAL_MOD_CONV)) THEN
    Tactic.CONV_TAC (Conv.DEPTH_CONV INT_DIVIDES_LITERAL_MOD_CONV) THEN
    Tactic.BETA_TAC THEN
    stage "num-to-int" num_to_int THEN
    stage "add-theorems" ADD_THEOREMS_TAC THEN
    stage "cleanup-assumptions" CLEANUP_ASSUMPTIONS_TAC THEN
    (* The theorem-discovery pass may expose a fresh num-valued occurrence.
       Run the semantic transfer last, then simplify its newly-added
       assumptions even when they no longer mention num themselves. *)
    stage "num-to-int" num_to_int THEN
    stage "cleanup-assumptions" CLEANUP_ASSUMPTIONS_TAC THEN
    stage "datatype-to-smt" DATATYPE_TO_SMT_TAC
  end

  fun SIMP_TAC simp_let = SIMP_TAC_WITH_NATIVE_BAGS false simp_let
  fun CVC_SIMP_TAC simp_let = SIMP_TAC_WITH_NATIVE_BAGS true simp_let

  datatype z3_roundtrip_expansion =
      Z3Inverse of Term.term
    | Z3Ceiling of Term.term
    | Z3SymbolicCons of Term.term * Term.term
    | Z3PartialRanked of Term.term * Term.term list * Type.hol_type list

  (* Recognition is proof-free.  In particular, a malformed proof below is
     never permitted to turn an admitted expansion back into UNCHANGED. *)
  fun recognize_z3_roundtrip_expansion tm =
    if realSyntax.is_inv tm then
      SOME (Z3Inverse (realSyntax.dest_inv tm))
    else if intrealSyntax.is_INT_CEILING tm then
      SOME (Z3Ceiling (intrealSyntax.dest_INT_CEILING tm))
    else if listSyntax.is_cons tm then
      let val (element, tail) = listSyntax.dest_cons tm in
        if listSyntax.is_nil tail orelse listSyntax.is_cons tail then NONE
        else SOME (Z3SymbolicCons (element, tail))
      end
    else
      let
        val (head, arguments) = boolSyntax.strip_comb tm
      in
        if not (Term.is_const head) then NONE
        else
          let
            val {Thy, Name, ...} = Term.dest_thy_const head
            val has_direct_encoding =
              Redblackset.member (builtin_const_names, (Thy, Name)) orelse
              is_native_set_head head orelse is_native_bag_head head
            val rank = declared_const_arity head
            val missing = rank - List.length arguments
            val (domains, _) = boolSyntax.strip_fun (Term.type_of tm)
          in
            if has_direct_encoding orelse TypeBase.is_constructor head orelse
               missing <= 0 orelse List.length domains <> missing then NONE
            else SOME (Z3PartialRanked (head, arguments, domains))
          end
      end

  (* The measure follows the emitter's maximal-application view.  Counting a
     rator prefix of a saturated application would incorrectly classify that
     prefix as an independently emitted partial symbol. *)
  fun z3_roundtrip_measure tm =
    let
      val contribution =
        if Option.isSome (recognize_z3_roundtrip_expansion tm) then 1 else 0
    in
      if Term.is_abs tm then
        let val (_, body) = Term.dest_abs tm
        in contribution + z3_roundtrip_measure body end
      else
        let val (_, arguments) = boolSyntax.strip_comb tm
        in contribution + List.foldl
          (fn (argument, total) => z3_roundtrip_measure argument + total)
          0 arguments
        end
    end

  fun eta_expansion_theorem function domains =
    Thm.SYM (eta_expansion_reduction
      "z3_assertion_roundtrip_conv" function domains)

  fun prove_z3_roundtrip_expansion (tm, expansion) =
    case expansion of
      Z3Inverse argument => let
        val variable = Term.genvar realSyntax.real_ty
        val totalized = boolSyntax.mk_cond
          (boolSyntax.mk_eq (variable, realSyntax.zero_tm),
           realSyntax.zero_tm,
           Term.list_mk_comb
             (smt_rdiv_tm, [realSyntax.one_tm, variable]))
        val generic = simpLib.SIMP_PROVE (bossLib.srw_ss ())
          [HolSmtTheory.smt_rinv_def, HolSmtTheory.smt_rdiv_eq_div]
          (boolSyntax.mk_forall (variable,
            boolSyntax.mk_eq (realSyntax.mk_inv variable, totalized)))
      in
        Thm.SPEC argument generic
      end
    | Z3Ceiling argument => let
        val variable = Term.genvar realSyntax.real_ty
        val lowered = intSyntax.mk_negated
          (intrealSyntax.mk_INT_FLOOR
            (realSyntax.mk_negated variable))
        val generic = simpLib.SIMP_PROVE (bossLib.srw_ss ())
          [intrealTheory.INT_FLOOR_NEG]
          (boolSyntax.mk_forall (variable,
            boolSyntax.mk_eq
              (intrealSyntax.mk_INT_CEILING variable, lowered)))
      in
        Thm.SPEC argument generic
      end
    | Z3SymbolicCons (element, tail) =>
      let
        val singleton = listSyntax.mk_list
          ([element], Term.type_of element)
        val appended = listSyntax.mk_append (singleton, tail)
        val reduction = simpLib.SIMP_PROVE (bossLib.srw_ss ())
          [listTheory.APPEND] (boolSyntax.mk_eq (appended, tm))
      in
        Thm.SYM reduction
      end
    | Z3PartialRanked (_, _, domains) =>
        eta_expansion_theorem tm domains

  (* Explicit terminating postorder/revisit traversal.  Every admitted
     expansion is checked at the same boundary, and its RHS is recursively
     normalized before the parent is retried. *)
  fun z3_assertion_roundtrip_conv_with prove tm =
  let
    fun changed theorem =
      let val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl theorem)
      in not (Term.aconv lhs rhs) end
    fun normalize input =
      let
        val children =
          if Term.is_abs input then
            let val (variable, body) = Term.dest_abs input
            in Thm.ABS variable (normalize body) end
          else
            let
              val (head, arguments) = boolSyntax.strip_comb input
              val argument_theorems = List.map normalize arguments
            in
              List.foldl (fn (argument, application) =>
                Thm.MK_COMB (application, argument))
                (Thm.REFL head) argument_theorems
            end
        val (_, current) = boolSyntax.dest_eq (Thm.concl children)
        val root =
          case recognize_z3_roundtrip_expansion current of
            NONE => Thm.REFL current
          | SOME admitted =>
              let
                val old_measure = z3_roundtrip_measure current
                val step = prove (current, admitted)
                val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl step)
                val _ = Term.aconv lhs current orelse
                  raise ERR "z3_assertion_roundtrip_conv"
                    "admitted expansion theorem has the wrong left-hand side"
                val new_measure = z3_roundtrip_measure rhs
                val _ = not (Term.aconv lhs rhs) orelse
                  raise ERR "z3_assertion_roundtrip_conv"
                    "admitted expansion theorem is alpha-unchanged"
                val _ = new_measure < old_measure orelse
                  raise ERR "z3_assertion_roundtrip_conv"
                    ("admitted expansion did not decrease the measure: " ^
                     Int.toString old_measure ^ " -> " ^
                     Int.toString new_measure)
              in
                Thm.TRANS step (normalize rhs)
              end
      in
        if changed children then Thm.TRANS children root else root
      end
  in
    normalize tm
  end

  val z3_assertion_roundtrip_total_conv =
    z3_assertion_roundtrip_conv_with prove_z3_roundtrip_expansion

  fun z3_assertion_roundtrip_conv tm =
    let val theorem = z3_assertion_roundtrip_total_conv tm in
      if let val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl theorem)
         in Term.aconv lhs rhs end then raise Conv.UNCHANGED
      else theorem
    end

  val Z3_ASSERTION_TO_SMT_TAC =
    Tactical.THEN
      (Tactic.RULE_ASSUM_TAC
        (Conv.CONV_RULE z3_assertion_roundtrip_total_conv),
       Tactic.CONV_TAC z3_assertion_roundtrip_total_conv)

  fun Z3_SIMP_TAC simp_let =
    Tactical.THEN (SIMP_TAC simp_let, Z3_ASSERTION_TO_SMT_TAC)

  val z3_assertion_roundtrip_conv_for_test =
    z3_assertion_roundtrip_conv
  val z3_assertion_roundtrip_conv_with_for_test =
    z3_assertion_roundtrip_conv_with

  (* Kept public for Unittest's outbound-scope audit. *)
  val builtin_encoding_for_test = builtin_encoding

  (* Kept public for Unittest's replay-table completeness audit. *)
  val native_set_operator_names_for_test = native_set_operator_names
  val native_bag_operator_names_for_test = native_bag_operator_names
end  (* local *)

end
