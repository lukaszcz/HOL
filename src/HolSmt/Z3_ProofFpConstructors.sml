(* Copyright (c) 2026 The HOL4 contributors. *)

(* Authoritative type/index-only Z3 FP constructors, shared with graph
   schematic recipes. No actual operand shape or free-variable scan occurs. *)
structure Z3_ProofFpConstructors =
struct
  fun z3_is_smtfp_type ty =
    let val {Thy, Tyop, ...} = Type.dest_thy_type ty
    in Thy = "smtfloat" andalso Tyop = "smtfp" end
    handle Feedback.HOL_ERR _ => false

  fun z3_is_rounding_type ty =
    Type.compare (ty, SmtLib_Theories.rounding_mode_ty) = EQUAL

  fun z3_expect_word_width name width tm =
    let
      val actual = fcpLib.index_to_num (wordsSyntax.dim_of tm)
    in
      if actual = Arbnum.fromInt width then ()
      else SmtLib_Theories.decline ("<z3_builtin_dict." ^ name ^ ">")
        (Int.toString width ^ "-bit bit-vector expected")
    end
    handle Feedback.HOL_ERR _ =>
      SmtLib_Theories.decline ("<z3_builtin_dict." ^ name ^ ">")
        (Int.toString width ^ "-bit bit-vector expected")

  fun z3_smtfp_packed_type x =
    let
      val {Thy, Tyop, Args, ...} =
        Type.dest_thy_type (Term.type_of x)
      val _ = Thy = "smtfloat" andalso Tyop = "smtfp" orelse
        SmtLib_Theories.decline "<z3_builtin_dict.bv_wrap>"
          "FloatingPoint or RoundingMode operand expected"
      val (significand_index, exponent_index) = Lib.pair_of_list Args
      val significand_width = fcpLib.index_to_num significand_index
      val exponent_width = fcpLib.index_to_num exponent_index
      val packed_width = Arbnum.plus1
        (Arbnum.+ (significand_width, exponent_width))
    in
      wordsSyntax.mk_word_type (fcpLib.index_type packed_width)
    end

  fun z3_positive_word_index name width =
    let
      fun invalid () =
        SmtLib_Theories.decline ("<z3_builtin_dict." ^ name ^ ">")
          (name ^ ": positive numeric bit-vector width index expected")
    in
      ((let val value = SmtLib_Theories.natural_of_index width in
          if Arbnum.compare (value, Arbnum.zero) = GREATER then
            fcpLib.index_type value
          else invalid ()
        end)
       handle Interrupt => raise Interrupt
            | _ => invalid ())
    end

  fun z3_bv_wrap x =
    if z3_is_smtfp_type (Term.type_of x) then
      SmtLib_Theories.smtfloat_app_result "smtfp_pack_bv"
        (z3_smtfp_packed_type x) [x]
    else if z3_is_rounding_type (Term.type_of x) then
      SmtLib_Theories.smtfloat_app "smtfp_pack_rounding" [x]
    else
      SmtLib_Theories.decline "<z3_builtin_dict.bv_wrap>"
        "FloatingPoint or RoundingMode operand expected"

  fun z3_bv2rm name bits =
    let val _ = z3_expect_word_width name 3 bits in
      SmtLib_Theories.smtfloat_app "smtfp_unpack_rounding" [bits]
    end

  fun z3_fp_binary name hol_name (x, y) =
    if z3_is_smtfp_type (Term.type_of x) andalso
       Type.compare (Term.type_of x, Term.type_of y) = EQUAL then
      SmtLib_Theories.smtfloat_app hol_name [x, y]
    else
      SmtLib_Theories.decline ("<z3_builtin_dict." ^ name ^ ">")
        "equal FloatingPoint operand sorts expected"

  fun z3_fp_to_bv_i name hol_name indices args =
    case (indices, args) of
      ([width], [mode, x]) =>
        if z3_is_rounding_type (Term.type_of mode) andalso
           z3_is_smtfp_type (Term.type_of x) then
          SmtLib_Theories.smtfloat_app_result hol_name
            (wordsSyntax.mk_word_type
              (z3_positive_word_index name width)) [mode, x]
        else
          SmtLib_Theories.decline ("<z3_builtin_dict." ^ name ^ ">")
            "RoundingMode and FloatingPoint operands expected"
    | ([_], _) => SmtLib_Theories.decline ("<z3_builtin_dict." ^ name ^ ">")
        "two arguments expected"
    | _ => SmtLib_Theories.decline ("<z3_builtin_dict." ^ name ^ ">")
        "one bit-vector width index expected"

  fun z3_fp_to_real_i x =
    if z3_is_smtfp_type (Term.type_of x) then
      SmtLib_Theories.smtfloat_app "smtfp_to_real" [x]
    else
      SmtLib_Theories.decline "<z3_builtin_dict.fp.to_real_I>"
        "FloatingPoint operand expected"

  val z3_hi_fp_unspecified_diagnostic =
    "Z3_FPA2BV_HI_FP_UNSPECIFIED_UNSUPPORTED"

  fun z3_hi_fp_unspecified _ _ _ =
    (* Z3 4.11.2 source evidence: [hi_fp_unspecified] occurs only as the
       Boolean fpa2bv/fpa rewriter parameter in [*_rewriter_params.pyg] and
       is never declared by [fpa_decl_plugin] as an AST term.  The proof
       inventory for pinned Z3 4.11.2, 4.12.4, 4.13.0, 4.14.1 and 4.15.3 --
       all in-tree proof fixtures plus the HOLSMT_VALIDATION_DIR corpus --
       contains zero occurrences of the token as a proof term.  It therefore
       has no term type or HOL denotation to reconstruct.  Keep the exact
       token enumerated so it cannot fall through to the proof catch-all. *)
    SmtLib_Theories.decline "<z3_builtin_dict.hi_fp_unspecified>"
      (z3_hi_fp_unspecified_diagnostic ^
       ": Z3 configuration parameter is not a proof term")

  type callback = string -> Term.term list -> Term.term list -> Term.term
  val entries : (string * callback) list =
    [("bv_wrap", SmtLib_Theories.K_zero_one z3_bv_wrap),
     ("rm", SmtLib_Theories.K_zero_one (z3_bv2rm "rm")),
     ("bv2rm", SmtLib_Theories.K_zero_one (z3_bv2rm "bv2rm")),
     ("fp.min_i", SmtLib_Theories.K_zero_two
       (z3_fp_binary "fp.min_i" "smtfp_min")),
     ("fp.max_i", SmtLib_Theories.K_zero_two
       (z3_fp_binary "fp.max_i" "smtfp_max")),
     ("fp.to_ubv_I", fn _ => z3_fp_to_bv_i "fp.to_ubv_I" "smtfp_to_ubv"),
     ("fp.to_sbv_I", fn _ => z3_fp_to_bv_i "fp.to_sbv_I" "smtfp_to_sbv"),
     ("fp.to_real_I", SmtLib_Theories.K_zero_one z3_fp_to_real_i),
     ("hi_fp_unspecified", z3_hi_fp_unspecified)]

  fun bounded_entries maximum =
    let
      val _ = if maximum > 0 then () else
        raise Feedback.mk_HOL_ERR "Z3_ProofFpConstructors" "bounds"
          "nonpositive FP format/index contract"
      fun width value =
        if Arbnum.<= (value, Arbnum.fromInt maximum) then () else
          raise Feedback.mk_HOL_ERR "Z3_ProofFpConstructors" "bounds"
            "FP format/index exceeds admitted contract"
      fun index term = case Lib.total SmtLib_Theories.natural_of_index term of
          SOME value => width value | NONE => ()
      fun operand term =
        if z3_is_smtfp_type (Term.type_of term) then
          let val {Args, ...} = Type.dest_thy_type (Term.type_of term)
              val dimensions = List.map fcpLib.index_to_num Args
              val packed = Arbnum.plus1
                (List.foldl (fn (value, total) => Arbnum.+ (value, total))
                  Arbnum.zero dimensions)
          in List.app width dimensions; width packed end
        else ()
      fun adapt (name, parse : callback) =
        (name, fn token => fn indices => fn operands =>
          (List.app index indices; List.app operand operands;
           parse token indices operands))
    in List.map adapt entries end
  fun entries_with_policy maximum =
    let
      val _ = if SmtReplayResourcePolicy.positive maximum then () else
        raise Feedback.mk_HOL_ERR "Z3_ProofFpConstructors" "bounds"
          "nonpositive FP format/index contract"
      fun width value =
        if (case maximum of
            SmtReplayResourcePolicy.Uncapped => true
          | SmtReplayResourcePolicy.AtMost cap =>
              Arbnum.<= (value,
                Arbnum.fromString (IntInf.toString cap))) then () else
          raise Feedback.mk_HOL_ERR "Z3_ProofFpConstructors" "bounds"
            "FP format/index exceeds admitted contract"
      fun index term = case Lib.total SmtLib_Theories.natural_of_index term of
          SOME value => width value | NONE => ()
      fun operand term =
        if z3_is_smtfp_type (Term.type_of term) then
          let val {Args, ...} = Type.dest_thy_type (Term.type_of term)
              val dimensions = List.map fcpLib.index_to_num Args
              val packed = Arbnum.plus1
                (List.foldl (fn (value, total) => Arbnum.+ (value, total))
                  Arbnum.zero dimensions)
          in List.app width dimensions; width packed end
        else ()
      fun adapt (name, parse : callback) =
        (name, fn token => fn indices => fn operands =>
          (List.app index indices; List.app operand operands;
           parse token indices operands))
    in List.map adapt entries end
end
