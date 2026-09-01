(* Parsing cvc5's native CPC proof scripts. *)

structure CPC_ProofParser =
struct

local
  open CPC_Proof

  val ERR = Feedback.mk_HOL_ERR "CPC_ProofParser"

  type dicts = SmtLib_Parser.dicts

  (* @list is CPC's compact representation for a list of binders or
     resolution annotations.  It is not an SMT-LIB term, so retain only the
     binder-list payload needed when it is referenced by a later quantifier. *)
  val cpc_list_definitions = ref (Redblackmap.mkDict String.compare)
  val cpc_list_names = ref ([] : string list)

  (* Definitions are syntax aliases.  Keep their exact occurrence tree so an
     alias use retains CPC's operand boundaries without consulting HOL-term
     identity.  This dictionary is used only while parsing the current proof;
     every command receives its own copied provenance value. *)
  val cpc_term_provenances = ref
    (Redblackmap.mkDict String.compare :
      (string, term_provenance) Redblackmap.dict)

  fun add_term_provenance name provenance =
    cpc_term_provenances := Redblackmap.insert
      (!cpc_term_provenances, name, provenance)

  fun lookup_term_provenance name =
    SOME (Redblackmap.find (!cpc_term_provenances, name))
    handle Redblackmap.NotFound => NONE

  fun add_cpc_list name terms =
    (cpc_list_definitions := Redblackmap.insert
       (!cpc_list_definitions, name, terms);
     cpc_list_names := name :: !cpc_list_names)

  fun lookup_cpc_list name =
    SOME (Redblackmap.find (!cpc_list_definitions, name))
    handle Redblackmap.NotFound => NONE

  val cpc_cfg : SmtLib_Parser.parser_cfg = {
    mk_let_bindings = SmtLib_Parser.smtlib_mk_let_bindings,
    mk_let = SmtLib_Parser.smtlib_mk_let,
    lookup_binder_list = lookup_cpc_list,
    parse_choice = false,
    parse_lambda = true
  }

  fun add_term (dicts_ref : dicts ref) name tm =
    let
      val (tydict, tmdict) = !dicts_ref
      val tmdict = Library.extend_dict ((name,
        SmtLib_Theories.K_zero_zero tm), tmdict)
    in
      dicts_ref := (tydict, tmdict)
    end

  (* CPC prints rational literals as atoms (for example `-1` and `4/3`),
     while SMT-LIB normally uses constructor syntax.  These occur in proof
     arguments and definitions even when the source query contained no
     rational atom.  Keep the compatibility layer narrow: standard literals
     remain delegated to the ordinary dictionaries and unknown proof tokens
     still fail loudly. *)
  fun cpc_literal_parsefn token indices args =
    if not (List.null indices) orelse not (List.null args) then
      raise ERR "cpc_literal_parsefn" "not a nullary CPC literal"
    else case SmtLib_Parser.proof_string_token token of
      SOME value =>
        (SmtLib_String_Literal.mk_string_term value
         handle SmtLib_String_Literal.InvalidStringLiteral detail =>
           raise ERR "cpc_literal_parsefn" detail)
    | NONE =>
    if String.isPrefix "-" token orelse String.isSubstring "/" token then
      let
        val is_fraction = String.isSubstring "/" token
        val fields = String.fields (fn c => c = #"/") token
        val (numerator_text, denominator_text) =
          case fields of
            [numerator, denominator] => (numerator, denominator)
          | [numerator] => (numerator, "1")
          | _ => raise ERR "cpc_literal_parsefn" "malformed CPC rational literal"
        val numerator = Arbint.fromString numerator_text
        val denominator = Arbint.fromString denominator_text
      in
        if not is_fraction then intSyntax.term_of_int numerator
        else if denominator = Arbint.one then realSyntax.term_of_int numerator
        else realSyntax.mk_div (realSyntax.term_of_int numerator,
          realSyntax.term_of_int denominator)
      end
    else raise ERR "cpc_literal_parsefn" "not a CPC rational literal"

  fun numeral_of_term where_ tm =
    numSyntax.dest_numeral tm
    handle Feedback.HOL_ERR _ =>
      Arbint.toNat (intSyntax.int_of_term tm)
      handle Feedback.HOL_ERR _ =>
        raise ERR where_ "expected a CPC natural-number argument"

  (* These compact constructors are emitted by cvc5's CPC printer, not by
     SMT-LIB source files.  They are definitional presentations of ordinary
     HOL bit-vector terms. *)
  fun cpc_bv_parsefn token indices args =
    if not (List.null indices) then
      raise ERR "cpc_bv_parsefn" "unexpected indexed CPC bit-vector term"
    else
      case (token, args) of
        ("@bv", [value, width]) =>
          wordsSyntax.mk_word (numeral_of_term "@bv value" value,
            numeral_of_term "@bv width" width)
      | ("@bvsize", [word]) =>
          intSyntax.mk_injected
            (numSyntax.mk_numeral
              (fcpLib.index_to_num (wordsSyntax.dim_of word)))
      | ("@bit", [index, word]) =>
          wordsSyntax.mk_word_bit
            (numSyntax.mk_numeral (numeral_of_term "@bit index" index), word)
      | ("@from_bools", bits) => SmtLib_Theories.mk_bbterm bits
      | ("extract", [upper_tm, lower_tm, word]) =>
          let
            val upper = numeral_of_term "extract upper index" upper_tm
            val lower = numeral_of_term "extract lower index" lower_tm
            val index_type = fcpLib.index_type
              (Arbnum.plus1 (Arbnum.- (upper, lower)))
          in
            wordsSyntax.mk_word_extract
              (numSyntax.mk_numeral upper, numSyntax.mk_numeral lower,
               word, index_type)
          end
      | ("zero_extend", [amount_tm, word]) =>
          let
            val amount = numeral_of_term "zero_extend amount" amount_tm
            val width = fcpLib.index_to_num (wordsSyntax.dim_of word)
          in
            wordsSyntax.mk_w2w
              (word, fcpLib.index_type (Arbnum.+ (width, amount)))
          end
      | ("sign_extend", [amount_tm, word]) =>
          let
            val amount = numeral_of_term "sign_extend amount" amount_tm
            val width = fcpLib.index_to_num (wordsSyntax.dim_of word)
          in
            wordsSyntax.mk_sw2sw
              (word, fcpLib.index_type (Arbnum.+ (width, amount)))
          end
      | ("bvsltbv", [left, right]) =>
          boolSyntax.mk_cond
            (wordsSyntax.mk_word_lt (left, right),
             wordsSyntax.mk_word (Arbnum.one, Arbnum.one),
             wordsSyntax.mk_word (Arbnum.zero, Arbnum.one))
      | ("bvultbv", [left, right]) =>
          boolSyntax.mk_cond
            (wordsSyntax.mk_word_lo (left, right),
             wordsSyntax.mk_word (Arbnum.one, Arbnum.one),
             wordsSyntax.mk_word (Arbnum.zero, Arbnum.one))
      | ("concat", first :: rest) =>
          if List.null rest then
            raise ERR "cpc_bv_parsefn" "concat expects at least two words"
          else List.foldl
            (fn (right, left) => wordsSyntax.mk_word_concat (left, right))
            first rest
      | _ => raise ERR "cpc_bv_parsefn" "malformed CPC bit-vector term"

  (* A linear-integer source proof can introduce real-valued rational
     coefficients.  cvc5 writes the corresponding floor/coercion operators
     even though the input logic did not need the mixed Int/Real dictionary. *)
  fun cpc_intreal_parsefn token indices args =
    if not (List.null indices) then
      raise ERR "cpc_intreal_parsefn" "unexpected indexed CPC arithmetic term"
    else
      case (token, args) of
        ("to_int", [real]) => intrealSyntax.mk_INT_FLOOR real
      | ("to_real", [integer]) => intrealSyntax.mk_real_of_int integer
      | ("int.pow2", [exponent]) =>
          intSyntax.mk_exp
            (intSyntax.term_of_int (Arbint.fromInt 2),
             intSyntax.mk_Num exponent)
      | _ => raise ERR "cpc_intreal_parsefn" "malformed CPC arithmetic term"

  (* CPC flattens indexed FP applications: `((_ to_fp eb sb) x)` is
     printed as `(to_fp eb sb x)`, and similarly for FP/BV conversions.
     Restore the indices and reuse the official dictionary constructors. *)
  fun cpc_fp_indexed_parsefn token indices args =
    let
      fun two_indices constructor =
        case (indices, args) of
          ([_, _], _) => constructor indices args
        | ([], eb :: sb :: rest) => constructor [eb, sb] rest
        | _ => raise ERR "cpc_fp_indexed_parsefn"
            (token ^ " expects two FP format indices")
      fun one_index smt_name hol_name =
        case (indices, args) of
          ([_], _) => SmtLib_Theories.FloatingPoint.fp_to_bv
            smt_name hol_name indices args
        | ([], width :: rest) =>
            SmtLib_Theories.FloatingPoint.fp_to_bv
              smt_name hol_name [width] rest
        | _ => raise ERR "cpc_fp_indexed_parsefn"
            (token ^ " expects one bit-vector width index")
    in
      case token of
        "to_fp" => two_indices SmtLib_Theories.FloatingPoint.to_fp
      | "to_fp_bv" => two_indices SmtLib_Theories.FloatingPoint.to_fp
      | "to_fp_unsigned" =>
          two_indices SmtLib_Theories.FloatingPoint.to_fp_unsigned
      | "fp.to_sbv" => one_index "fp.to_sbv" "smtfp_to_sbv"
      | "fp.to_ubv" => one_index "fp.to_ubv" "smtfp_to_ubv"
      | _ => raise ERR "cpc_fp_indexed_parsefn"
          ("unsupported flattened FP symbol " ^ token)
    end

  (* cvc5's FP bit-blaster uses sort expressions as proof-term metadata,
     for example `(@fp.SIGN (_ BitVec 1))`.  HOL has no terms denoting
     types, so retain only the marker's HOL type.  The internal @fp names
     then become ordinary free HOL variables of that type; a later `trust`
     step must still prove every relationship between them and the source FP
     term.  This interpretation therefore grants no theorem. *)
  fun cpc_sort_marker_parsefn token indices args =
    let
      fun marker name ty = Term.mk_var (name, ty)
      fun width index = fcpLib.index_type (numeral_of_term token index)
    in
      case (token, indices, args) of
        ("BitVec", [bits], []) =>
          marker "@cpc.BitVec" (wordsSyntax.mk_word_type (width bits))
      | ("FloatingPoint", [eb, sb], []) =>
          marker "@cpc.FloatingPoint"
            (SmtLib_Theories.smtfp_type
              (numeral_of_term token eb, numeral_of_term token sb))
      | ("->", [], domain :: rest) =>
          if List.null rest then
            raise ERR "cpc_sort_marker_parsefn"
              "CPC function-sort marker needs a range"
          else
            let
              val (domains, range) = Lib.front_last (domain :: rest)
            in
              marker "@cpc.function"
                (boolSyntax.list_mk_fun
                  (List.map Term.type_of domains, Term.type_of range))
            end
      | _ => raise ERR "cpc_sort_marker_parsefn"
          ("malformed CPC sort marker " ^ token)
    end

  fun cpc_fp_private_parsefn token indices args =
    if not (List.null indices) then
      raise ERR "cpc_fp_private_parsefn" "unexpected indices"
    else
      case args of
        [sort_marker] => Term.mk_var (token, Term.type_of sort_marker)
      | _ => raise ERR "cpc_fp_private_parsefn"
          (token ^ " expects one sort marker")

  fun cpc_private_const_parsefn token indices args =
    if token <> "@const" orelse not (List.null indices) then
      raise ERR "cpc_private_const_parsefn" "malformed private constant"
    else
      case args of
        [index, sort_marker] =>
          Term.mk_var
            ("@cpc.const." ^ Arbnum.toString (numeral_of_term token index),
             Term.type_of sort_marker)
      | _ => raise ERR "cpc_private_const_parsefn"
          "@const expects an index and a sort marker"

  fun cpc_bvite_parsefn token indices args =
    if token <> "bvite" orelse not (List.null indices) then
      raise ERR "cpc_bvite_parsefn" "malformed bvite"
    else
      case args of
        [condition, then_branch, else_branch] =>
          boolSyntax.mk_cond
            (wordsSyntax.mk_word_bit (numSyntax.zero_tm, condition),
             then_branch, else_branch)
      | _ => raise ERR "cpc_bvite_parsefn" "bvite expects three arguments"

  (* Totalized FP operators are private bit-blaster vocabulary.  Keep each
     application as an uninterpreted HOL function: its defining `trust` step
     is accepted only if the FP re-prover can establish the relationship to
     the public SMT-LIB operator. *)
  fun cpc_fp_total_parsefn token indices args =
    if not (List.null indices) orelse List.null args then
      raise ERR "cpc_fp_total_parsefn" "malformed private FP operator"
    else
      let
        val result_type = Term.type_of (List.hd args)
        val function_type = boolSyntax.list_mk_fun
          (List.map Term.type_of args, result_type)
      in
        Term.list_mk_comb (Term.mk_var (token, function_type), args)
      end

  (* cvc5's CPC signature contains totalized arithmetic operators that are
     not SMT-LIB symbols.  Integer totals have specified zero branches;
     integer by-zero skolems remain HOL's underspecified ediv/emod at zero.
     Real by-zero uses smt_rdiv, since HOL real division is specified there. *)
  val smt_ediv_total_tm = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_ediv_total"}
  val smt_emod_total_tm = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_emod_total"}
  val smt_rdiv_tm = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_rdiv"}

  fun cpc_arith_total_error message =
    raise ERR "cpc_arith_total_parsefn" message

  fun cpc_left_assoc name constructor args =
    case args of
      first :: rest =>
        if List.null rest then
          cpc_arith_total_error (name ^ " expects at least two arguments")
        else List.foldl (fn (right, left) => constructor (left, right))
          first rest
    | [] => cpc_arith_total_error (name ^ " expects arguments")

  fun cpc_real_arg arg =
    if Type.compare (Term.type_of arg, intSyntax.int_ty) = EQUAL then
      intrealSyntax.mk_real_of_int arg
    else arg

  fun cpc_arith_total_parsefn token indices args =
    if not (List.null indices) then
      cpc_arith_total_error (token ^ " does not accept indices")
    else
      case token of
        "div_total" => cpc_left_assoc token
          (fn (left, right) => Term.list_mk_comb
            (smt_ediv_total_tm, [left, right])) args
      | "mod_total" =>
          (case args of
             [left, right] => Term.list_mk_comb
               (smt_emod_total_tm, [left, right])
           | _ => cpc_arith_total_error "mod_total expects two arguments")
      | "/_total" => cpc_left_assoc token
          (fn (left, right) => realSyntax.mk_div (left, right))
          (List.map cpc_real_arg args)
      | "@int_div_by_zero" =>
          (case args of
             [arg] => SmtLib_Theories.mk_int_ediv
               (arg, intSyntax.zero_tm)
           | [] => Term.mk_var (token, intSyntax.int_ty)
           | _ => cpc_arith_total_error
               "@int_div_by_zero expects one argument")
      | "@mod_by_zero" =>
          (case args of
             [arg] => SmtLib_Theories.mk_int_emod
               (arg, intSyntax.zero_tm)
           | [] => Term.mk_var (token, intSyntax.int_ty)
           | _ => cpc_arith_total_error
               "@mod_by_zero expects one argument")
      | "@div_by_zero" =>
          (case args of
             [arg] => Term.list_mk_comb
               (smt_rdiv_tm, [arg, realSyntax.zero_tm])
           | [] => Term.mk_var (token, realSyntax.real_ty)
           | _ => cpc_arith_total_error
               "@div_by_zero expects one argument")
      | _ => cpc_arith_total_error
        ("unsupported totalized arithmetic symbol " ^ token)

  (* cvc5 uses unary str.++ and re.++ applications as compact suffix
     containers in RARE annotations.  They are proof metadata, not accepted
     benchmark syntax; interpret a singleton as itself and retain the
     standard left-associative meaning for longer lists. *)
  fun cpc_concat_parsefn theory_name token indices args =
    if not (List.null indices) then
      raise ERR "cpc_concat_parsefn" "unexpected concat indices"
    else
      let
        val constant =
          Term.prim_mk_const {Thy = "smtstring", Name = theory_name}
        fun concat (right, left) =
          Term.list_mk_comb (constant, [left, right])
      in
        case args of
          first :: rest => List.foldl concat first rest
        | [] => raise ERR "cpc_concat_parsefn"
            (token ^ " expects at least one CPC argument")
      end

  fun with_cpc_fp_entries tmdict =
    let
      val tmdict = List.foldl
        (fn (name, dict) => Library.extend_dict
          ((name, cpc_sort_marker_parsefn), dict))
        tmdict ["BitVec", "FloatingPoint", "->"]
      val tmdict = List.foldl
        (fn (name, dict) => Library.extend_dict
          ((name, cpc_fp_private_parsefn), dict))
        tmdict
        ["@fp.SIGN", "@fp.EXPONENT", "@fp.SIGNIFICAND", "@fp.ZERO",
         "@fp.NAN", "@fp.INF"]
      val tmdict = Library.extend_dict
        (("@const", cpc_private_const_parsefn), tmdict)
      val tmdict = Library.extend_dict
        (("bvite", cpc_bvite_parsefn), tmdict)
      val tmdict = List.foldl
        (fn (name, dict) => Library.extend_dict
          ((name, cpc_fp_total_parsefn), dict))
        tmdict ["fp.max_total", "fp.min_total"]
    in
      List.foldl
      (fn (name, dict) => Library.extend_dict
        ((name, cpc_fp_indexed_parsefn), dict))
      tmdict
      ["to_fp", "to_fp_bv", "to_fp_unsigned", "fp.to_sbv", "fp.to_ubv"]
    end

  fun with_cpc_literals (tydict, tmdict) =
    let
      (* cvc5 writes [Bag Bool] in qualified bag literals.  A proof sort is
         parsed through the term dictionary, so retain Bool only as a marker. *)
      fun bool_sort_marker token indices args =
        if token = "Bool" andalso List.null indices andalso List.null args then
          boolSyntax.T
        else raise ERR "bool_sort_marker" "expected the Bool sort marker"
      fun bag_sort_marker token indices args =
        case (token, indices, args) of
          ("Bag", [], [element]) => Term.mk_var ("@cpc.Bag",
            Type.--> (Term.type_of element, numSyntax.num))
        | _ => raise ERR "bag_sort_marker" "expected a Bag sort marker"
      fun set_sort_marker token indices args =
        case (token, indices, args) of
          ("Set", [], [element]) => Term.mk_var ("@cpc.Set",
            Type.--> (Term.type_of element, Type.bool))
        | _ => raise ERR "set_sort_marker" "expected a Set sort marker"
      fun as_sort_marker token indices args =
        case (token, indices, args) of
          ("as", [], [term, sort]) =>
            if Type.compare (Term.type_of term, Term.type_of sort) = EQUAL
            then term
            else raise ERR "as_sort_marker" "qualification sort mismatch"
        | _ => raise ERR "as_sort_marker" "expected a qualified term"
      (* The source translation dictionary is deliberately as narrow as its
         declared logic.  CPC arithmetic lemmas may nevertheless contain
         rationals and their Real coercions, so add the mixed arithmetic
         overloads only while reading the proof. *)
      val tmdict = Library.extend_dict (("Bool", bool_sort_marker),
        Library.extend_dict (("Bag", bag_sort_marker),
          Library.extend_dict (("Set", set_sort_marker),
            Library.extend_dict (("as", as_sort_marker),
              Library.union_dict tmdict SmtLib_Theories.Reals_Ints.tmdict))))
      fun cpc_quantifiers_skolemize_parsefn token indices args =
        case args of
          [quantified, index] =>
            let
              val index = Arbnum.toInt
                (numeral_of_term "@quantifiers_skolemize index" index)
              val (variables, objective) =
                (let val (variables, body) = boolSyntax.strip_forall quantified
                 in (variables, boolSyntax.mk_neg body) end)
                handle Feedback.HOL_ERR _ => boolSyntax.strip_exists quantified
              fun witnesses [] _ = []
                | witnesses (variable :: rest) objective =
                    let
                      val witness = boolSyntax.mk_select
                        (variable,
                         boolSyntax.list_mk_exists (rest, objective))
                      val objective' = Term.subst
                        [{redex = variable, residue = witness}] objective
                    in
                      witness :: witnesses rest objective'
                    end
            in
              List.nth (witnesses variables objective, index)
              handle Subscript => raise ERR
                "cpc_quantifiers_skolemize_parsefn"
                "binder index is outside the quantified formula"
            end
        | _ => raise ERR "cpc_quantifiers_skolemize_parsefn"
            "expected a quantified formula and a binder index"
      fun sets_deq_diff_parsefn token indices args =
        case (token, indices, args) of
          ("@sets_deq_diff", [], [left, right]) =>
            let
              val (element, range) = Type.dom_rng (Term.type_of left)
              val _ =
                if Type.compare (range, Type.bool) = EQUAL andalso
                   Type.compare (Term.type_of left, Term.type_of right) = EQUAL
                then ()
                else raise ERR "sets_deq_diff_parsefn"
                  "expected two Sets of the same type"
              val element_var = Term.variant (Term.all_varsl [left, right])
                (Term.mk_var ("sets_deq_diff_x", element))
            in
              boolSyntax.mk_select (element_var, boolSyntax.mk_neg
                (boolSyntax.mk_eq (Term.mk_comb (left, element_var),
                  Term.mk_comb (right, element_var))))
            end
        | _ => raise ERR "sets_deq_diff_parsefn"
            "expected two unindexed Set arguments"
      fun bags_deq_diff_parsefn token indices args =
        case (token, indices, args) of
          ("@bags_deq_diff", [], [left, right]) =>
            let
              val (element, count) = Type.dom_rng (Term.type_of left)
              val _ =
                if Type.compare (count, numSyntax.num) = EQUAL andalso
                   Type.compare (Term.type_of left, Term.type_of right) = EQUAL
                then ()
                else raise ERR "bags_deq_diff_parsefn"
                  "expected two Bags of the same type"
              val element_var = Term.variant (Term.all_varsl [left, right])
                (Term.mk_var ("bags_deq_diff_x", element))
              val differs = boolSyntax.mk_neg (boolSyntax.mk_eq
                (Term.mk_comb (left, element_var),
                 Term.mk_comb (right, element_var)))
            in
              boolSyntax.mk_select (element_var, differs)
            end
        | _ => raise ERR "bags_deq_diff_parsefn"
            "expected two unindexed Bag arguments"
    in
    (tydict, Library.extend_dict
      (("@sets_deq_diff", sets_deq_diff_parsefn),
      Library.extend_dict
      (("@bags_deq_diff", bags_deq_diff_parsefn),
      Library.extend_dict
      (("@quantifiers_skolemize", cpc_quantifiers_skolemize_parsefn),
      Library.extend_dict (("str.++",
        cpc_concat_parsefn "smtstr_concat"),
      Library.extend_dict (("re.++",
        cpc_concat_parsefn "reglan_concat"),
      Library.extend_dict (("to_int", cpc_intreal_parsefn),
      Library.extend_dict (("to_real", cpc_intreal_parsefn),
      Library.extend_dict (("int.pow2", cpc_intreal_parsefn),
      Library.extend_dict (("div_total", cpc_arith_total_parsefn),
      Library.extend_dict (("mod_total", cpc_arith_total_parsefn),
      Library.extend_dict (("/_total", cpc_arith_total_parsefn),
      Library.extend_dict (("@int_div_by_zero", cpc_arith_total_parsefn),
      Library.extend_dict (("@mod_by_zero", cpc_arith_total_parsefn),
      Library.extend_dict (("@div_by_zero", cpc_arith_total_parsefn),
      Library.extend_dict (("**_total", cpc_arith_total_parsefn),
      Library.extend_dict (("extract", cpc_bv_parsefn),
      Library.extend_dict (("zero_extend", cpc_bv_parsefn),
      Library.extend_dict (("sign_extend", cpc_bv_parsefn),
      Library.extend_dict (("bvsltbv", cpc_bv_parsefn),
      Library.extend_dict (("bvultbv", cpc_bv_parsefn),
      Library.extend_dict (("concat", cpc_bv_parsefn),
      Library.extend_dict (("@bit", cpc_bv_parsefn),
      Library.extend_dict (("@from_bools", cpc_bv_parsefn),
      Library.extend_dict (("@bvsize", cpc_bv_parsefn),
        Library.extend_dict (("@bv", cpc_bv_parsefn),
          Library.extend_dict (("_", cpc_literal_parsefn),
            with_cpc_fp_entries tmdict)))))))))))))))))))))))))))
    end

  fun parse_term dicts_ref get_token =
    let
      val first = get_token ()
      fun ordinary tokens = SmtLib_Parser.parse_term_with_cfg cpc_cfg
        (Library.undo_look_ahead tokens get_token) (!dicts_ref)
    in
      if first <> "(" then ordinary [first]
      else
        let val head = get_token () in
          if head = "_" then
            let
              fun application_terms terms =
                let val token = get_token () in
                  if token = ")" then List.rev terms
                  else application_terms
                    (parse_term dicts_ref
                       (Library.undo_look_ahead [token] get_token) :: terms)
                end
            in
              case application_terms [] of
                function :: arguments =>
                  if List.null arguments then
                    raise ERR "parse_term"
                      "CPC `_` application expects an argument"
                  else Term.list_mk_comb (function, arguments)
              | [] => raise ERR "parse_term"
                  "CPC `_` application expects a function"
            end
          (* CPC declares [is] as a parameterized constant whose first
             explicit argument is a constructor symbol, rather than as the
             indexed identifier used by SMT-LIB.  Keep that symbol opaque
             until the datatype scrutinee has been typed; in particular, do
             not elaborate it as a nullary constructor application. *)
          else if head = "is" then
            let
              val constructor = get_token ()
              val _ =
                if constructor = "(" orelse constructor = ")" then
                  raise ERR "parse_term"
                    "CPC datatype tester expects a constructor symbol"
                else ()
              val scrutinee = parse_term dicts_ref get_token
              val _ = Library.expect_token ")" (get_token ())
              val constructor_parameter = Term.mk_var
                (constructor, Type.gen_tyvar ())
              val (_, tmdict) = !dicts_ref
            in
              SmtLib_Parser.apply_term tmdict "is"
                [constructor_parameter] [scrutinee]
            end
          else if head = "@var" then
            let
              val var_name = get_token ()
              val var_type = SmtLib_Parser.parse_type get_token
                (#1 (!dicts_ref))
              val _ = Library.expect_token ")" (get_token ())
            in
              Term.mk_var (var_name, var_type)
            end
          else if head = "forall" orelse head = "exists" orelse
                  head = "lambda" then
            let
              val binders = get_token ()
              fun bind vars body =
                if head = "forall" then
                  boolSyntax.list_mk_forall (vars, body)
                else if head = "exists" then
                  boolSyntax.list_mk_exists (vars, body)
                else Term.list_mk_abs (vars, body)
            in
              case lookup_cpc_list binders of
                SOME vars =>
                  let
                    val body = parse_term dicts_ref get_token
                    val _ = Library.expect_token ")" (get_token ())
                  in
                    bind vars body
                  end
              | NONE =>
                  if binders = "(" then
                    let
                      val binder_head = get_token ()
                      fun inline_binders terms =
                        let val token = get_token () in
                          if token = ")" then List.rev terms
                          else inline_binders
                            (parse_term dicts_ref
                              (Library.undo_look_ahead [token] get_token) ::
                             terms)
                        end
                    in
                      if binder_head = "@list" then
                        let
                          val vars = inline_binders []
                          val body = parse_term dicts_ref get_token
                          val _ = Library.expect_token ")" (get_token ())
                        in
                          bind vars body
                        end
                      else ordinary ["(", head, binders, binder_head]
                    end
                  else raise ERR "parse_term"
                    ("undefined CPC @list alias " ^ binders ^
                     " (known aliases: " ^
                     String.concatWith ", " (List.rev (!cpc_list_names)) ^ ")")
            end
          else ordinary ["(", head]
        end
    end

  datatype raw_term =
      RawAtom of string
    | RawList of raw_term list

  (* CPC represents a datatype tester as the parameterized application
       (is Constructor scrutinee)
     even when it occurs below equality or another proof argument.  The
     shared SMT-LIB parser deliberately accepts only the standard indexed
     spelling.  Normalize the complete raw occurrence tree before
     elaboration so nested CPC testers take the same registered dictionary
     path as ((_ is Constructor) scrutinee).  Malformed arities remain
     untouched and therefore retain the ordinary parser diagnostic. *)
  fun normalize_cpc_testers raw =
    case raw of
      RawList [RawAtom "is", RawAtom constructor, scrutinee] =>
        RawList
          [RawList [RawAtom "_", RawAtom "is", RawAtom constructor],
           normalize_cpc_testers scrutinee]
    | RawList entries => RawList (List.map normalize_cpc_testers entries)
    | RawAtom _ => raw

  fun read_raw_term get_token =
    case get_token () of
      "(" =>
        let
          fun entries acc =
            case get_token () of
              ")" => RawList (List.rev acc)
            | token => entries
                (read_raw_term
                  (Library.undo_look_ahead [token] get_token) :: acc)
        in
          entries []
        end
    | ")" => raise ERR "read_raw_term" "unexpected closing parenthesis"
    | token => RawAtom token

  fun raw_tokens raw =
    case raw of
      RawAtom token => [token]
    | RawList entries =>
        "(" :: List.concat (List.map raw_tokens entries) @ [")"]

  fun raw_contains_let raw =
    case raw of
      RawAtom _ => false
    | RawList (RawAtom "let" :: _) => true
    | RawList entries => List.exists raw_contains_let entries

  fun exact_application head operands =
    ApplicationProvenance (head, operands)

  fun exact_binder head body =
    BinderProvenance (head, body)

  fun exact_binders head names body =
    List.foldr (fn (_, nested) => exact_binder head nested) body names

  (* Equality endpoints are semantic inputs to omitted SYM, TRANS,
     EQ_RESOLVE, and CONG.  Retain their boundary even when both endpoints
     are conjunction-free; AtomicProvenance for the whole equality would
     erase which exact side an equality-consuming route selected. *)
  fun sparse_equality left right = EqualityProvenance (left, right)

  fun lookup_lexical_provenance [] _ = NONE
    | lookup_lexical_provenance ((bound, provenance) :: rest) name =
        if bound = name then SOME provenance
        else lookup_lexical_provenance rest name

  fun binder_names raw =
    case raw of
      RawList (RawAtom "@list" :: binders) =>
        let
          fun binder_name (RawAtom alias) = alias
            | binder_name (RawList
                [RawAtom "@var", RawAtom name, _]) = name
            | binder_name _ = raise ERR "provenance_of_raw"
                "unsupported CPC inline binder"
        in
          SOME (List.map binder_name binders)
          handle Feedback.HOL_ERR _ => NONE
        end
    | RawList binders =>
        let
          fun binder_name (RawList [RawAtom name, _]) = name
            | binder_name _ = raise ERR "provenance_of_raw"
                "unsupported SMT-LIB binder declaration"
        in
          SOME (List.map binder_name binders)
          handle Feedback.HOL_ERR _ => NONE
        end
    | RawAtom alias =>
        (case lookup_cpc_list alias of
           SOME variables =>
             (SOME (List.map (Lib.fst o Term.dest_var) variables)
              handle Feedback.HOL_ERR _ => NONE)
         | NONE => NONE)

  fun let_bindings environment raw =
    case raw of
      RawList bindings =>
        let
          fun binding (RawList [RawAtom name, rhs]) =
                (name, provenance_of_raw_in environment rhs)
            | binding _ = raise ERR "provenance_of_raw"
                "unsupported SMT-LIB let binding"
        in
          SOME (List.map binding bindings)
          handle Feedback.HOL_ERR _ => NONE
        end
    | _ => NONE

  and provenance_of_raw_in environment raw =
    case raw of
      RawAtom token =>
        (case lookup_lexical_provenance environment token of
           SOME provenance => provenance
         | NONE =>
             (case lookup_term_provenance token of
                SOME provenance => provenance
              | NONE => AtomicProvenance))
    | RawList (RawAtom "and" :: operands) =>
        if List.length operands >= 2 then
          ConjunctionProvenance
            (ParsedConjunction,
             List.map (provenance_of_raw_in environment) operands)
        else UnavailableProvenance
          "parsed CPC conjunction has fewer than two operands"
    | RawList [RawAtom "=", left, right] =>
        sparse_equality (provenance_of_raw_in environment left)
          (provenance_of_raw_in environment right)
    | RawList [RawAtom head, binders, body] =>
        if head = "forall" orelse head = "exists" orelse
           head = "lambda"
         then
          (case binder_names binders of
             SOME names => exact_binders head names
               (provenance_of_raw_in
                 (List.map (fn name => (name, AtomicProvenance)) names @
                  environment) body)
           | NONE => UnavailableProvenance
               ("unsupported " ^ head ^ " binder provenance"))
        else if head = "let" then
          (case let_bindings environment binders of
             SOME bindings =>
               provenance_of_raw_in (bindings @ environment) body
           | NONE => UnavailableProvenance
               "unsupported SMT-LIB let provenance")
        else exact_application head
          [provenance_of_raw_in environment binders,
           provenance_of_raw_in environment body]
    | RawList (RawAtom head :: operands) =>
        if head = "match" orelse head = "par" then
          UnavailableProvenance
            ("unsupported binding form " ^ head)
        else if head = "@var" then AtomicProvenance
        else exact_application head
          (List.map (provenance_of_raw_in environment) operands)
    | RawList entries =>
        exact_application "<computed-head>"
          (List.map (provenance_of_raw_in environment) entries)

  fun provenance_of_raw raw = provenance_of_raw_in [] raw

  (* Read exactly one CPC occurrence before elaborating it to HOL.  The raw
     occurrence tree retains every path to a nested conjunction and every
     conjunction's exact operand boundaries.  Conjunction-free subtrees use
     one atomic marker; no HOL-term equality participates in provenance
     recovery. *)
  fun parse_located_term dicts_ref get_token : located_term =
    let
      val raw = read_raw_term get_token
      val tokens = ref (raw_tokens (normalize_cpc_testers raw))
      fun next_token () =
        case !tokens of
          token :: rest => (tokens := rest; token)
        | [] => raise ERR "parse_located_term"
            "internal CPC occurrence token stream exhausted"
      val parsed_term = parse_term dicts_ref next_token
      val _ = List.null (!tokens) orelse
        raise ERR "parse_located_term"
          "internal CPC occurrence parser left trailing tokens"
      (* SMT-LIB lets elaborate to kernel LET applications, while the exact
         lexical provenance above already describes their simultaneous,
         capture-avoiding substitution.  Reduce precisely those occurrences
         before pairing the HOL term with that substituted occurrence tree.
         The conversion is proof-producing; aliases consequently store the
         same normalized term/provenance pair as direct commands. *)
      val term =
        if raw_contains_let raw then
          boolSyntax.rhs (Thm.concl
            (Conv.DEPTH_CONV pairLib.let_CONV parsed_term))
          handle Conv.UNCHANGED => parsed_term
        else parsed_term
    in
      {term = term, provenance = provenance_of_raw raw}
    end

  fun parse_recorded_term dicts_ref get_token =
    #term (parse_located_term dicts_ref get_token)

  fun unavailable_term reason term : located_term =
    {term = term, provenance = UnavailableProvenance reason}

  fun skip_sexp get_token =
    let
      fun skip depth =
        case get_token () of
          "(" => skip (depth + 1)
        | ")" => if depth = 0 then () else skip (depth - 1)
        | _ => skip depth
    in
      skip 0
    end

  (* Read the remainder of a declaration after its command name.  We use the
     token copy both to decide whether it redeclares a symbol already supplied
     by HolSmt's translation dictionaries and, when it does not, to feed the
     ordinary SMT-LIB declaration parsers. *)
  fun declaration_tokens get_token =
    let
      fun loop depth acc =
        let val token = get_token () in
          case token of
            "(" => loop (depth + 1) (token :: acc)
          | ")" => if depth = 0 then List.rev (token :: acc)
                   else loop (depth - 1) (token :: acc)
          | _ => loop depth (token :: acc)
        end
    in
      loop 0 []
    end

  fun term_declared (tydict, tmdict) name =
    Option.isSome (Redblackmap.peek (tmdict, name))

  fun type_declared (tydict, tmdict) name =
    Option.isSome (Redblackmap.peek (tydict, name))

  fun datatype_binding_names tokens =
    let
      fun bindings ("(" :: name :: _ :: ")" :: rest) acc =
            bindings rest (name :: acc)
        | bindings (")" :: _) acc = List.rev acc
        | bindings _ _ = []
    in
      case tokens of "(" :: rest => bindings rest [] | _ => []
    end

  fun parse_or_keep_term_declaration parse dicts_ref get_token =
    let
      val tokens = declaration_tokens get_token
      val name = case tokens of name :: _ => name
        | [] => raise ERR "parse_declaration" "missing declaration name"
    in
      if term_declared (!dicts_ref) name then ()
      else dicts_ref := parse (Library.undo_look_ahead tokens get_token)
        (!dicts_ref)
    end

  fun parse_declare_const get_token (tydict, tmdict) =
    let
      val name = get_token ()
      val range = SmtLib_Parser.parse_type get_token tydict
      val _ = Library.expect_token ")" (get_token ())
      val tm = Term.mk_var (name, range)
      fun parsefn _ indices args =
        if not (List.null indices) then
          raise ERR "parse_declare_const"
            ("CPC constant " ^ name ^ " does not accept indices")
        else
          Term.list_mk_comb (tm, args)
          handle Feedback.HOL_ERR holerr =>
            raise ERR "parse_declare_const"
              ("ill-typed CPC application of " ^ name ^ ": " ^
               Feedback.message_of holerr)
    in
      (tydict, Library.extend_dict ((name, parsefn), tmdict))
    end

  fun parse_declare_fun get_token (tydict, tmdict) =
    let val (_, tmdict) = SmtLib_Parser.parse_declare_fun get_token
      (tydict, tmdict)
    in (tydict, tmdict) end

  fun parse_declare_sort get_token (tydict, tmdict) =
    let
      val name = get_token ()
      val _ = Library.expect_token "0" (get_token ())
      val _ = Library.expect_token ")" (get_token ())
      val ty = Type.mk_vartype ("'cpc_" ^ name)
      fun parsefn _ indices args =
        if List.null indices andalso List.null args then ty
        else raise ERR ("<" ^ name ^ ">") "wrong number of arguments"
    in
      (Library.extend_dict ((name, parsefn), tydict), tmdict)
    end

  fun parse_or_keep_sort_declaration dicts_ref get_token =
    let
      val tokens = declaration_tokens get_token
      val name = case tokens of name :: _ => name
        | [] => raise ERR "parse_declaration" "missing sort declaration name"
    in
      if type_declared (!dicts_ref) name then ()
      else dicts_ref := parse_declare_sort
        (Library.undo_look_ahead tokens get_token) (!dicts_ref)
    end

  fun parse_paren_name_list get_token =
    let
      fun loop acc =
        case get_token () of
          ")" => List.rev acc
        | name => loop (name :: acc)
      val first = get_token ()
    in
      if first = "(" then loop [] else [first]
    end

  (* A CPC definition is a term alias, not a HOL hypothesis.  Resolving it in
     the parser preserves sharing without granting the solver any theorem. *)
  fun parse_define dicts_ref get_token =
    let
      val name = get_token ()
      (* Most CPC definitions use SMT-LIB's ``()`` binder list, but cvc5
         also emits proof-local aliases without that list (notably for its
         @list bookkeeping values).  Both forms are nullary definitions. *)
      val definition_start = get_token ()
      val first =
        if definition_start = "(" then
          let val close = get_token () in
            if close = ")" then get_token ()
            else raise ERR "parse_define"
              "CPC parameterized definitions are unsupported"
          end
        else definition_start
      val defined_term =
        if first = "@list" then
          (* An unparenthesized @list is the same opaque resolution metadata
             as ``(@list ...)`` below. *)
          (skip_sexp get_token; NONE)
        else if first = "(" then
          let val head = get_token () in
            if head = "@list" then
              let
                fun list_terms acc =
                  let val token = get_token () in
                    if token = ")" then List.rev acc
                    else list_terms (parse_term dicts_ref
                      (Library.undo_look_ahead [token] get_token) :: acc)
                  end
                val terms = list_terms []
                val _ = add_cpc_list name terms
                val _ = Library.expect_token ")" (get_token ())
              in NONE end
            else if head = "@purify" then
              let
                val payload = parse_located_term dicts_ref get_token
                val _ = Library.expect_token ")" (get_token ())
              in
                (* CPC's purify definition names the payload and its
                   `skolem_intro` step exposes that definitional equality.
                   Keeping the alias avoids inventing an unconstrained HOL
                   variable for a proof-local sharing marker. *)
                SOME payload
              end
            else if head = "@var" then
              let
                val var_name = get_token ()
                val var_type = SmtLib_Parser.parse_type get_token
                  (#1 (!dicts_ref))
                val _ = Library.expect_token ")" (get_token ())
              in
                SOME {term = Term.mk_var (var_name, var_type),
                  provenance = AtomicProvenance}
              end
            else
              SOME (parse_located_term dicts_ref
                (Library.undo_look_ahead ["(", head] get_token))
          end
        else SOME (parse_located_term dicts_ref
          (Library.undo_look_ahead [first] get_token))
      val _ = case defined_term of
          SOME ({term, provenance} : located_term) =>
            (Library.expect_token ")" (get_token ());
             add_term dicts_ref name term;
             add_term_provenance name provenance)
        | NONE => ()
    in
      ()
    end

  fun parse_step dicts_ref version get_token =
    let
      val id = get_token ()
      val first = get_token ()
      val (conclusion, attr) =
        if first = ":rule" then (NONE, first)
        else
          let val get_token' = Library.undo_look_ahead [first] get_token in
            (SOME (parse_located_term dicts_ref get_token'), get_token ())
          end
      val _ = if attr = ":rule" then () else
        raise ERR "parse_step" "expected :rule"
      val rule_name = get_token ()
      val rule =
        case lookup_rule version rule_name of
          SOME rule => rule
        | NONE => raise ERR "parse_step" (registry_lookup_failure version rule_name)
      fun attrs premises args =
        case get_token () of
          ")" => {id = id, conclusion = conclusion, rule = rule,
                   premises = premises, args = args}
        | ":premises" => attrs (parse_paren_name_list get_token) args
        | ":args" =>
            let
              val _ = Library.expect_token "(" (get_token ())
              (* Resolution annotations such as @list are proof-search hints,
                 not premises of the kernel replay.  Preserve the rule step
                 while consuming their full s-expression syntax; this avoids
                 pretending that cvc5's private annotation vocabulary is an
                 SMT-LIB term language. *)
              fun ignore_terms () =
                let val token = get_token () in
                  if token = ")" then []
                  else (if token = "(" then skip_sexp get_token else ();
                        ignore_terms ())
                end
              fun resolution_args () =
                let
                  val first = get_token ()
                in
                  if first = ")" then []
                  else
                    let
                      (* ProofRule::RESOLUTION is annotated with the
                         polarity of its pivot in the first premise and the
                         pivot itself.  These are required to reconstruct
                         the (otherwise omitted) resolvent. *)
                      val polarity = parse_located_term dicts_ref
                        (Library.undo_look_ahead [first] get_token)
                      val pivot = parse_located_term dicts_ref get_token
                      val _ = ignore_terms ()
                    in [polarity, pivot] end
                end
              fun macro_resolution_args () =
                let
                  val first = get_token ()
                  fun parse_list_after_open () =
                    let
                      fun entries acc =
                        let val token = get_token () in
                          if token = ")" then List.rev acc
                          else entries (parse_located_term dicts_ref
                            (Library.undo_look_ahead [token] get_token) :: acc)
                        end
                    in entries [] end
                  fun parse_list token =
                    if token = "(" then
                      let
                        val _ = Library.expect_token "@list" (get_token ())
                      in parse_list_after_open () end
                    else
                      case lookup_cpc_list token of
                        SOME terms => List.map
                          (unavailable_term
                            "expanded CPC resolution-list alias") terms
                      | NONE => raise ERR "parse_step"
                          ("undefined CPC resolution @list alias " ^ token)
                in
                  if first = ")" then []
                  else
                    let
                      val target = parse_located_term dicts_ref
                        (Library.undo_look_ahead [first] get_token)
                      val next = get_token ()
                    in
                      if next = ")" then [target]
                      else
                        let
                          val polarities = parse_list next
                          val pivots = parse_list (get_token ())
                          val _ = Library.expect_token ")" (get_token ())
                        in target :: polarities @ pivots end
                    end
                end
              fun and_elim_index () =
                let
                  val text = get_token ()
                  val index =
                    case Int.fromString text of
                      SOME n => if n < 0 then raise ERR "parse_step"
                        "negative CPC and_elim index" else n
                    | NONE => raise ERR "parse_step"
                        ("non-numeral CPC and_elim index '" ^ text ^ "'")
                  val _ = Library.expect_token ")" (get_token ())
                in
                  [unavailable_term "CPC and_elim index metadata"
                    (intSyntax.mk_injected
                      (numSyntax.mk_numeral (Arbnum.fromInt index)))]
                end
              fun not_or_elim_index () =
                let
                  val text = get_token ()
                  val index =
                    case Int.fromString text of
                      SOME n => if n < 0 then raise ERR "parse_step"
                        "negative CPC not_or_elim index" else n
                    | NONE => raise ERR "parse_step"
                        ("non-numeral CPC not_or_elim index '" ^ text ^ "'")
                  val _ = Library.expect_token ")" (get_token ())
                in
                  [unavailable_term "CPC not_or_elim index metadata"
                    (intSyntax.mk_injected
                      (numSyntax.mk_numeral (Arbnum.fromInt index)))]
                end
              fun cnf_and_pos_args () =
                let
                  val first = get_token ()
                  val conjunction = parse_located_term dicts_ref
                    (Library.undo_look_ahead [first] get_token)
                  val text = get_token ()
                  val index =
                    case Int.fromString text of
                      SOME n => if n < 0 then raise ERR "parse_step"
                        "negative CPC cnf_and_pos index" else n
                    | NONE => raise ERR "parse_step"
                        ("non-numeral CPC cnf_and_pos index '" ^ text ^ "'")
                  val _ = Library.expect_token ")" (get_token ())
                in
                  [conjunction,
                   unavailable_term "CPC cnf_and_pos index metadata"
                     (intSyntax.mk_injected
                       (numSyntax.mk_numeral (Arbnum.fromInt index)))]
                end
              fun cnf_or_neg_args () =
                let
                  val first = get_token ()
                  val disjunction = parse_located_term dicts_ref
                    (Library.undo_look_ahead [first] get_token)
                  val text = get_token ()
                  val index =
                    case Int.fromString text of
                      SOME n => if n < 0 then raise ERR "parse_step"
                        "negative CPC cnf_or_neg index" else n
                    | NONE => raise ERR "parse_step"
                        ("non-numeral CPC cnf_or_neg index '" ^ text ^ "'")
                  val _ = Library.expect_token ")" (get_token ())
                in
                  [disjunction,
                   unavailable_term "CPC cnf_or_neg index metadata"
                     (intSyntax.mk_injected
                       (numSyntax.mk_numeral (Arbnum.fromInt index)))]
                end
              fun exists_elim_args () =
                let
                  val _ = Library.expect_token "(" (get_token ())
                  val _ = Library.expect_token "=" (get_token ())
                  val first = get_token ()
                  val (lhs, rhs) = if first = "(" then
                    let
                      val quantifier = get_token ()
                      val _ = if quantifier = "exists" then () else
                        raise ERR "parse_step"
                          "expected existential left side for exists-elim"
                      val binder_name = get_token ()
                      val binders =
                        case lookup_cpc_list binder_name of
                          SOME vars => vars
                        | NONE => raise ERR "parse_step"
                            ("undefined CPC @list alias " ^ binder_name)
                      val body = parse_term dicts_ref get_token
                      val _ = Library.expect_token ")" (get_token ())
                      val rhs = parse_term dicts_ref get_token
                    in (boolSyntax.list_mk_exists (binders, body), rhs) end
                    else
                      (parse_term dicts_ref
                         (Library.undo_look_ahead [first] get_token),
                       parse_term dicts_ref get_token)
                  val _ = Library.expect_token ")" (get_token ())
                  val _ = Library.expect_token ")" (get_token ())
                in
                  [unavailable_term
                    "CPC exists-elim argument reconstructed from metadata"
                    (boolSyntax.mk_eq (lhs, rhs))]
                end
              fun quant_rewrite_args () =
                let val first = get_token () in
                  if first <> "(" then
                    let
                      val proposition = parse_located_term dicts_ref
                        (Library.undo_look_ahead [first] get_token)
                      val _ = Library.expect_token ")" (get_token ())
                    in [proposition] end
                  else
                    let
                      val _ = Library.expect_token "=" (get_token ())
                      val _ = Library.expect_token "(" (get_token ())
                      val quantifier = get_token ()
                      val binder_name = get_token ()
                      val binders =
                        case lookup_cpc_list binder_name of
                          SOME vars => vars
                        | NONE => raise ERR "parse_step"
                            ("undefined CPC @list alias " ^ binder_name)
                      val body = parse_located_term dicts_ref get_token
                      val _ = Library.expect_token ")" (get_token ())
                      val rhs = parse_located_term dicts_ref get_token
                      val _ = Library.expect_token ")" (get_token ())
                      val _ = Library.expect_token ")" (get_token ())
                      val lhs = if quantifier = "forall" then
                        boolSyntax.list_mk_forall (binders, #term body)
                        else if quantifier = "exists" then
                          boolSyntax.list_mk_exists (binders, #term body)
                        else raise ERR "parse_step"
                          "expected quantified left side for CPC quantifier rewrite"
                      val binder_provenance = exact_binders quantifier binders
                        (#provenance body)
                    in
                      [{term = boolSyntax.mk_eq (lhs, #term rhs),
                        provenance = EqualityProvenance
                          (binder_provenance, #provenance rhs)}]
                    end
                end
              (* CPC Set rules carry their set sort as an argument, e.g.
                 [(Set Int)].  This is proof metadata, not a HOL term; retain
                 it only as a variable of the parsed sort so rule-specific
                 replay can ignore it without rejecting a recorded proof. *)
              fun sort_marker tokens =
                let val (tydict, _) = !dicts_ref in
                  Term.mk_var ("@cpc.sort",
                    SmtLib_Parser.parse_type
                      (Library.undo_look_ahead tokens get_token) tydict)
                end
              fun is_set_sort_metadata position =
                (rule_name = "sets-card-emp" andalso position = 2) orelse
                (rule_name = "sets-is-empty-elim" andalso position = 2) orelse
                (rule_name = "sets-member-emp" andalso position = 3) orelse
                (rule_name = "sets-minus-self" andalso position = 2)
              fun terms acc =
                let val token = get_token () in
                  if token = ")" then List.rev acc
                  else if token = "(" then
                    let val head = get_token () in
                      if head = "@list" then
                        (* Lists in CPC arguments carry a homogeneous
                           sequence of object terms (not a HOL list term).
                           Flatten them for handlers such as instantiate. *)
                        terms (List.revAppend
                          (List.map (unavailable_term
                            "expanded CPC argument-list syntax")
                            (list_terms []), acc))
                      else if head = "Set" andalso
                              is_set_sort_metadata (List.length acc + 1) then
                        let
                          val tm = sort_marker ["(", head]
                            handle Feedback.HOL_ERR holerr =>
                              raise ERR "parse_step"
                                ("could not parse Set sort metadata for CPC " ^
                                 "step " ^ id ^ " (rule " ^ rule_name ^ "): " ^
                                 Feedback.message_of holerr)
                        in terms
                          (unavailable_term "CPC Set sort metadata" tm :: acc)
                        end
                      else
                        let
                          val tm = parse_located_term dicts_ref
                            (Library.undo_look_ahead ["(", head] get_token)
                            handle Feedback.HOL_ERR holerr =>
                              raise ERR "parse_step"
                                ("could not parse :args for CPC step " ^ id ^
                                 " (rule " ^ rule_name ^ "): " ^
                                 Feedback.message_of holerr)
                        in terms (tm :: acc) end
                    end
                  else
                    (case lookup_cpc_list token of
                       SOME listed_terms =>
                         terms (List.revAppend
                           (List.map (unavailable_term
                             "expanded CPC argument-list alias") listed_terms,
                            acc))
                     | NONE =>
                         let
                           val tm = parse_located_term dicts_ref
                             (Library.undo_look_ahead [token] get_token)
                             handle Feedback.HOL_ERR holerr =>
                               raise ERR "parse_step"
                                 ("could not parse :args for CPC step " ^ id ^
                                  " (rule " ^ rule_name ^ "): " ^
                                  Feedback.message_of holerr)
                         in terms (tm :: acc) end)
                end
              and list_terms acc =
                let val token = get_token () in
                  if token = ")" then List.rev acc
                  else list_terms (parse_recorded_term dicts_ref
                    (Library.undo_look_ahead [token] get_token) :: acc)
                end
              fun cpc_list_term terms =
                case terms of
                  first :: _ => listSyntax.mk_list
                    (terms, Term.type_of first)
                | [] => listSyntax.mk_list
                    ([], Type.mk_vartype "'cpc_list")
              fun validate_set_sort_metadata args =
                let
                  fun check (set, marker) =
                    if Type.compare (Term.type_of set, Term.type_of marker) =
                         EQUAL then ()
                    else raise ERR "parse_step"
                      ("CPC Set sort metadata does not match its set argument " ^
                       "in step " ^ id ^ " (rule " ^ rule_name ^ ")")
                in
                  case (rule_name, args) of
                    ("sets-card-emp", [set, marker]) => check (set, marker)
                  | ("sets-is-empty-elim", [set, marker]) =>
                      check (set, marker)
                  | ("sets-member-emp", [_ , set, marker]) =>
                      check (set, marker)
                  | ("sets-minus-self", [set, marker]) => check (set, marker)
                  | _ => ()
                end
              fun structured_terms acc =
                let val token = get_token () in
                  if token = ")" then List.rev acc
                  else if token = "(" then
                    let val head = get_token () in
                      if head = "@list" then
                        structured_terms
                          (unavailable_term "CPC structured-list metadata"
                            (cpc_list_term (list_terms [])) :: acc)
                      else
                        let
                          val tm = parse_located_term dicts_ref
                            (Library.undo_look_ahead ["(", head]
                              get_token)
                        in structured_terms (tm :: acc) end
                    end
                  else
                    (case lookup_cpc_list token of
                       SOME listed_terms => structured_terms
                         (unavailable_term "CPC structured-list alias"
                           (cpc_list_term listed_terms) :: acc)
                     | NONE =>
                         let
                           val tm = parse_located_term dicts_ref
                             (Library.undo_look_ahead [token] get_token)
                         in structured_terms (tm :: acc) end)
                end
            in
              if rule_name = "resolution" then
                attrs premises (resolution_args ())
              else if #replay_handler rule = "resolution" then
                (* Macro/chain resolution gives its result clause first;
                   the remaining arguments only describe its pivots. *)
                attrs premises (macro_resolution_args ())
              else if #replay_handler rule = "and_elim" then
                attrs premises (and_elim_index ())
              else if #replay_handler rule = "not_or_elim" then
                attrs premises (not_or_elim_index ())
              else if #replay_handler rule = "exists_elim" then
                attrs premises (exists_elim_args ())
              else if #replay_handler rule = "quant_rewrite" then
                attrs premises (quant_rewrite_args ())
              else if rule_name = "cnf_and_pos" then
                attrs premises (cnf_and_pos_args ())
              else if rule_name = "cnf_or_neg" then
                attrs premises (cnf_or_neg_args ())
              else if rule_name = "arith-mod-over-mod" orelse
                      rule_name = "arith-mod-over-mod-mult" then
                attrs premises (structured_terms [])
              else
                let val args = terms [] in
                  (validate_set_sort_metadata
                    (List.map (fn (located : located_term) => #term located)
                      args);
                   attrs premises args)
                end
            end
        | attribute => raise ERR "parse_step"
            ("unknown CPC step attribute " ^ attribute ^
             " in cvc5 version " ^ version)
    in
      attrs [] []
    end

  fun parse_commands dicts_ref version get_token stop acc =
    let
      val token = (SOME (get_token ())) handle Feedback.HOL_ERR _ => NONE
    in
      case token of
        NONE => List.rev acc
      | SOME ")" => if stop then List.rev acc
                      else parse_commands dicts_ref version get_token stop acc
      | SOME "(" =>
          let val head = get_token () in
            case head of
              "(" =>
                let val nested = parse_commands dicts_ref version
                      (Library.undo_look_ahead ["("] get_token) true []
                in if List.null acc then nested
                   else List.rev acc end
            | "declare-const" => (parse_or_keep_term_declaration
                  parse_declare_const dicts_ref get_token;
                parse_commands dicts_ref version get_token stop acc)
            | "declare-fun" => (parse_or_keep_term_declaration
                  parse_declare_fun dicts_ref get_token;
                parse_commands dicts_ref version get_token stop acc)
            | "declare-sort" => (parse_or_keep_sort_declaration
                  dicts_ref get_token;
                parse_commands dicts_ref version get_token stop acc)
            | "declare-datatype" => (skip_sexp get_token;
                parse_commands dicts_ref version get_token stop acc)
            | "declare-datatypes" => (skip_sexp get_token;
                parse_commands dicts_ref version get_token stop acc)
            | "define" => (parse_define dicts_ref get_token;
                            parse_commands dicts_ref version get_token stop acc)
            | "assume" =>
                let val id = get_token ()
                    val tm = parse_located_term dicts_ref get_token
                    val _ = Library.expect_token ")" (get_token ())
                in parse_commands dicts_ref version get_token stop
                     (ASSUME (id, tm) :: acc) end
            | "assume-push" =>
                let val id = get_token ()
                    val tm = parse_located_term dicts_ref get_token
                    val _ = Library.expect_token ")" (get_token ())
                in parse_commands dicts_ref version get_token stop
                     (ASSUME_PUSH (id, tm) :: acc) end
            | "step" =>
                let val step = parse_step dicts_ref version get_token
                in parse_commands dicts_ref version get_token stop
                     (STEP step :: acc) end
            | "step-pop" =>
                let val step = parse_step dicts_ref version get_token
                in parse_commands dicts_ref version get_token stop
                     (STEP step :: acc) end
            | other => raise ERR "parse_commands"
                ("unknown CPC construct " ^ other ^ " in cvc5 version " ^ version)
          end
      | SOME _ => parse_commands dicts_ref version get_token stop acc
    end
in
  fun parse_stream_with_version (dicts : dicts) version instream : proof =
    let
      (* Resolve once, here: everything downstream -- rule lookup, gating and
         diagnostics -- then works with a tested version. *)
      val version = resolve_version version
      val _ = cpc_list_definitions := Redblackmap.mkDict String.compare
      val _ = cpc_list_names := []
      val _ = cpc_term_provenances := Redblackmap.mkDict String.compare
      (* CPC conclusions and arguments can contain SMT-LIB string literals.
         Preserve their token kind so the empty string is not confused with
         an empty atom by the legacy term parser. *)
      val get_token =
        SmtLib_Parser.make_proof_stream_tokenizer instream
      val commands = parse_commands (ref (with_cpc_literals dicts)) version
        get_token false []
    in
      {commands = commands, cvc_version = version}
    end

  fun parse_stream dicts instream =
    parse_stream_with_version dicts unknown_cvc_version instream

end

end
