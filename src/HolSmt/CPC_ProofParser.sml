(* Parsing cvc5's native CPC proof scripts. *)

structure CPC_ProofParser =
struct

local
  open CPC_Proof

  val ERR = Feedback.mk_HOL_ERR "CPC_ProofParser"

  type dicts = SmtLib_Parser.dicts

  val cpc_cfg : SmtLib_Parser.parser_cfg = {
    mk_let_bindings = SmtLib_Parser.smtlib_mk_let_bindings,
    mk_let = SmtLib_Parser.smtlib_mk_let,
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
    if List.null indices andalso List.null args andalso
       (String.isPrefix "-" token orelse String.isSubstring "/" token) then
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

  fun with_cpc_literals (tydict, tmdict) =
    let
      (* The source translation dictionary is deliberately as narrow as its
         declared logic.  CPC arithmetic lemmas may nevertheless contain
         rationals and their Real coercions, so add the mixed arithmetic
         overloads only while reading the proof. *)
      val tmdict = Library.union_dict tmdict SmtLib_Theories.Reals_Ints.tmdict
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
    in
    (tydict, Library.extend_dict
      (("@quantifiers_skolemize", cpc_quantifiers_skolemize_parsefn),
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
      Library.extend_dict (("@bit", cpc_bv_parsefn),
      Library.extend_dict (("@from_bools", cpc_bv_parsefn),
      Library.extend_dict (("@bvsize", cpc_bv_parsefn),
        Library.extend_dict (("@bv", cpc_bv_parsefn),
          Library.extend_dict (("_", cpc_literal_parsefn), tmdict)))))))))))))))))))
    end

  (* @list is CPC's compact representation for a list of binders or
     resolution annotations.  It is not an SMT-LIB term, so retain only the
     binder-list payload needed when it is referenced by a later quantifier. *)
  val cpc_list_definitions = ref (Redblackmap.mkDict String.compare)
  val cpc_list_names = ref ([] : string list)

  fun add_cpc_list name terms =
    (cpc_list_definitions := Redblackmap.insert
       (!cpc_list_definitions, name, terms);
     cpc_list_names := name :: !cpc_list_names)

  fun lookup_cpc_list name =
    SOME (Redblackmap.find (!cpc_list_definitions, name))
    handle Redblackmap.NotFound => NONE

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
                val payload = parse_term dicts_ref get_token
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
                SOME (Term.mk_var (var_name, var_type))
              end
            else
              SOME (parse_term dicts_ref
                (Library.undo_look_ahead ["(", head] get_token))
          end
        else SOME (parse_term dicts_ref
          (Library.undo_look_ahead [first] get_token))
      val _ = case defined_term of
          SOME tm => (Library.expect_token ")" (get_token ());
                      add_term dicts_ref name tm)
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
          let val get_token' = Library.undo_look_ahead [first] get_token
          in (SOME (parse_term dicts_ref get_token'), get_token ()) end
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
                      val polarity = parse_term dicts_ref
                        (Library.undo_look_ahead [first] get_token)
                      val pivot = parse_term dicts_ref get_token
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
                          else entries (parse_term dicts_ref
                            (Library.undo_look_ahead [token] get_token) :: acc)
                        end
                    in entries [] end
                in
                  if first = ")" then []
                  else
                    let
                      val target = parse_term dicts_ref
                        (Library.undo_look_ahead [first] get_token)
                      val next = get_token ()
                    in
                      if next <> "(" then (ignore_terms (); [target])
                      else
                        let val head = get_token () in
                          if head <> "@list" then
                            (skip_sexp get_token; ignore_terms (); [target])
                          else
                            let
                              val polarities = parse_list_after_open ()
                              val _ = Library.expect_token "(" (get_token ())
                              val _ = Library.expect_token "@list" (get_token ())
                              val pivots = parse_list_after_open ()
                              val _ = Library.expect_token ")" (get_token ())
                            in target :: polarities @ pivots end
                        end
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
                  [intSyntax.mk_injected
                    (numSyntax.mk_numeral (Arbnum.fromInt index))]
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
                  [intSyntax.mk_injected
                    (numSyntax.mk_numeral (Arbnum.fromInt index))]
                end
              fun cnf_and_pos_args () =
                let
                  val first = get_token ()
                  val conjunction = parse_term dicts_ref
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
                  [conjunction, intSyntax.mk_injected
                    (numSyntax.mk_numeral (Arbnum.fromInt index))]
                end
              fun cnf_or_neg_args () =
                let
                  val first = get_token ()
                  val disjunction = parse_term dicts_ref
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
                  [disjunction, intSyntax.mk_injected
                    (numSyntax.mk_numeral (Arbnum.fromInt index))]
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
                  [boolSyntax.mk_eq (lhs, rhs)]
                end
              fun quant_rewrite_args () =
                let
                  val _ = Library.expect_token "(" (get_token ())
                  val _ = Library.expect_token "=" (get_token ())
                  val _ = Library.expect_token "(" (get_token ())
                  val quantifier = get_token ()
                  val binder_name = get_token ()
                  val binders =
                    case lookup_cpc_list binder_name of
                      SOME vars => vars
                    | NONE => raise ERR "parse_step"
                        ("undefined CPC @list alias " ^ binder_name)
                  val body = parse_term dicts_ref get_token
                  val _ = Library.expect_token ")" (get_token ())
                  val rhs = parse_term dicts_ref get_token
                  val _ = Library.expect_token ")" (get_token ())
                  val _ = Library.expect_token ")" (get_token ())
                  val lhs = if quantifier = "forall" then
                    boolSyntax.list_mk_forall (binders, body)
                    else if quantifier = "exists" then
                      boolSyntax.list_mk_exists (binders, body)
                    else raise ERR "parse_step"
                      "expected quantified left side for CPC quantifier rewrite"
                in [boolSyntax.mk_eq (lhs, rhs)] end
              fun terms acc =
                let val token = get_token () in
                  if token = ")" then List.rev acc
                  else if token = "(" then
                    let val head = get_token () in
                      if head = "@list" then
                        (* Lists in CPC arguments carry a homogeneous
                           sequence of object terms (not a HOL list term).
                           Flatten them for handlers such as instantiate. *)
                        terms (List.revAppend (list_terms [], acc))
                      else
                        let
                          val tm = parse_term dicts_ref
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
                         terms (List.revAppend (listed_terms, acc))
                     | NONE =>
                         let
                           val tm = parse_term dicts_ref
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
                  else list_terms (parse_term dicts_ref
                    (Library.undo_look_ahead [token] get_token) :: acc)
                end
              fun cpc_list_term terms =
                case terms of
                  first :: _ => listSyntax.mk_list
                    (terms, Term.type_of first)
                | [] => listSyntax.mk_list
                    ([], Type.mk_vartype "'cpc_list")
              fun structured_terms acc =
                let val token = get_token () in
                  if token = ")" then List.rev acc
                  else if token = "(" then
                    let val head = get_token () in
                      if head = "@list" then
                        structured_terms
                          (cpc_list_term (list_terms []) :: acc)
                      else
                        let
                          val tm = parse_term dicts_ref
                            (Library.undo_look_ahead ["(", head]
                              get_token)
                        in structured_terms (tm :: acc) end
                    end
                  else
                    (case lookup_cpc_list token of
                       SOME listed_terms => structured_terms
                         (cpc_list_term listed_terms :: acc)
                     | NONE =>
                         let
                           val tm = parse_term dicts_ref
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
              else attrs premises (terms [])
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
                    val tm = parse_term dicts_ref get_token
                    val _ = Library.expect_token ")" (get_token ())
                in parse_commands dicts_ref version get_token stop
                     (ASSUME (id, tm) :: acc) end
            | "assume-push" =>
                let val id = get_token ()
                    val tm = parse_term dicts_ref get_token
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
      val get_token = Library.get_token (Library.get_buffered_char instream)
      val commands = parse_commands (ref (with_cpc_literals dicts)) version
        get_token false []
    in
      {commands = commands, cvc_version = version}
    end

  fun parse_stream dicts instream =
    parse_stream_with_version dicts unknown_cvc_version instream

end

end
