(* Copyright (c) 2009-2011 Tjark Weber. All rights reserved. *)

(* Proof reconstruction for Z3: parsing of Z3's proofs *)

structure Z3_ProofParser =
struct

  (* I tried to implement this parser in ML-Lex/ML-Yacc, but gave up
     on that -- mainly for two reasons: 1. The whole toolchain/build
     process gets more complicated. 2. Performance and memory usage of
     the generated parser were far from satisfactory (probably because
     my naive definition of the underlying grammar required the parser
     to maintain a large stack internally). *)

local

  local open HolSmtTheory in end

  open Z3_Proof

  val ERR = Feedback.mk_HOL_ERR "Z3_ProofParser"
  val WARNING = Feedback.HOL_WARNING "Z3_ProofParser"

  (***************************************************************************)
  (* auxiliary functions                                                     *)
  (***************************************************************************)

  fun proofterm_id (name : string) : int =
    if String.isPrefix "@x" name then
      let
        val id = Option.valOf (Int.fromString (String.extract (name, 2, NONE)))
          handle Option.Option =>
            raise ERR "proofterm_id" "'@x' not followed by an integer"
      in
        if id < 1 then
          raise ERR "proofterm_id" "integer less than 1 found"
        else
          id
      end
    else
      raise ERR "proofterm_id" "'@x' prefix expected"

  (***************************************************************************)
  (* parsing Z3 proofterms as terms                                          *)
  (***************************************************************************)

  (* Z3 proofterms are essentially encoded in SMT-LIB term syntax, so
     we re-use the SMT-LIB parser. *)

  (* Limitation: the Z3 proof format does not syntactically separate a rule's
     premise proofterms from its final conclusion term.  The parser therefore
     parses proofterms and conclusion terms through one SMT-LIB term grammar,
     encoding proofterms as HOL terms of type :'pt.  If a conclusion term uses
     an identifier that is also a Z3 rule name, the term may be parsed as a
     proofterm-shaped term before replay can tell that it was the conclusion.

     A format-level fix would make premises an explicit list, e.g. by
     parenthesizing the premises before the conclusion.  See the ready-to-file
     upstream draft:
     .agent-files/reports/TASK_22_c6/upstream_issues/z3_proofterm_term_ambiguity.md *)

  val pt_ty = Type.mk_vartype "'pt"
  val th_lemma_metadata_ty = listSyntax.mk_list_type stringSyntax.string_ty

  fun zero_prems name =
    SmtLib_Theories.K_zero_one (Lib.curry Term.mk_comb (Term.mk_var
      (name, Type.--> (Type.bool, pt_ty))))

  fun one_prem name =
    SmtLib_Theories.K_zero_two (Lib.uncurry (Lib.curry Term.mk_comb o
      Lib.curry Term.mk_comb (Term.mk_var (name, boolSyntax.list_mk_fun
      ([pt_ty, Type.bool], pt_ty)))))

  fun two_prems name =
  let
    val t = Term.mk_var (name,
      boolSyntax.list_mk_fun ([pt_ty, pt_ty, Type.bool], pt_ty))
  in
    SmtLib_Theories.K_zero_three (fn (p1, p2, concl) =>
      Term.list_mk_comb (t, [p1, p2, concl]))
  end

  fun list_prems name =
    SmtLib_Theories.K_zero_list (Lib.uncurry (Lib.curry Term.mk_comb o
      (Lib.curry Term.mk_comb (Term.mk_var (name, boolSyntax.list_mk_fun
      ([listSyntax.mk_list_type pt_ty, Type.bool], pt_ty))))) o
      Lib.apfst (Lib.C (Lib.curry listSyntax.mk_list) pt_ty) o Lib.front_last)

  fun th_lemma_normalize_index_string s =
  let
    val n = String.size s
    fun all_digits_until limit i =
      i >= limit orelse
      (Char.isDigit (String.sub (s, i)) andalso
       all_digits_until limit (i + 1))
    val int_suffix =
      n > 1 andalso String.sub (s, n - 1) = #"i" andalso
      (all_digits_until (n - 1) 0 orelse
       (n > 2 andalso
        (String.sub (s, 0) = #"-" orelse String.sub (s, 0) = #"~") andalso
        all_digits_until (n - 1) 1))
  in
    if int_suffix then String.substring (s, 0, n - 1) else s
  end

  fun th_lemma_index_to_string tm =
    th_lemma_normalize_index_string (Arbint.toString (intSyntax.int_of_term tm))
    handle Feedback.HOL_ERR _ =>
      th_lemma_normalize_index_string (Lib.fst (Term.dest_var tm))
      handle Feedback.HOL_ERR _ =>
        th_lemma_normalize_index_string (Library.term_to_string tm)

  fun th_lemma_metadata_of_index_terms indices =
    case List.map th_lemma_index_to_string indices of
      theory :: subkind :: rest =>
        mk_th_lemma_metadata (theory, SOME subkind, rest)
    | theory :: [] =>
        mk_th_lemma_metadata (theory, NONE, [])
    | [] =>
        raise ERR "th_lemma_metadata_of_index_terms"
          "th-lemma rule has no theory index"

  fun th_lemma_metadata_term ({theory, subkind, indices}
      : th_lemma_metadata) =
    listSyntax.mk_list
      (List.map stringSyntax.fromMLstring
        (theory :: Option.getOpt (subkind, "") :: indices),
       stringSyntax.string_ty)

  fun th_lemma_prems name metadata prems =
  let
    val (pts, concl) = Lib.front_last prems
    val t = Term.mk_var (name, boolSyntax.list_mk_fun
      ([th_lemma_metadata_ty, listSyntax.mk_list_type pt_ty, Type.bool], pt_ty))
  in
    Term.list_mk_comb (t, [th_lemma_metadata_term metadata,
      listSyntax.mk_list (pts, pt_ty), concl])
  end

  fun list_args_zero_prems name =
    SmtLib_Theories.K_list_one (fn indices => fn term =>
      let
        val arg_types = List.map Term.type_of indices
        val fn_type = arg_types @ [Type.bool]
        val t = Term.mk_var (name, boolSyntax.list_mk_fun (fn_type, pt_ty))
        val args = indices @ [term]
      in
        Term.list_mk_comb (t, args)
      end)

  (* This function is used only to allow some symbols used as indices in indexed
     identifiers to be parsed (as terms) without the parser erroring out due to
     not having the symbols in the term dictionary. *)
  fun builtin_name name =
    SmtLib_Theories.K_zero_zero (Term.mk_var (name, Type.alpha))

  fun proof_rule_builtin (rule : proof_rule) =
    let
      val names = rule_names rule
      fun builtin name =
        case #premise_shape rule of
          ZeroPremises => SOME (name, zero_prems name)
        | OnePremise => SOME (name, one_prem name)
        | TwoPremises => SOME (name, two_prems name)
        | ListPremises => SOME (name, list_prems name)
        | TermArguments => SOME (name, list_args_zero_prems name)
    in
      if #name rule = "rewrite" orelse String.isPrefix "th-lemma-" (#name rule)
      then []
      else List.mapPartial builtin names
    end

  val proof_rule_builtin_entries =
    List.concat (List.map proof_rule_builtin proof_rule_registry)

  val z3_builtin_dict = Library.dict_from_list (proof_rule_builtin_entries @ [
    (* the following names are used as `(_ th-lemma ...)` indices. *)
    ("arith",           builtin_name "arith"),
    ("array",           builtin_name "array"),
    ("assign-bounds",   builtin_name "assign-bounds"),
    ("basic",           builtin_name "basic"),
    ("bit-blast",       builtin_name "bit-blast"),
    ("bv",              builtin_name "bv"),
    ("datatype",        builtin_name "datatype"),
    ("datatypes",       builtin_name "datatypes"),
    ("dt",              builtin_name "dt"),
    ("eq-propagate",    builtin_name "eq-propagate"),
    ("extensionality",  builtin_name "extensionality"),
    ("farkas",          builtin_name "farkas"),
    ("floating-point",  builtin_name "floating-point"),
    ("fp",              builtin_name "fp"),
    ("fpa",             builtin_name "fpa"),
    ("gomory-cut",      builtin_name "gomory-cut"),
    ("nla",             builtin_name "nla"),
    ("nia",             builtin_name "nia"),
    ("nonlinear",       builtin_name "nonlinear"),
    ("nonlinear-arith", builtin_name "nonlinear-arith"),
    ("nra",             builtin_name "nra"),
    ("re",              builtin_name "re"),
    ("regex",           builtin_name "regex"),
    ("regexp",          builtin_name "regexp"),
    ("seq",             builtin_name "seq"),
    ("sequence",        builtin_name "sequence"),
    ("sequences",       builtin_name "sequences"),
    ("str",             builtin_name "str"),
    ("string",          builtin_name "string"),
    ("strings",         builtin_name "strings"),
    (* `proof-bind` doesn't seem to have semantic value, despite the Z3 v4.12.4
       source code implying that it either introduces lambda abstractions or
       `forall` quantifiers, depending on the interpretation *)
    ("proof-bind",      SmtLib_Theories.K_zero_one Lib.I),
    (* in `rewrite` proof rules, we currently ignore the indices (if they exist) *)
    ("rewrite",         (fn token => fn indices => fn prems =>
      zero_prems "rewrite" token [] prems)),
    ("th-lemma",        SmtLib_Theories.list_list (fn token => fn indices =>
      fn prems =>
        let
          (* Parsing this rule: (_ |th-lemma| arith farkas 1 1 1)
             The vertical bars have already been eliminated in the tokenizer, so
             we're already matching "th-lemma".

             The indices will be passed as [``arith``, ``farkas``, ``1``, ``1``,
             ``1``].  Preserve them as theory/subkind/proof indices so replay
             dispatch and diagnostics can report the exact indexed rule.

             We'll change the name of the rule to "th-lemma-<theory>" which will
             later hook into the theory-specific rule processing. *)
          val metadata = th_lemma_metadata_of_index_terms indices
          val theory_str = #theory metadata
          val name = "th-lemma-" ^ theory_str
        in
          th_lemma_prems name metadata prems
        end)),
    ("trans",           two_prems "trans"),
    ("select-store",    builtin_name "select-store"),
    ("triangle-eq",     builtin_name "triangle-eq"),

    (* Z3 proof dialect shims keyed to C1:

       token/function        C1 4.x corpus status              decision
       iff                  not observed as a proof token      keep
       implies              not observed as a proof token      keep
       ~, binary            not observed as a proof token      keep
       ~, unary Int/Real    not observed as a proof token      keep
       _, negative/fraction not observed as a proof token      keep

       These are not proof rules; they let legacy and proof-local Z3 terms
       parse even when Z3 prints non-SMT-LIB spellings inside proofs.  The C1
       inventory did not show a corpus-dead extra shim to drop in the available
       4.11.2, 4.12.4, 4.13.0, 4.14.1, and 4.15.3 proofs, and Z3 2.19.1 could
       not be executed on this host.  See:
       .agent-files/reports/C1/C1_rule_inventory.md *)
    ("iff", SmtLib_Theories.K_zero_two boolSyntax.mk_eq),
    ("implies", SmtLib_Theories.K_zero_two boolSyntax.mk_imp),
    (* equivalence modulo naming *)
    ("~", SmtLib_Theories.K_zero_two boolSyntax.mk_eq),
    (* the following two are the unary arithmetic negation operator *)
    ("~", SmtLib_Theories.K_zero_one intSyntax.mk_negated),
    ("~", SmtLib_Theories.K_zero_one realSyntax.mk_negated),
    (* negative numerals and fractions such as `-3` or `1/2`, used in the
       indices of `th-lemma arith` rules but otherwise invalid SMT-LIB term
       syntax *)
    ("_", SmtLib_Theories.zero_zero (fn token =>
      let
        val negated = String.isPrefix "-" token
        val fraction = String.isSubstring "/" token
      in
        if negated orelse fraction then
          let
            (* convert to a fraction, if it isn't already *)
            val n_fraction =
              if fraction then
                token
              else
                token ^ "/1"
            val (left, right) = Lib.pair_of_list (String.fields (Lib.equal #"/")
              n_fraction)
            val numerator = Arbint.fromString left
            val denominator = Arbint.fromString right
          in
            if denominator = Arbint.one then
              realSyntax.term_of_int numerator
            else
              realSyntax.mk_div (realSyntax.term_of_int numerator,
                realSyntax.term_of_int denominator)
          end
        else
          raise ERR "<z3_builtin_dict._>" "not a negated numeral or fraction"
      end)),
    (* bit-vector constants: bvm[n] *)
    ("_", SmtLib_Theories.zero_zero (fn token =>
      if String.isPrefix "bv" token then
        let
          val args = String.extract (token, 2, NONE)
          val (value, args) = Lib.pair_of_list (String.fields (Lib.equal #"[")
            args)
          val (size, args) = Lib.pair_of_list (String.fields (Lib.equal #"]")
            args)
          val _ = args = "" orelse
            raise ERR "<z3_builtin_dict._>" "not a bit-vector constant"
          val value = Library.parse_arbnum value
          val size = Library.parse_arbnum size
        in
          wordsSyntax.mk_word (value, size)
        end
      else
        raise ERR "<z3_builtin_dict._>" "not a bit-vector constant")),
    (* mkbv: bool list -> _ word *)
    ("mkbv", SmtLib_Theories.K_zero_list (fn l =>
      bitstringSyntax.mk_v2w (listSyntax.mk_list (l, Type.bool),
        fcpSyntax.mk_int_numeric_type (List.length l)))),
    (* extract[m:n] t *)
    ("_", SmtLib_Theories.zero_one (fn token =>
      if String.isPrefix "extract[" token then
        let
          val args = String.extract (token, 8, NONE)
          val (m, args) = Lib.pair_of_list (String.fields (Lib.equal #":") args)
          val (n, args) = Lib.pair_of_list (String.fields (Lib.equal #"]") args)
          val _ = args = "" orelse
            raise ERR "<z3_builtin_dict._>" "not extract[m:n]"
          val m = Library.parse_arbnum m
          val n = Library.parse_arbnum n
          val index_type = fcpLib.index_type (Arbnum.plus1 (Arbnum.- (m, n)))
          val m = numSyntax.mk_numeral m
          val n = numSyntax.mk_numeral n
        in
          fn t => wordsSyntax.mk_word_extract (m, n, t, index_type)
        end
      else
        raise ERR "<z3_builtin_dict._>" "not extract[m:n]")),
    (* (_ extractm n) t *)
    ("_", SmtLib_Theories.one_one (fn token => fn n_tm =>
      if String.isPrefix "extract" token then
        let
          val m_str = String.extract (token, 7, NONE)
          val m = Library.parse_arbnum m_str
          val n = Arbint.toNat (intSyntax.int_of_term n_tm)
          val index_type = fcpLib.index_type (Arbnum.plus1 (Arbnum.- (m, n)))
          val (m, n) = Lib.pair_map numSyntax.mk_numeral (m, n)
        in
          fn t => wordsSyntax.mk_word_extract (m, n, t, index_type)
        end
      else
        raise ERR "<z3_builtin_dict._>" "not extract<m> n")),
    ("bvudiv_i", SmtLib_Theories.K_zero_two wordsSyntax.mk_word_div),
    ("bvurem_i", SmtLib_Theories.K_zero_two wordsSyntax.mk_word_mod),
    ("bvsmod_i", SmtLib_Theories.K_zero_two integer_wordSyntax.mk_word_smod),
    (* bvudiv0 t *)
    ("bvudiv0", SmtLib_Theories.K_zero_one (fn t =>
      let
        val zero = wordsSyntax.mk_n2w (numSyntax.zero_tm, wordsSyntax.dim_of t)
      in
        wordsSyntax.mk_word_div (t, zero)
      end)),
    (* bvurem0 t *)
    ("bvurem0", SmtLib_Theories.K_zero_one (fn t =>
      let
        val zero = wordsSyntax.mk_n2w (numSyntax.zero_tm, wordsSyntax.dim_of t)
      in
        wordsSyntax.mk_word_mod (t, zero)
      end)),
    (* array_extArray[m:n] t1 t2 *)
    ("_", SmtLib_Theories.zero_two (fn token =>
      if String.isPrefix "array_ext" token then
        (fn (t1, t2) => Term.mk_comb (boolSyntax.mk_icomb
          (Term.prim_mk_const {Thy="HolSmt", Name="array_ext"}, t1), t2))
      else
        raise ERR "<z3_builtin_dict._>" "not array_ext...")),
    (* repeatn t *)
    ("_", SmtLib_Theories.zero_one (fn token =>
      if String.isPrefix "repeat" token then
        let
          val n = Library.parse_arbnum (String.extract (token, 6, NONE))
          val n = numSyntax.mk_numeral n
        in
          fn t => wordsSyntax.mk_word_replicate (n, t)
        end
      else
        raise ERR "<z3_builtin_dict._>" "not repeat<n>")),
    (* zero_extendn t *)
    ("_", SmtLib_Theories.zero_one (fn token =>
      if String.isPrefix "zero_extend" token then
        let
          val n = Library.parse_arbnum (String.extract (token, 11, NONE))
        in
          fn t => wordsSyntax.mk_w2w (t, fcpLib.index_type
            (Arbnum.+ (fcpLib.index_to_num (wordsSyntax.dim_of t), n)))
        end
      else
        raise ERR "<z3_builtin_dict._>" "not zero_extend<n>")),
    (* sign_extendn t *)
    ("_", SmtLib_Theories.zero_one (fn token =>
      if String.isPrefix "sign_extend" token then
        let
          val n = Library.parse_arbnum (String.extract (token, 11, NONE))
        in
          fn t => wordsSyntax.mk_sw2sw (t, fcpLib.index_type
            (Arbnum.+ (fcpLib.index_to_num (wordsSyntax.dim_of t), n)))
        end
      else
        raise ERR "<z3_builtin_dict._>" "not sign_extend<n>")),
    (* rotate_leftn t *)
    ("_", SmtLib_Theories.zero_one (fn token =>
      if String.isPrefix "rotate_left" token then
        let
          val n = Library.parse_arbnum (String.extract (token, 11, NONE))
          val n = numSyntax.mk_numeral n
        in
          fn t => wordsSyntax.mk_word_rol (t, n)
        end
      else
        raise ERR "<z3_builtin_dict._>" "not rotate_left<n>"))
  ])

  (***************************************************************************)
  (* turning terms into Z3 proofterms                                        *)
  (***************************************************************************)

  val zero_prems_pt = SmtLib_Theories.one_arg

  fun proofterm_of_term version t =
  let
    val (hd, args) = boolSyntax.strip_comb t
    val name = Lib.fst (Term.dest_var hd)
      handle Feedback.HOL_ERR holerr =>
        raise ERR "proofterm_of_term"
          ("local proof subterm <" ^ Library.term_to_string t ^
           "> does not encode a Z3 proofterm: " ^ Feedback.message_of holerr)
  in
    case lookup_rule version name of
      SOME rule =>
        (proofterm_maker version (#replay_handler rule) args
          handle Feedback.HOL_ERR holerr =>
            raise ERR "proofterm_of_term"
              ("malformed Z3 proof rule '" ^ name ^ "' in local proof subterm <" ^
               Library.term_to_string t ^ ">: " ^ Feedback.message_of holerr))
    | NONE =>
        if List.null args andalso String.isPrefix "@x" name then
          ID (proofterm_id name)
        else
          raise ERR "proofterm_of_term"
            (registry_lookup_failure version name ^
             " in local proof subterm <" ^ Library.term_to_string t ^ ">")
  end

  and one_prem_pt version f =
    SmtLib_Theories.two_args (f o Lib.apfst (proofterm_of_term version))

  and two_prems_pt version f = SmtLib_Theories.three_args (fn (t1, t2, t3) =>
    f (proofterm_of_term version t1, proofterm_of_term version t2, t3))

  and list_prems_pt version f =
    SmtLib_Theories.two_args (f o Lib.apfst
      (List.map (proofterm_of_term version) o Lib.fst o listSyntax.dest_list))

  and list_args_zero_prems_pt f = f o Lib.front_last

  and th_lemma_metadata_of_term metadata_tm =
    case List.map stringSyntax.fromHOLstring
        (Lib.fst (listSyntax.dest_list metadata_tm)) of
      theory :: "" :: indices =>
        mk_th_lemma_metadata (theory, NONE, indices)
    | theory :: subkind :: indices =>
        mk_th_lemma_metadata (theory, SOME subkind, indices)
    | _ =>
        raise ERR "th_lemma_metadata_of_term"
          "malformed th-lemma metadata term"

  and th_lemma_prems_pt version f =
    SmtLib_Theories.three_args (fn (metadata_tm, pts_tm, concl) =>
      f (th_lemma_metadata_of_term metadata_tm,
         List.map (proofterm_of_term version)
          (Lib.fst (listSyntax.dest_list pts_tm)),
         concl))

  and proofterm_maker version "and_elim" = one_prem_pt version AND_ELIM
    | proofterm_maker version "apply_def" = one_prem_pt version APPLY_DEF
    | proofterm_maker version "asserted" = zero_prems_pt ASSERTED
    | proofterm_maker version "commutativity" = zero_prems_pt COMMUTATIVITY
    | proofterm_maker version "def_axiom" = zero_prems_pt DEF_AXIOM
    | proofterm_maker version "elim_unused" = zero_prems_pt ELIM_UNUSED
    | proofterm_maker version "hypothesis" = zero_prems_pt HYPOTHESIS
    | proofterm_maker version "iff_false" = one_prem_pt version IFF_FALSE
    | proofterm_maker version "iff_true" = one_prem_pt version IFF_TRUE
    | proofterm_maker version "intro_def" = zero_prems_pt INTRO_DEF
    | proofterm_maker version "lemma" = one_prem_pt version LEMMA
    | proofterm_maker version "monotonicity" =
        list_prems_pt version MONOTONICITY
    | proofterm_maker version "mp" = two_prems_pt version MP
    | proofterm_maker version "mp_eq" = two_prems_pt version MP_EQ
    | proofterm_maker version "nnf_neg" = list_prems_pt version NNF_NEG
    | proofterm_maker version "nnf_pos" = list_prems_pt version NNF_POS
    | proofterm_maker version "not_or_elim" =
        one_prem_pt version NOT_OR_ELIM
    | proofterm_maker version "quant_inst" =
        list_args_zero_prems_pt QUANT_INST
    | proofterm_maker version "quant_intro" =
        one_prem_pt version QUANT_INTRO
    | proofterm_maker version "refl" = zero_prems_pt REFL
    | proofterm_maker version "rewrite" = zero_prems_pt REWRITE
    | proofterm_maker version "skolem" = zero_prems_pt SKOLEM
    | proofterm_maker version "symm" = one_prem_pt version SYMM
    | proofterm_maker version "th_lemma[arith]" =
        th_lemma_prems_pt version TH_LEMMA_ARITH
    | proofterm_maker version "th_lemma[array]" =
        th_lemma_prems_pt version TH_LEMMA_ARRAY
    | proofterm_maker version "th_lemma[basic]" =
        th_lemma_prems_pt version TH_LEMMA_BASIC
    | proofterm_maker version "th_lemma[bv]" =
        th_lemma_prems_pt version TH_LEMMA_BV
    | proofterm_maker version "th_lemma[datatype]" =
        th_lemma_prems_pt version TH_LEMMA_DATATYPE
    | proofterm_maker version "th_lemma[advanced]" =
        th_lemma_prems_pt version TH_LEMMA_ADVANCED
    | proofterm_maker version "trans" = two_prems_pt version TRANS
    | proofterm_maker version "trans_star" = list_prems_pt version TRANS_STAR
    | proofterm_maker version "true_axiom" = zero_prems_pt TRUE_AXIOM
    | proofterm_maker version "unit_resolution" =
        list_prems_pt version UNIT_RESOLUTION
    | proofterm_maker _ handler =
        raise ERR "proofterm_maker"
          ("Z3 proof rule registry has no parser wrapper for replay handler '" ^
           handler ^ "'")

  (***************************************************************************)
  (* parsing of let definitions                                              *)
  (***************************************************************************)

  (* returns an extended proof; 't' must encode a proofterm *)
  fun extend_proof proof (id, t) =
  let
    val steps = proof_steps proof
    val version = proof_version proof
    val _ = if !Library.trace > 0 andalso
      Option.isSome (Redblackmap.peek (steps, id)) then
        WARNING "extend_proof"
          ("proofterm ID " ^ Int.toString id ^ " defined more than once")
      else ()
  in
    update_proof_steps proof
      (Redblackmap.insert (steps, id, proofterm_of_term version t))
  end

  (* Checks whether the `let` bindings are like the ones used in Z3 proof
     certificates, i.e. that there is only one binding and the name starts with
     `?x`, `$x` or `@x`. Otherwise, we'll assume it's of a real `let` expression
     as used in SMT-LIB.
     Ideally, `@x` bindings nested within `let` definitions would be treated
     specially like those being bound in the outermost `let` definitions, i.e.
     we'd create nodes in the proof graph so that we don't have to replay the
     proofs for these proofterms more than once. However, this would greatly
     complicate the parser and currently each of these nested proofterms only
     seem to be used once, so there doesn't seem to be a need to handle them
     specially. *)
  fun is_z3_proof_binding ((name, _, _) :: []) =
        String.isPrefix "?x" name orelse String.isPrefix "$x" name orelse
          String.isPrefix "@x" name
    | is_z3_proof_binding _ = false

  (* The Z3 proof certificate version of `mk_let_bindings` checks whether we are
     parsing a typical Z3 proof certificate `let` binding. If so, it binds the
     name to the corresponding term. Otherwise, it does what the SMT-LIB version
     of the parser would do. *)
  fun z3_mk_let_bindings ((tydict, tmdict), bindings)
    : Term.term SmtLib_Parser.dict =
    if is_z3_proof_binding bindings then
      (* We cannot use `Library.extend_dict_unique` because Z3 does rebind the
         same name (although when this happened, it assigned the same value). *)
      List.foldl (fn ((name, _, t), tmdict) => Library.extend_dict
        ((name, SmtLib_Theories.K_zero_zero t), tmdict)) tmdict bindings
    else
      SmtLib_Parser.smtlib_mk_let_bindings ((tydict, tmdict), bindings)

  (* The Z3 proof certificate version of `mk_let` checks whether we are parsing
     a typical Z3 proof certificate `let` binding. If so, it simply returns the
     body of the `let` expression, otherwise it does what the SMT-LIB version of
     the parser would do (i.e. create a HOL4 `let` term). *)
  fun z3_mk_let (bindings, body) : Term.term =
    if is_z3_proof_binding bindings then
      body
    else
      SmtLib_Parser.smtlib_mk_let (bindings, body)

  val z3_proof_cfg = {
    mk_let_bindings = z3_mk_let_bindings,
    mk_let = z3_mk_let,
    parse_choice = false,
    parse_lambda = true
  }

  (* distinguishes between a term definition and a proofterm
     definition; returns a (possibly extended) dictionary and proof *)
  fun parse_definition get_token (tydict, tmdict, proof) =
  let
    val _ = Library.expect_token "(" (get_token ())
    val _ = Library.expect_token "(" (get_token ())
    val name = get_token ()
    val first = get_token ()
    val (head, get_token') =
      if first = "(" then
        let
          val head = get_token ()
        in
          (head, Library.undo_look_ahead ["(", head] get_token)
        end
      else
        (first, Library.undo_look_ahead [first] get_token)
    val t = SmtLib_Parser.parse_term_with_cfg z3_proof_cfg get_token'
      (tydict, tmdict)
      handle Feedback.HOL_ERR holerr =>
        if String.isPrefix "@x" name andalso
           not (String.isPrefix "@x" head) andalso
           not (Option.isSome (lookup_rule (proof_version proof) head)) then
          raise ERR "parse_definition"
            (registry_lookup_failure (proof_version proof) head ^
             " while parsing proofterm definition '" ^ name ^ "': " ^
             Feedback.message_of holerr)
        else
          raise Feedback.HOL_ERR holerr
    val _ = Library.expect_token ")" (get_token ())
    val _ = Library.expect_token ")" (get_token ())
  in
    if String.isPrefix "@x" name then
      (* proofterm definition *)
      let
        val tmdict = Library.extend_dict_unique ((name,
          SmtLib_Theories.K_zero_zero (Term.mk_var (name, pt_ty))), tmdict)
        val proof = extend_proof proof (proofterm_id name, t)
      in
        (tmdict, proof)
      end
    else
      (* term definition *)
      (Library.extend_dict_unique ((name, SmtLib_Theories.K_zero_zero t),
        tmdict), proof)
  end

  (* Parses the actual proof expression *)
  fun parse_proof_expression get_token (tydict, tmdict, proof) (rpars : int) =
  let
    val () = Library.expect_token "(" (get_token ())
    val head = get_token ()
  in
    if head = "let" then
      let
        val (tmdict, proof) = parse_definition get_token (tydict, tmdict, proof)
      in
        parse_proof_expression get_token (tydict, tmdict, proof) (rpars + 1)
      end
    else
      let
        (* undo look-ahead of 2 tokens *)
        val get_token' = Library.undo_look_ahead ["(", head] get_token
        val version = proof_version proof
        val t = SmtLib_Parser.parse_term_with_cfg z3_proof_cfg get_token'
          (tydict, tmdict)
          handle Feedback.HOL_ERR holerr =>
            if String.isPrefix "@x" head orelse
               Option.isSome (lookup_rule version head) then
              raise Feedback.HOL_ERR holerr
            else
              raise ERR "parse_proof_expression"
                (registry_lookup_failure version head ^
                 " while parsing proof expression: " ^
                 Feedback.message_of holerr)
      in
        (* Z3 assigns no ID to the final proof step; we use ID 0 *)
        extend_proof proof (0, t) before Lib.funpow rpars
          (fn () => Library.expect_token ")" (get_token ())) ()
      end
  end

  (* Parses the initial proof declarations *)
  fun parse_proof_decl get_token (tydict, tmdict, proof) (rpars : int) =
  let
    val () = Library.expect_token "(" (get_token ())
    val head = get_token ()
  in
    if head = "proof" then
      parse_proof_expression get_token (tydict, tmdict, proof) (rpars + 1)
    else if head = "set-logic" then (
      (* Modern Z3 v4 proof output may echo the script's logic command before
         the proof expression.  It carries no declaration information for
         replay, so skip it like the surrounding proof wrapper metadata. *)
      get_token ();
      Library.expect_token ")" (get_token ());
      parse_proof_decl get_token (tydict, tmdict, proof) rpars
    )
    else if head = "declare-fun" then
      let
        val (tm, tmdict) = SmtLib_Parser.parse_declare_fun get_token (tydict, tmdict)
        val proof = update_proof_vars proof (HOLset.add (proof_vars proof, tm))
      in
        parse_proof_decl get_token (tydict, tmdict, proof) rpars
      end
    else if head = "error" then (
      (* some (otherwise valid) proofs are preceded by an error message,
         which we simply ignore *)
      get_token ();
      Library.expect_token ")" (get_token ());
      parse_proof_decl get_token (tydict, tmdict, proof) rpars
    ) else
      let
        (* undo look-ahead of 2 tokens *)
        val get_token' = Library.undo_look_ahead ["(", head] get_token
      in
        parse_proof_expression get_token' (tydict, tmdict, proof) rpars
      end
  end

  (* entry point into the parser (i.e., the grammar's start symbol)

     Z3 v2.19 proofs begin with:
     ```
     (error "...")          ; may or may not be present
     (let ...
     ```

     Z3 v4 proofs begin with:
     ```
     (                      ; note the extra parenthesis
       (declare-fun ...)    ; any number of these, maybe none
       (proof
         (let ...
     ```
     We'll try to seamlessly handle both styles of proof here. Namely,
     for v4 proofs we'll consume the extra parenthesis here and then
     continue parsing as normal. *)
  fun parse_proof get_token state =
  let
    val () = Library.expect_token "(" (get_token ())
    val token = get_token ()
  in
    if token = "let" orelse token = "error" then
      (* Z3 v2.19 proof *)
      let
        (* undo look-ahead of the 2 tokens *)
        val get_token' = Library.undo_look_ahead ["(", token] get_token
      in
        parse_proof_decl get_token' state 0
      end
    else
      (* Must be a Z3 v4 proof then *)
      let
        val () = Library.expect_token "(" token
        (* leave the 1st parenthesis consumed and undo the 2nd *)
        val get_token' = Library.undo_look_ahead ["("] get_token
      in
        parse_proof_decl get_token' state 1
      end
  end

in

  (* Similar to 'parse_file' below, but for instreams.  Does not close
     the instream. *)

  fun parse_stream_with_version ((tydict, tmdict): SmtLib_Parser.dicts)
    (z3_version : string) (instream : TextIO.instream) : proof =
  let
    (* union of user-declared names and Z3's inference rule names *)
    val tmdict = Library.union_dict tmdict z3_builtin_dict
    (* parse the stream *)
    val _ = if !Library.trace > 1 then
        Feedback.HOL_MESG "HolSmtLib: parsing Z3 proof"
      else ()
    val get_token = Library.get_token (Library.get_buffered_char instream)
    val initial_proof = empty_proof z3_version
    val proof = parse_proof get_token
      (tydict, tmdict, initial_proof)
    val _ = if !Library.trace > 0 then
        WARNING "parse_stream" ("ignoring token '" ^ get_token () ^
          "' (and perhaps others) after proof")
          handle Feedback.HOL_ERR _ => ()  (* end of stream, as expected *)
      else ()
  in
    proof
  end

  fun parse_stream dicts instream =
    parse_stream_with_version dicts unknown_z3_version instream

  (* Function 'parse_file' parses Z3's response to the SMT2
     (get-proof) command (for an unsatisfiable problem, with proofs
     enabled in Z3, i.e., using option "PROOF_MODE=2").  It has been
     tested with proofs generated by Z3 2.13 (which was released in
     October 2010).  'parse_file' takes three arguments: two
     dictionaries mapping names of types and terms (namely those
     declared in the SMT-LIB benchmark) to lists of parsing functions
     (cf. 'SmtLib_Parser.parse_file'); and the name of the proof
     file. *)

  fun parse_file_with_version (tydict, tmdict) (z3_version : string)
    (path : string) : proof =
  let
    val instream = TextIO.openIn path
  in
    parse_stream_with_version (tydict, tmdict) z3_version instream
      before TextIO.closeIn instream
  end

  fun parse_file dicts path =
    parse_file_with_version dicts unknown_z3_version path

end  (* local *)

end
