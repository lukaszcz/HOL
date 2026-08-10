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

  local open HolSmtTheory smtstringz3Theory in end

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
     parenthesizing the premises before the conclusion.  That is an upstream
     Z3 change; nothing here can remove the ambiguity on its own. *)

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

  fun z3_leftassoc name make args =
    case args of
      first :: second :: rest =>
        List.foldl (fn (next, result) => make (result, next))
          (make (first, second)) rest
    | _ => raise ERR ("<z3_builtin_dict." ^ name ^ ">")
        "at least two arguments expected"

  (***************************************************************************)
  (* Z3-internal Unicode-string symbols                                      *)
  (***************************************************************************)

  val z3_string_ty =
    Type.mk_thy_type {Thy = "smtstring", Tyop = "smtstr", Args = []}
  val z3_char_width = Arbnum.fromInt 18
  val z3_char_index_ty = fcpLib.index_type z3_char_width
  val z3_char_ty = wordsSyntax.mk_word_type z3_char_index_ty

  fun z3_char_to_num c = wordsSyntax.mk_w2n c

  fun z3_num_to_char n =
    wordsSyntax.mk_n2w (n, z3_char_index_ty)

  fun z3_string_const name =
    Term.prim_mk_const {Thy = "smtstringz3", Name = name}

  fun z3_string_app name args =
    Term.list_mk_comb (z3_string_const name, args)

  fun smtstring_app name args =
    Term.list_mk_comb
      (Term.prim_mk_const {Thy = "smtstring", Name = name}, args)

  fun apply_native_const const args =
    let
      fun apply_one (arg, rator) =
        let
          val (domain, _) = Type.dom_rng (Term.type_of rator)
        in
          Term.mk_comb (Term.inst
            (Type.match_type domain (Term.type_of arg)) rator, arg)
        end
    in
      List.foldl apply_one const args
    end

  fun holsmt_app name args =
    apply_native_const
      (Term.prim_mk_const {Thy = "HolSmt", Name = name}) args

  fun rich_list_app name args =
    apply_native_const
      (Term.prim_mk_const {Thy = "rich_list", Name = name}) args

  fun is_z3_string tm = Type.compare (Term.type_of tm, z3_string_ty) = EQUAL

  fun seq_extract (s, i, n) =
    if is_z3_string s then smtstring_app "smtstr_substr" [s, i, n]
    else
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

  fun seq_at (s, i) =
    if is_z3_string s then smtstring_app "smtstr_at" [s, i]
    else
      let
        val invalid = boolSyntax.mk_disj
          (intSyntax.mk_less (i, intSyntax.zero_tm),
           numSyntax.mk_leq (listSyntax.mk_length s, intSyntax.mk_Num i))
        val empty = listSyntax.mk_nil (listSyntax.eltype s)
      in
        boolSyntax.mk_cond (invalid, empty,
          listSyntax.mk_cons (listSyntax.mk_el (intSyntax.mk_Num i, s),
            empty))
      end

  fun z3_natural tm =
    numSyntax.mk_numeral (Arbint.toNat (intSyntax.int_of_term tm))

  fun z3_same_index expected actual =
    Term.same_const expected actual orelse Term.aconv expected actual

  fun z3_indexed_unary name make =
    let val marker = z3_string_const name
    in
      fn _ => fn indices => fn args =>
        case (indices, args) of
          ([], []) => marker
        | ([], [x]) => make x
        | ([index], [x]) =>
            if z3_same_index marker index then make x
            else raise ERR ("<z3_string_dict." ^ name ^ ">")
              "unexpected self index"
        | _ => raise ERR ("<z3_string_dict." ^ name ^ ">")
            "at most one self index and one argument expected"
    end

  fun z3_indexed_binary name make =
    let val marker = z3_string_const name
    in
      fn _ => fn indices => fn args =>
        case (indices, args) of
          ([], []) => marker
        | ([], [x, y]) => make (x, y)
        | ([index], [x, y]) =>
            if z3_same_index marker index then make (x, y)
            else raise ERR ("<z3_string_dict." ^ name ^ ">")
              "unexpected self index"
        | _ => raise ERR ("<z3_string_dict." ^ name ^ ">")
            "at most one self index and two arguments expected"
    end

  fun z3_string_witness_specs version =
    let
      val common =
        ["seq.prefix.c", "seq.prefix.d", "seq.prefix.x",
         "seq.prefix.y", "seq.prefix.z",
         "str.<.c", "str.<.d", "str.<.x", "str.<.y", "str.<.z"]
      val names =
        case version of
          "4.11.2" => common
        | "4.12.4" => common @ ["seq.p.suffix"]
        | "4.13.0" => common @ ["seq.p.suffix"]
        | "4.14.1" => common @ ["seq.p.suffix"]
        | "4.15.3" => common @ ["seq.p.suffix"]
        | _ => raise ERR "z3_string_witness_specs"
            ("no pinned string-proof inventory for Z3 " ^ version)
      fun result_ty name =
        if String.isSuffix ".c" name orelse String.isSuffix ".d" name then
          z3_char_ty
        else z3_string_ty
      fun witness name =
        let
          val ty = boolSyntax.list_mk_fun
            ([z3_string_ty, z3_string_ty], result_ty name)
        in
          (name, Term.mk_var (name, ty))
        end
    in
      List.map witness names
    end

  fun z3_string_witness_entry (name, witness) =
    (name, fn _ => fn indices => fn args =>
      case (indices, args) of
        ([], []) => witness
      | ([index], [x, y]) =>
          if Term.aconv index witness then
            Term.list_mk_comb (witness, [x, y])
          else
            raise ERR ("<z3_string_dict." ^ name ^ ">")
              "unexpected self index"
      | _ => raise ERR ("<z3_string_dict." ^ name ^ ">")
          "one self index and two arguments expected")

  fun z3_bits2char bits =
    let
      val zero = wordsSyntax.mk_word (Arbnum.zero, z3_char_width)
      fun add_bit ([], 18, sum) = sum
        | add_bit (bit :: rest, index, sum) =
            let
              val weight = wordsSyntax.mk_word
                (Arbnum.pow (Arbnum.two, Arbnum.fromInt index),
                 z3_char_width)
              val contribution =
                boolSyntax.mk_cond (bit, weight, zero)
            in
              add_bit (rest, index + 1,
                wordsSyntax.mk_word_or (sum, contribution))
            end
        | add_bit _ = raise ERR "<z3_string_dict.bits2char>"
            "exactly 18 Boolean arguments expected"
    in
      add_bit (bits, 0, zero)
    end

  (* Z3 treats String as (Seq Char).  Keep the Phase-4 smtstr carrier at
     that one sequence instance; every other Seq A remains A list. *)
  fun z3_sequence_ty element =
    if Type.compare (element, z3_char_ty) = EQUAL then
      Type.mk_thy_type {Thy = "smtstring", Tyop = "smtstr", Args = []}
    else
      SmtLib_Theories.sequence_ty element

  (* The legacy Z3 proof grammar represents the sort annotation in
     `(as seq.empty (Seq Int))` as a term-shaped index.  These markers are
     consumed only by the proof-local `seq.empty` entry below; they preserve
     the element type without admitting a term-level Seq sort. *)
  val z3_int_sort_marker = intSyntax.zero_tm
  val z3_char_sort_marker = z3_num_to_char numSyntax.zero_tm

  fun z3_seq_sort_marker element =
    listSyntax.mk_nil (Term.type_of element)

  fun z3_seq_empty marker =
    case Lib.total listSyntax.dest_list_type (Term.type_of marker) of
      SOME element =>
        if Type.compare (element, z3_char_ty) = EQUAL then
          SmtLib_String_Literal.mk_string_term ""
        else
          listSyntax.mk_nil element
    | NONE => raise ERR "<z3_string_dict.seq.empty>"
        "expected a Seq sort marker"

  val z3_empty_marker = listSyntax.mk_nil intSyntax.int_ty

  fun z3_as_seq_empty (empty, marker) =
    if Term.aconv empty z3_empty_marker then z3_seq_empty marker
    else raise ERR "<z3_string_dict.as>" "not a seq.empty annotation"

  val z3_string_tydict = Library.dict_from_list [
    ("Char", SmtLib_Theories.K_zero_zero z3_char_ty),
    ("Seq", SmtLib_Theories.K_zero_one z3_sequence_ty)
  ]

  fun z3_string_tmdict version =
    let
      val string_witnesses = z3_string_witness_specs version
      val entries = [
        ("_", SmtLib_Theories.zero_zero (fn token =>
          case SmtLib_Parser.proof_string_token token of
            SOME value =>
              (SmtLib_String_Literal.mk_string_term value
               handle SmtLib_String_Literal.InvalidStringLiteral detail =>
                 raise ERR "<z3_string_dict._>" detail)
          | NONE => raise ERR "<z3_string_dict._>"
              "not a proof string literal")),
        ("re.diff", SmtLib_Theories.K_zero_two (fn (x, y) =>
          if Library.same_const
              (Term.prim_mk_const
                {Thy = "smtstring", Name = "reglan_all"}) x then
            (* Z3 canonicalizes re.diff re.all R to re.comp R in proofs.
               Keep that proof-local alias canonical without changing the
               ordinary SMT-LIB surface dictionary. *)
            Term.list_mk_comb
              (Term.prim_mk_const
                {Thy = "smtstring", Name = "reglan_comp"}, [y])
          else
            Term.list_mk_comb
              (Term.prim_mk_const
                {Thy = "smtstring", Name = "reglan_diff"}, [x, y]))),
        ("Char", fn _ => fn indices => fn args =>
          case (indices, args) of
            ([code], []) => z3_num_to_char (z3_natural code)
          | ([], []) => z3_char_sort_marker
          | _ => raise ERR "<z3_string_dict.Char>"
              "one code-point index or a sort marker expected"),
        ("Int", SmtLib_Theories.K_zero_zero z3_int_sort_marker),
        ("Seq", SmtLib_Theories.K_zero_one z3_seq_sort_marker),
        ("seq.empty", fn _ => fn indices => fn args =>
          case (indices, args) of
            ([], []) => z3_empty_marker
          | ([marker], []) => z3_seq_empty marker
          | ([], [marker]) => z3_seq_empty marker
          | _ => raise ERR "<z3_string_dict.seq.empty>"
              "one Seq sort annotation and no arguments expected"),
        ("as", SmtLib_Theories.K_zero_two z3_as_seq_empty),
        (* These aliases keep Z3's public (Seq Char) surface on the same
           smtstr carrier as String, rather than falling through to the
           generic list builders. *)
        ("seq.++", SmtLib_Theories.K_zero_two
          (fn (s, t) => if is_z3_string s then
             smtstring_app "smtstr_concat" [s, t]
           else listSyntax.mk_append (s, t))),
        ("seq.len", SmtLib_Theories.K_zero_one
          (fn s => if is_z3_string s then smtstring_app "smtstr_len" [s]
                   else Term.mk_comb
                     (intSyntax.int_injection, listSyntax.mk_length s))),
        ("seq.extract", SmtLib_Theories.K_zero_three seq_extract),
        ("seq.at", SmtLib_Theories.K_zero_two seq_at),
        ("seq.nth", SmtLib_Theories.K_zero_two
          (fn (s, i) => if is_z3_string s then z3_num_to_char
             (z3_string_app "seq_nth_i" [s, intSyntax.mk_Num i])
           else holsmt_app "smt_seq_nth" [s, i])),
        ("seq.contains", SmtLib_Theories.K_zero_two
          (fn (s, t) => if is_z3_string s then
             smtstring_app "smtstr_contains" [s, t]
           else rich_list_app "IS_SUBLIST" [s, t])),
        ("seq.indexof", SmtLib_Theories.K_zero_three
          (fn (s, t, i) => if is_z3_string s then
             smtstring_app "smtstr_indexof" [s, t, i]
           else holsmt_app "smt_seq_indexof" [s, t, i])),
        ("seq.replace", SmtLib_Theories.K_zero_three
          (fn (s, t, u) => if is_z3_string s then
             smtstring_app "smtstr_replace" [s, t, u]
           else holsmt_app "smt_seq_replace" [s, t, u])),
        ("seq.prefixof", SmtLib_Theories.K_zero_two
          (fn (s, t) => if is_z3_string s then
             smtstring_app "smtstr_prefixof" [s, t]
           else listSyntax.mk_isprefix (s, t))),
        ("seq.suffixof", SmtLib_Theories.K_zero_two
          (fn (s, t) => if is_z3_string s then
             smtstring_app "smtstr_suffixof" [s, t]
           else rich_list_app "IS_SUFFIX" [t, s])),
        ("seq.unit", SmtLib_Theories.K_zero_one
          (fn c => if Type.compare (Term.type_of c, z3_char_ty) = EQUAL then
             z3_string_app "seq_unit" [z3_char_to_num c]
           else listSyntax.mk_cons
             (c, listSyntax.mk_nil (Term.type_of c)))),
        (* Z3 exposes these internal helpers in Seq proof certificates.  They
           have String-specific meanings only on the smtstr carrier; for a
           genuine Seq A certificate, reconstruct their native list forms.
           The nth_i/tail uses are guarded by Z3's in-range branch, while
           nth_u is deliberately the existing totalized Seq access. *)
        ("seq.nth_i", SmtLib_Theories.K_zero_two
          (fn (s, i) => if is_z3_string s then z3_num_to_char
             (z3_string_app "seq_nth_i" [s, z3_natural i])
           else listSyntax.mk_el (z3_natural i, s))),
        ("seq.nth_u", SmtLib_Theories.K_zero_two
          (fn (s, i) => if is_z3_string s then z3_num_to_char
             (z3_string_app "seq_nth_i" [s, z3_natural i])
           else holsmt_app "smt_seq_nth" [s, i])),
        ("seq.tail", z3_indexed_binary "seq_tail"
          (fn (s, i) => if is_z3_string s then z3_string_app "seq_tail"
             [s, z3_natural i]
           else listSyntax.mk_drop
             (numSyntax.mk_plus (z3_natural i,
               numSyntax.mk_numeral Arbnum.one), s))),
        ("seq.eq", z3_indexed_binary "seq_eq"
          (fn (s, t) => if is_z3_string s then z3_string_app "seq_eq" [s, t]
           else boolSyntax.mk_eq (s, t))),
        ("seq.stoi", z3_indexed_binary "seq_stoi"
          (fn (s, i) => z3_string_app "seq_stoi"
            [s, z3_natural i])),
        ("seq.digit2int", z3_indexed_unary "seq_digit2int"
          (fn c => z3_string_app "seq_digit2int"
            [z3_char_to_num c])),
        ("seq.digit", SmtLib_Theories.K_zero_one
          (fn c => z3_string_app "seq_digit" [z3_char_to_num c])),
        ("char.is_digit", SmtLib_Theories.K_zero_one
          (fn c => z3_string_app "char_is_digit"
            [z3_char_to_num c])),
        ("char.<=", SmtLib_Theories.K_zero_two
          (fn (c, d) => numSyntax.mk_leq
            (z3_char_to_num c, z3_char_to_num d))),
        ("bits2char", fn _ => fn indices => fn args =>
          case (indices, args) of
            ([], []) => Term.mk_var ("bits2char", Type.alpha)
          | ([marker], bits) =>
              if Term.is_var marker andalso
                 Lib.fst (Term.dest_var marker) = "bits2char" then
                z3_bits2char bits
              else
                raise ERR "<z3_string_dict.bits2char>"
                  "unexpected self index"
          | _ => raise ERR "<z3_string_dict.bits2char>"
              "one self index and 18 arguments expected"),
        ("char.bit", fn _ => fn indices => fn args =>
          case (indices, args) of
            ([marker, bit], [c]) =>
              if Term.is_var marker andalso
                 Lib.fst (Term.dest_var marker) = "char.bit" then
                z3_string_app "char_bit"
                  [z3_natural bit, z3_char_to_num c]
              else
                raise ERR "<z3_string_dict.char.bit>"
                  "unexpected self index"
          | ([], []) => Term.mk_var ("char.bit", Type.alpha)
          | _ => raise ERR "<z3_string_dict.char.bit>"
              "self index, bit index, and one argument expected"),
        ("aut.accept", fn _ => fn indices => fn args =>
          case (indices, args) of
            ([marker], [s, state, re]) =>
              if Term.is_var marker andalso
                 Lib.fst (Term.dest_var marker) = "aut.accept" then
                z3_string_app "aut_accept"
                  [s, z3_natural state, re]
              else
                raise ERR "<z3_string_dict.aut.accept>"
                  "unexpected self index"
          | ([], []) => Term.mk_var ("aut.accept", Type.alpha)
          | _ => raise ERR "<z3_string_dict.aut.accept>"
              "one self index and three arguments expected")
      ]
    in
      Library.dict_from_list
        (entries @ List.map z3_string_witness_entry string_witnesses)
    end

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
      if #name rule = "proof-bind" orelse #name rule = "rewrite" orelse
         String.isPrefix "th-lemma-" (#name rule) then []
      else List.mapPartial builtin names
    end

  val proof_rule_builtin_entries =
    List.concat (List.map proof_rule_builtin proof_rule_registry)

  val z3_builtin_dict = Library.dict_from_list (proof_rule_builtin_entries @ [
    (* Z3 may retain the SMT-LIB Reals_Ints predicate in proof conclusions.
       Keep it available even when the translation-local inverse dictionary
       recorded the asserted application as a nullary term. *)
    ("is_int", SmtLib_Theories.K_zero_one intrealSyntax.mk_is_int),
    (* the following names are used as `(_ th-lemma ...)` indices. *)
    ("arith",           builtin_name "arith"),
    ("array",           builtin_name "array"),
    ("assign-bounds",   builtin_name "assign-bounds"),
    ("basic",           builtin_name "basic"),
    ("bit-blast",       builtin_name "bit-blast"),
    ("bv",              builtin_name "bv"),
    ("char",            builtin_name "char"),
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
    (* Keep the lambda operand intact until [proofterm_maker] separates its
       bound variables from its proofterm body.  The marker is assigned the
       result type :'pt so it can occur among an enclosing rule's premises. *)
    ("proof-bind", SmtLib_Theories.K_zero_one (fn operand =>
      Term.mk_comb (Term.mk_var ("proof-bind",
        Type.--> (Term.type_of operand, pt_ty)), operand))),
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

    (* Z3 proof dialect shims, keyed to a rule inventory measured over the
       4.11.2, 4.12.4, 4.13.0, 4.14.1, and 4.15.3 proof corpora:

       token/function        4.x corpus status                 decision
       iff                  not observed as a proof token      keep
       implies              not observed as a proof token      keep
       ~, binary            not observed as a proof token      keep
       ~, unary Int/Real    not observed as a proof token      keep
       _, negative/fraction not observed as a proof token      keep

       These are not proof rules; they let proof-local Z3 terms parse even
       when Z3 prints non-SMT-LIB spellings inside proofs.  The inventory did
       not show a corpus-dead extra shim to drop in those proofs, so all of
       them are kept. *)
    ("iff", SmtLib_Theories.K_zero_two boolSyntax.mk_eq),
    ("implies", SmtLib_Theories.K_zero_two boolSyntax.mk_imp),
    (* fpa2bv uses Z3's n-ary extension of otherwise binary BV operators. *)
    ("concat", SmtLib_Theories.K_zero_list
      (z3_leftassoc "concat" wordsSyntax.mk_word_concat)),
    ("bvadd", SmtLib_Theories.K_zero_list
      (z3_leftassoc "bvadd" wordsSyntax.mk_word_add)),
    ("bvor", SmtLib_Theories.K_zero_list
      (z3_leftassoc "bvor" wordsSyntax.mk_word_or)),
    ("bvredand", SmtLib_Theories.K_zero_one wordsSyntax.mk_reduce_and),
    ("bvredor", SmtLib_Theories.K_zero_one wordsSyntax.mk_reduce_or),
    (* Z3's symbolic fp.to_real bridge contains its internal real-power
       operator.  HOL's ordinary [pow] has a natural exponent, so preserve
       this proof-local operator without assigning it the wrong semantics. *)
    ("^", SmtLib_Theories.K_zero_two (fn (base, exponent) =>
      Term.list_mk_comb
        (Term.mk_var ("z3_real_pow", boolSyntax.list_mk_fun
          ([realSyntax.real_ty, realSyntax.real_ty], realSyntax.real_ty)),
         [base, exponent]))),
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
    (* Z3's internal mkbv arguments run from LSB to MSB, whereas HOL's
       v2w list runs from MSB to LSB. *)
    ("mkbv", SmtLib_Theories.K_zero_list (fn l =>
      bitstringSyntax.mk_v2w (listSyntax.mk_list (List.rev l, Type.bool),
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
    (* In [(_ map f) ...], Z3 treats the lifted function as an index rather
       than as an applied term.  The recorded Set slice uses Boolean [and],
       [or], and [not]; the Bag slice uses Int addition.  Preserve precisely
       those observed typed operators for the checked pointwise lowering. *)
    ("+", SmtLib_Theories.zero_zero (fn token =>
      if token = "+" then intSyntax.plus_tm
      else raise ERR "<z3_builtin_dict.+>" "not an Int addition")),
    ("and", SmtLib_Theories.zero_zero (fn token =>
      if token = "and" then boolSyntax.conjunction
      else raise ERR "<z3_builtin_dict.and>" "not a Boolean conjunction")),
    ("or", SmtLib_Theories.zero_zero (fn token =>
      if token = "or" then boolSyntax.disjunction
      else raise ERR "<z3_builtin_dict.or>" "not a Boolean disjunction")),
    ("not", SmtLib_Theories.zero_zero (fn token =>
      if token = "not" then boolSyntax.negation
      else raise ERR "<z3_builtin_dict.not>" "not a Boolean negation")),
    (* Z3's ArraysEx [(_ map f) a b] denotes the pointwise lift of [f].
       It is not part of SMT-LIB's ArraysEx dictionary, but Z3 emits it for
       the Int-array representation of bags.  Reconstructing the lambda is
       checked by ordinary beta/update replay; accepting only its indexed
       spelling keeps arbitrary proof-local indexed identifiers on the
       existing fallback path. *)
    ("_", fn token => fn indices => fn arrays =>
      let
        val _ = token = "map" orelse
          raise ERR "<z3_builtin_dict._>" "not an array map"
        val f =
          case indices of
            [f] => f
          | _ => raise ERR "<z3_builtin_dict._>" "map needs one function"
        val first =
          case arrays of
            first :: _ => first
          | [] => raise ERR "<z3_builtin_dict._>" "map needs arrays"
        val (domain, _) = Type.dom_rng (Term.type_of first)
        val x = Term.variant
          (List.concat (List.map Term.free_vars (f :: arrays)))
          (Term.mk_var ("array_map_x", domain))
        (* A nested map is often immediately selected by its parent map.
           Contract that beta redex while parsing, so the recorded Set
           lowering [(_ map and) a ((_ map not) b)] reaches replay as the
           pointwise [a x /\ ~b x] proposition rather than an opaque lambda
           application. *)
        fun has_update tm = Lib.can (HolKernel.find_term
          combinSyntax.is_update_comb) tm
        fun select array =
          case Lib.total Term.dest_abs array of
            SOME (variable, body) =>
              (* Keep a map over a store as an explicit application.  Z3's
                 following monotonicity step supplies exactly the equality
                 between these functions; contracting just one side would
                 obscure that checked congruence. *)
              if has_update body then Term.mk_comb (array, x)
              else Term.subst [{redex = variable, residue = x}] body
          | NONE => Term.mk_comb (array, x)
        val selections = List.map select arrays
      in
        Term.mk_abs (x, Term.list_mk_comb (f, selections))
      end),
    (* Z3 prints both legacy array_extArray[m:n] and indexed
       `(_ array-ext 0)` spellings across the pinned proof corpus. *)
    ("_", fn token => fn indices => fn args =>
      let
        val legacy = String.isPrefix "array_ext" token
        val indexed = token = "array-ext" andalso
          (case indices of
             [index] => intSyntax.int_of_term index = Arbint.zero
           | _ => false)
          handle Feedback.HOL_ERR _ => false
        val _ = if (legacy andalso List.null indices) orelse indexed then ()
          else raise ERR "<z3_builtin_dict._>" "not array_ext..."
      in
        SmtLib_Theories.two_args (fn (t1, t2) =>
          Term.mk_comb (boolSyntax.mk_icomb
            (Term.prim_mk_const {Thy="HolSmt", Name="array_ext"}, t1), t2))
          args
      end),
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

  fun proofterm_of_term version = proofterm_of_term_for version false

  and proofterm_of_term_for version accepts_bind t =
  let
    val (hd, args) = boolSyntax.strip_comb t
    val name = Lib.fst (Term.dest_var hd)
      handle Feedback.HOL_ERR holerr =>
        raise ERR "proofterm_of_term"
          ("local proof subterm <" ^ Library.term_to_string t ^
           "> does not encode a Z3 proofterm: " ^ Feedback.message_of holerr)
    (* Z3 also emits `proof-bind` where no rule looks at the variables it
       binds.  There the wrapper carries no semantic content, so erase it
       instead of rejecting a proof Z3 actually produced. *)
    fun checked pt =
      case pt of
        PROOF_BIND (_, body) => if accepts_bind then pt else body
      | _ => pt
  in
    case lookup_rule version name of
      SOME rule =>
        (checked (proofterm_maker version (#replay_handler rule) args)
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

  and one_prem_pt version accepts_bind f =
    SmtLib_Theories.two_args
      (f o Lib.apfst (proofterm_of_term_for version accepts_bind))

  and two_prems_pt version accepts_bind f =
    SmtLib_Theories.three_args (fn (t1, t2, t3) =>
      f (proofterm_of_term_for version accepts_bind t1,
         proofterm_of_term_for version accepts_bind t2, t3))

  and list_prems_pt version accepts_bind f =
    SmtLib_Theories.two_args (f o Lib.apfst
      (List.map (proofterm_of_term_for version accepts_bind) o Lib.fst o
       listSyntax.dest_list))

  and list_args_zero_prems_pt f = f o Lib.front_last

  and proof_bind_pt version = SmtLib_Theories.one_arg (fn operand =>
    let
      val (vars, body) = Term.strip_abs operand
      val _ = if Type.compare (Term.type_of body, pt_ty) = EQUAL then ()
        else
          raise ERR "proof_bind_pt"
            "unsupported proof-bind shape: body is not a proofterm"
      val pt = proofterm_of_term version body
    in
      (* Without a lambda operand there are no bound variables to preserve,
         and the wrapper degrades to the plain proofterm it wraps. *)
      if List.null vars then pt else PROOF_BIND (vars, pt)
    end)

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

  and th_lemma_prems_pt version accepts_bind f =
    SmtLib_Theories.three_args (fn (metadata_tm, pts_tm, concl) =>
      f (th_lemma_metadata_of_term metadata_tm,
         List.map (proofterm_of_term_for version accepts_bind)
          (Lib.fst (listSyntax.dest_list pts_tm)),
         concl))

  (* The `accepts_bind` flag records whether a rule consumes the variables a
     Z3 `proof-bind` premise binds; only nnf-neg, nnf-pos, and quant-intro
     do.  Everywhere else the wrapper is erased. *)
  and proofterm_maker version "and_elim" =
        one_prem_pt version false AND_ELIM
    | proofterm_maker version "apply_def" =
        one_prem_pt version false APPLY_DEF
    | proofterm_maker version "asserted" = zero_prems_pt ASSERTED
    | proofterm_maker version "commutativity" = zero_prems_pt COMMUTATIVITY
    | proofterm_maker version "def_axiom" = zero_prems_pt DEF_AXIOM
    | proofterm_maker version "elim_unused" = zero_prems_pt ELIM_UNUSED
    | proofterm_maker version "hypothesis" = zero_prems_pt HYPOTHESIS
    | proofterm_maker version "iff_false" =
        one_prem_pt version false IFF_FALSE
    | proofterm_maker version "iff_true" =
        one_prem_pt version false IFF_TRUE
    | proofterm_maker version "intro_def" = zero_prems_pt INTRO_DEF
    | proofterm_maker version "lemma" =
        one_prem_pt version false LEMMA
    | proofterm_maker version "monotonicity" =
        list_prems_pt version false MONOTONICITY
    | proofterm_maker version "mp" = two_prems_pt version false MP
    | proofterm_maker version "mp_eq" = two_prems_pt version false MP_EQ
    | proofterm_maker version "nnf_neg" =
        list_prems_pt version true NNF_NEG
    | proofterm_maker version "nnf_pos" =
        list_prems_pt version true NNF_POS
    | proofterm_maker version "not_or_elim" =
        one_prem_pt version false NOT_OR_ELIM
    | proofterm_maker version "proof_bind" = proof_bind_pt version
    | proofterm_maker version "quant_inst" =
        list_args_zero_prems_pt QUANT_INST
    | proofterm_maker version "quant_intro" =
        one_prem_pt version true QUANT_INTRO
    | proofterm_maker version "refl" = zero_prems_pt REFL
    | proofterm_maker version "rewrite" = zero_prems_pt REWRITE
    | proofterm_maker version "skolem" = zero_prems_pt SKOLEM
    | proofterm_maker version "symm" = one_prem_pt version false SYMM
    | proofterm_maker version "th_lemma[arith]" =
        th_lemma_prems_pt version false TH_LEMMA_ARITH
    | proofterm_maker version "th_lemma[array]" =
        th_lemma_prems_pt version false TH_LEMMA_ARRAY
    | proofterm_maker version "th_lemma[basic]" =
        th_lemma_prems_pt version false TH_LEMMA_BASIC
    | proofterm_maker version "th_lemma[bv]" =
        th_lemma_prems_pt version false TH_LEMMA_BV
    | proofterm_maker version "th_lemma[datatype]" =
        th_lemma_prems_pt version false TH_LEMMA_DATATYPE
    | proofterm_maker version "th_lemma[seq]" =
        th_lemma_prems_pt version false TH_LEMMA_SEQ
    | proofterm_maker version "th_lemma[char]" =
        th_lemma_prems_pt version false TH_LEMMA_CHAR
    | proofterm_maker version "th_lemma[advanced]" =
        th_lemma_prems_pt version false TH_LEMMA_ADVANCED
    | proofterm_maker version "trans" = two_prems_pt version false TRANS
    | proofterm_maker version "trans_star" =
        list_prems_pt version false TRANS_STAR
    | proofterm_maker version "true_axiom" = zero_prems_pt TRUE_AXIOM
    | proofterm_maker version "unit_resolution" =
        list_prems_pt version false UNIT_RESOLUTION
    | proofterm_maker _ handler =
        raise ERR "proofterm_maker"
          ("Z3 proof rule registry has no parser wrapper for replay handler '" ^
           handler ^ "'")

  (***************************************************************************)
  (* discovering FloatingPoint bit-decomposition rewrites                    *)
  (***************************************************************************)

  fun is_k_skolem tm =
    Term.is_var tm andalso
    let
      val name = Lib.fst (Term.dest_var tm)
      val n = String.size name
      fun digits i =
        i >= n orelse
        (Char.isDigit (String.sub (name, i)) andalso digits (i + 1))
    in
      n > 2 andalso String.isPrefix "k!" name andalso digits 2
    end

  fun dest_smtfp_bits tm =
  let
    val (head, args) = boolSyntax.strip_comb tm
    val {Thy, Name, ...} = Term.dest_thy_const head
  in
    if Thy = "smtfloat" andalso Name = "smtfp_bits" then
      case args of
        [sign, exponent, significand] => (sign, exponent, significand)
      | _ => raise ERR "dest_smtfp_bits" "three fields expected"
    else
      raise ERR "dest_smtfp_bits" "smtfp_bits expected"
  end

  fun bit_decomposition_of_rewrite vars equation =
  let
    val (fp_var, fields) = boolSyntax.dest_eq equation
    val _ = SmtFpProve.type_mentions_fp (Term.type_of fp_var) orelse
      raise ERR "bit_decomposition_of_rewrite" "FP term expected"
    val (sign, exponent, significand) = dest_smtfp_bits fields
    fun extract_source field =
      let val (_, _, source, _) = wordsSyntax.dest_word_extract field
      in source end
    val sources = List.map extract_source [sign, exponent, significand]
    val bv_var = List.hd sources
    val _ = List.all (Term.aconv bv_var) (List.tl sources) orelse
      raise ERR "bit_decomposition_of_rewrite"
        "extracts do not share a source"
    val _ = is_k_skolem bv_var orelse
      raise ERR "bit_decomposition_of_rewrite" "k! skolem expected"
    val _ = HOLset.member (vars, bv_var) orelse
      raise ERR "bit_decomposition_of_rewrite" "undeclared k! skolem"
  in
    SOME {fp_var = fp_var, bv_var = bv_var, equation = equation}
  end
  handle Feedback.HOL_ERR _ => NONE

  fun discover_bit_decompositions proof =
  let
    val vars = proof_vars proof
    fun add_decomposition decomposition decompositions =
      if List.exists (fn {bv_var, equation, ...} =>
          Term.aconv bv_var (#bv_var decomposition) andalso
          Term.aconv equation (#equation decomposition)) decompositions then
        decompositions
      else
        decomposition :: decompositions
    fun collect (pt, decompositions) =
      let
        val decompositions =
          case pt of
            REWRITE equation =>
              (case bit_decomposition_of_rewrite vars equation of
                 SOME decomposition =>
                   add_decomposition decomposition decompositions
               | NONE => decompositions)
          | _ => decompositions
      in
        List.foldl collect decompositions (proofterm_premises pt)
      end
    val decompositions = Redblackmap.foldl
      (fn (_, pt, found) => collect (pt, found)) [] (proof_steps proof)
  in
    update_proof_bit_decompositions proof (List.rev decompositions)
  end

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

     Z3 4.x proofs begin with:
     ```
     (                      ; note the extra parenthesis
       (declare-fun ...)    ; any number of these, maybe none
       (proof
         (let ...
     ```
     We consume the extra parenthesis here and then continue parsing as
     normal.  (Legacy Z3 2.x proofs, which began with `(let`/`(error`, are no
     longer supported.) *)
  fun parse_proof get_token state =
  let
    val () = Library.expect_token "(" (get_token ())
    (* leave the 1st parenthesis consumed and undo the 2nd *)
    val () = Library.expect_token "(" (get_token ())
    val get_token' = Library.undo_look_ahead ["("] get_token
  in
    parse_proof_decl get_token' state 1
  end

in

  (* Similar to 'parse_file' below, but for instreams.  Does not close
     the instream. *)

  fun parse_stream_with_version ((tydict, tmdict): SmtLib_Parser.dicts)
    (z3_version : string) (instream : TextIO.instream) : proof =
  let
    (* Resolve once, here: everything downstream -- rule lookup, gating and
       diagnostics -- then works with a tested anchor. *)
    val z3_version = resolve_version z3_version
    val string_witnesses = z3_string_witness_specs z3_version
    val tydict = Library.union_dict tydict z3_string_tydict
    (* Z3 writes generated sort names (such as [t0]) in the legacy
       term-shaped Seq annotations.  Give each declared proof sort a local
       marker so [(as seq.empty (Seq t0))] does not try to read [t0] as a
       numeral. *)
    val sort_markers : Term.term SmtLib_Parser.dict = Library.dict_from_list
      (List.mapPartial (fn (name,
          parsefns : Type.hol_type SmtLib_Parser.parse_fn list) =>
        case List.mapPartial (fn parsefn =>
          Lib.total (fn () => parsefn name [] []) ()) parsefns of
          ty :: _ => SOME (name, SmtLib_Theories.K_zero_zero
            (z3_seq_sort_marker ty))
        | [] => NONE) (Redblackmap.listItems tydict))
    val tmdict = Library.union_dict tmdict sort_markers
    val tmdict = Library.union_dict tmdict
      (z3_string_tmdict z3_version)
    (* union of user-declared names and Z3's inference rule names *)
    val tmdict = Library.union_dict tmdict z3_builtin_dict
    (* parse the stream *)
    val _ = if !Library.trace > 1 then
        Feedback.HOL_MESG "HolSmtLib: parsing Z3 proof"
      else ()
    val get_token = SmtLib_Parser.make_proof_stream_tokenizer instream
    val initial_proof = update_proof_vars (empty_proof z3_version)
      (List.foldl
        (fn ((_, witness), vars) => HOLset.add (vars, witness))
        Term.empty_tmset string_witnesses)
    val proof = discover_bit_decompositions (parse_proof get_token
      (tydict, tmdict, initial_proof))
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
     enabled in Z3 4.x, i.e., using options
     "proof=true pp.simplify_implies=false").  'parse_file' takes three
     arguments: two dictionaries mapping names of types and terms (namely those
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
