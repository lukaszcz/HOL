(* Copyright (c) 2010-2011 Tjark Weber. All rights reserved. *)

(* SMT-LIB 2 theories *)

structure SmtLib_Theories =
struct

local

  local open HolSmtTheory in end

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
    parametric_sorts = []
  }

  fun mk_attributes {
      overloaded, indexed, chainable, pairwise, left_associative,
      right_associative, parametric_sorts} =
    {
      overloaded = overloaded,
      indexed = indexed,
      chainable = chainable,
      pairwise = pairwise,
      left_associative = left_associative,
      right_associative = right_associative,
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
    parametric_sorts = []
  }

  val right_assoc_attributes = mk_attributes {
    overloaded = false,
    indexed = false,
    chainable = false,
    pairwise = false,
    left_associative = false,
    right_associative = true,
    parametric_sorts = []
  }

  val chainable_attributes = mk_attributes {
    overloaded = false,
    indexed = false,
    chainable = true,
    pairwise = false,
    left_associative = false,
    right_associative = false,
    parametric_sorts = []
  }

  val pairwise_attributes = mk_attributes {
    overloaded = false,
    indexed = false,
    chainable = false,
    pairwise = true,
    left_associative = false,
    right_associative = false,
    parametric_sorts = []
  }

  fun parametric_attributes params = mk_attributes {
    overloaded = false,
    indexed = false,
    chainable = false,
    pairwise = false,
    left_associative = false,
    right_associative = false,
    parametric_sorts = params
  }

  fun indexed_attributes params = mk_attributes {
    overloaded = false,
    indexed = true,
    chainable = false,
    pairwise = false,
    left_associative = false,
    right_associative = false,
    parametric_sorts = params
  }

  fun overloaded_attributes attrs = {
    overloaded = true,
    indexed = #indexed attrs,
    chainable = #chainable attrs,
    pairwise = #pairwise attrs,
    left_associative = #left_associative attrs,
    right_associative = #right_associative attrs,
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
      official_entry "bvnot" no_attributes ["(bvnot (_ BitVec m) (_ BitVec m))"]
        (K_zero_one wordsSyntax.mk_word_1comp),
      official_entry "bvneg" no_attributes ["(bvneg (_ BitVec m) (_ BitVec m))"]
        (K_zero_one wordsSyntax.mk_word_2comp),
      official_entry "bvand" no_attributes
        ["(bvand (_ BitVec m) (_ BitVec m) (_ BitVec m))"]
        (K_zero_two wordsSyntax.mk_word_and),
      official_entry "bvor" no_attributes
        ["(bvor (_ BitVec m) (_ BitVec m) (_ BitVec m))"]
        (K_zero_two wordsSyntax.mk_word_or),
      official_entry "bvxor" no_attributes
        ["(bvxor (_ BitVec m) (_ BitVec m) (_ BitVec m))"]
        (K_zero_two wordsSyntax.mk_word_xor),
      official_entry "bvxnor" no_attributes
        ["(bvxnor (_ BitVec m) (_ BitVec m) (_ BitVec m))"]
        (K_zero_two wordsSyntax.mk_word_xnor),
      official_entry "bvadd" no_attributes
        ["(bvadd (_ BitVec m) (_ BitVec m) (_ BitVec m))"]
        (K_zero_two wordsSyntax.mk_word_add),
      official_entry "bvmul" no_attributes
        ["(bvmul (_ BitVec m) (_ BitVec m) (_ BitVec m))"]
        (K_zero_two wordsSyntax.mk_word_mul),
      (* SMT-LIB states that division by 0w is unspecified. Thus, any
         proof (of unsatisfiability) should also be valid in HOL,
         regardless of how division by 0w is defined in HOL. *)
      official_entry "bvudiv" no_attributes
        ["(bvudiv (_ BitVec m) (_ BitVec m) (_ BitVec m))"]
        (K_zero_two wordsSyntax.mk_word_div),
      official_entry "bvurem" no_attributes
        ["(bvurem (_ BitVec m) (_ BitVec m) (_ BitVec m))"]
        (K_zero_two wordsSyntax.mk_word_mod),
      official_entry "bvshl" no_attributes
        ["(bvshl (_ BitVec m) (_ BitVec m) (_ BitVec m))"]
        (K_zero_two wordsSyntax.mk_word_lsl_bv),
      official_entry "bvlshr" no_attributes
        ["(bvlshr (_ BitVec m) (_ BitVec m) (_ BitVec m))"]
        (K_zero_two wordsSyntax.mk_word_lsr_bv),
      official_entry "bvult" no_attributes
        ["(bvult (_ BitVec m) (_ BitVec m) Bool)"]
        (K_zero_two wordsSyntax.mk_word_lo)
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
      (* FIXME: SMT-LIB declares "and" and "or" as left-assoc. This
         interacts badly with HOL4, where they are right-assoc.  In
         particular, it breaks our proof reconstruction implementation
         (Z3_ProofReplay.sml) in a few places that are not prepared to
         handle the additional parentheses. For now, we parse "and"
         and "or" as rightassoc. Since conjunction and disjunction are
         associative, this does not change the meaning of formulas. *)
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
      official_entry "div" left_assoc_attributes ["(div Int Int Int :left-assoc)"]
        (leftassoc (fn (t1, t2) => Term.mk_comb (Term.mk_comb
          (Term.prim_mk_const {Thy="integer", Name="ediv"}, t1), t2))),
      official_entry "mod" left_assoc_attributes ["(mod Int Int Int :left-assoc)"]
        (leftassoc (fn (t1, t2) => Term.mk_comb (Term.mk_comb
          (Term.prim_mk_const {Thy="integer", Name="emod"}, t1), t2))),
      official_entry "abs" no_attributes ["(abs Int Int)"]
        (K_zero_one intSyntax.mk_absval),
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
      ("div", leftassoc (fn (t1, t2) => Term.mk_comb (Term.mk_comb
        (Term.prim_mk_const {Thy="integer", Name="ediv"}, t1), t2))),
      ("div0", leftassoc (fn (t1, t2) => Term.mk_comb (Term.mk_comb
        (Term.prim_mk_const {Thy="integer", Name="ediv"}, t1), t2))),
      ("mod", leftassoc (fn (t1, t2) => Term.mk_comb (Term.mk_comb
        (Term.prim_mk_const {Thy="integer", Name="emod"}, t1), t2))),
      ("mod0", leftassoc (fn (t1, t2) => Term.mk_comb (Term.mk_comb
        (Term.prim_mk_const {Thy="integer", Name="emod"}, t1), t2))),
      ("abs", K_zero_one intSyntax.mk_absval),
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
          (K_zero_one intrealSyntax.mk_is_int),
        extension_entry "Z3" "div0" left_assoc_attributes
          ["(div0 Int Int Int :left-assoc)"]
          (leftassoc (fn (t1, t2) => Term.mk_comb (Term.mk_comb
            (Term.prim_mk_const {Thy="integer", Name="ediv"}, t1), t2))),
        extension_entry "Z3" "mod0" left_assoc_attributes
          ["(mod0 Int Int Int :left-assoc)"]
          (leftassoc (fn (t1, t2) => Term.mk_comb (Term.mk_comb
            (Term.prim_mk_const {Thy="integer", Name="emod"}, t1), t2)))
      ]

  end

end  (* local *)

end
