open testutils
open linarithSolve

val zero = Arbint.zero
val one = Arbint.one
val two = Arbint.two
val three = Arbint.fromInt 3
val negone = Arbint.~ one

fun check (name, predicate) =
  (tprint name;
   if predicate () then OK () else die "failed")

fun last xs = hd (rev xs)

val _ =
  check
    ("linarith theorem sets initially ship empty",
     fn () =>
       null (linarithData.arith_facts ()) andalso
       null (linarithData.arith_split_thms ()))

val registry_ty = Type.mk_type ("fun", [Type.bool, Type.bool])

fun decline _ = raise Fail "synthetic linarith instance declined"

fun synthetic_instance discrete : linarithData.linarith_instance =
  {ty = registry_ty,
   discrete = discrete,
   dest =
     {dest_plus = decline,
      dest_minus = NONE,
      dest_neg = NONE,
      dest_mult = decline,
      dest_div = NONE,
      dest_suc = NONE,
      dest_lit = decline,
      mk_lit = decline,
      dest_less = decline,
      dest_leq = decline},
   kit =
     {add_mono = [],
      mult_mono = [],
      lessD = [],
      not_less = boolTheory.TRUTH,
      not_le = boolTheory.TRUTH,
      neqE = boolTheory.TRUTH,
      nonneg = (fn _ => NONE)},
   norm_conv = Conv.ALL_CONV,
   pre_split = [],
   divmod_facts = NONE}

val _ = linarithData.register_instance (synthetic_instance false)
val _ = linarithData.register_instance (synthetic_instance true)

val _ =
  check
    ("instance registration replaces an existing same-type entry",
     fn () =>
       case linarithData.instance_for registry_ty of
           SOME instance => #discrete instance
         | NONE => false)

val bad_split_name =
  {Thy = "bool", Name = "TRUTH"}

fun bad_split_rejected () =
  case ThmSetData.data_exportfns {settype = "arith_split"} of
      NONE => false
    | SOME export =>
        ((#add export
            {thy = "bool",
             named_thm = (bad_split_name, boolTheory.TRUTH)};
          false)
         handle Feedback.HOL_ERR error =>
           String.isSubstring
             "Malformed [arith_split] theorem bool$TRUTH"
             (Feedback.message_of error))

val _ =
  check
    ("arith_split rejects a named theorem outside the P-form",
     bad_split_rejected)

fun first_pivot rows =
  case elim (rows, []) of
      Failure hist => SOME (#1 (last hist))
    | Success _ => NONE

val _ =
  check
    ("FM derives the expected unit-coefficient certificate",
     fn () =>
       let
         val upper = Lineq (zero, Le, [one], Asm 0)
         val lower = Lineq (one, Le, [negone], Asm 1)
       in
         case elim ([upper, lower], []) of
             Success (Added (Asm 0, Asm 1)) => true
           | _ => false
       end)

val _ =
  check
    ("FM records integer scaling in the certificate",
     fn () =>
       let
         val pos = Lineq (zero, Le, [two], Asm 0)
         val neg = Lineq (one, Le, [Arbint.~ three], Asm 1)
       in
         case elim ([pos, neg], []) of
             Success
               (Added
                  (Multiplied (m, Asm 0),
                   Multiplied (n, Asm 1))) =>
               m = three andalso n = two
           | _ => false
       end)

val _ =
  check
    ("equations take priority and use the smallest coefficient",
     fn () =>
       let
         val five = Arbint.fromInt 5
         val eq = Lineq (zero, Eq, [five, two], Asm 0)
         val p = Lineq (zero, Le, [one, zero], Asm 1)
         val n = Lineq (zero, Le, [negone, zero], Asm 2)
       in
         first_pivot [p, eq, n] = SOME 1
       end)

val _ =
  check
    ("inequality pivot minimizes Fourier-Motzkin blowup",
     fn () =>
       let
         val rows =
           [Lineq (zero, Le, [one, one], Asm 0),
            Lineq (zero, Le, [negone, zero], Asm 1),
            Lineq (zero, Le, [one, zero], Asm 2),
            Lineq (zero, Le, [negone, negone], Asm 3)]
       in
         first_pivot rows = SOME 1
       end)

val _ =
  check
    ("trivial rows are discarded and contradictory rows detected",
     fn () =>
       let
         val harmless = Lineq (zero, Le, [zero], Asm 0)
         val open_row = Lineq (zero, Le, [one], Asm 1)
         val bad_eq = Lineq (one, Eq, [zero], Asm 2)
       in
         (case elim ([harmless, open_row], []) of
              Failure _ => true
            | _ => false) andalso
         (case elim ([bad_eq], []) of
              Success (Asm 2) => true
            | _ => false)
       end)

val x = Term.mk_var ("linarith_unit_x", numSyntax.num)
val huge =
  Arbint.fromString "100000000000000000000000000000000000003"
val tiny = Arbrat./ (Arbrat.one, Arbrat.fromAInt huge)

val scaled =
  Decomp {
    lhs = [(x, tiny)], lhs_const = Arbrat.zero,
    rel = REL_LE, rhs = [], rhs_const = Arbrat.zero,
    discrete = true, negated = false
  }

val _ =
  check
    ("integ and mklineq use arbitrary-precision denominator scaling",
     fn () =>
       case mklineq [x] (scaled, 7) of
           Lineq (c, Le, [a], Multiplied (m, Asm 7)) =>
             c = zero andalso a = negone andalso m = huge
         | _ => false)

fun const_decomp lhs rel discrete =
  Decomp {
    lhs = [], lhs_const = Arbrat.fromInt lhs,
    rel = rel, rhs = [], rhs_const = Arbrat.zero,
    discrete = discrete, negated = false
  }

val dense_neq_tm =
  Term.mk_var ("linarith_unit_dense_neq", Type.bool)
val discrete_neq_tm =
  Term.mk_var ("linarith_unit_discrete_neq", Type.bool)
val contradiction_tm =
  Term.mk_var ("linarith_unit_contradiction", Type.bool)
val conclusion_tm =
  Term.mk_var ("linarith_unit_conclusion", Type.bool)

val dense_neq = const_decomp 1 REL_NEQ false
val discrete_neq = const_decomp 2 REL_NEQ true
val contradiction = const_decomp 1 REL_LE true

fun unit_decomp tm =
  if Term.aconv tm dense_neq_tm then SOME dense_neq
  else if Term.aconv tm discrete_neq_tm then SOME discrete_neq
  else if Term.aconv tm contradiction_tm then SOME contradiction
  else NONE

fun unit_selector tm =
  if Term.aconv tm dense_neq_tm then SOME false
  else if Term.aconv tm discrete_neq_tm then SOME true
  else NONE

fun constants (Decomp {lhs_const, rhs_const, ...}) =
  (Arbrat.toAInt lhs_const, Arbrat.toAInt rhs_const)

fun case_constants items =
  List.mapPartial
    (fn (_, item) =>
        case item of NONE => NONE | SOME decomp => SOME (constants decomp))
    items

val _ =
  check
    ("disequalities use by-premise selection and discrete-first order",
     fn () =>
       let
         val i0 = zero
         val i1 = one
         val i2 = two
         val items =
           [(dense_neq_tm, SOME dense_neq),
            (discrete_neq_tm, SOME discrete_neq)]
         val actual =
           List.map case_constants (elim_neq unit_selector items)
         val expected =
           [[(i2, i0), (i1, i0)],
            [(i2, i0), (i0, i1)],
            [(i0, i2), (i1, i0)],
            [(i0, i2), (i0, i1)]]
       in
         actual = expected
       end)

val _ =
  check
    ("split_items renumbers moved disequality premises for replay",
     fn () =>
       let
         val cases =
           split_items unit_selector true unit_decomp
             [dense_neq_tm, contradiction_tm, discrete_neq_tm]
       in
         List.length cases = 4 andalso
         List.all (fn items => List.map #2 items = [0, 1, 2]) cases
       end)

val _ =
  check
    ("prove splits at the neq_limit boundary",
     fn () =>
       case prove {neq_limit = 1, split_limit = 9} unit_decomp
                  [dense_neq_tm, contradiction_tm] conclusion_tm of
           (true, SOME justs) => List.length justs = 2
         | _ => false)

val _ =
  check
    ("prove ignores all disequalities when neq_limit is exceeded",
     fn () =>
       case prove {neq_limit = 0, split_limit = 9} unit_decomp
                  [dense_neq_tm, contradiction_tm] conclusion_tm of
           (false, SOME [_]) => true
         | _ => false)

val negated_conclusion_tm = boolSyntax.mk_neg conclusion_tm

fun from_negated_conclusion tm =
  if Term.aconv tm negated_conclusion_tm then SOME contradiction
  else NONE

fun from_unwrapped_conclusion tm =
  if Term.aconv tm conclusion_tm then SOME contradiction else NONE

val _ =
  check
    ("prove appends the negated conclusion with its assumption index",
     fn () =>
       case prove {neq_limit = 9, split_limit = 9}
                  from_negated_conclusion [] conclusion_tm of
           (true, SOME [Asm 0]) => true
         | _ => false)

val _ =
  check
    ("prove avoids double negation of an already-negated conclusion",
     fn () =>
       case prove {neq_limit = 9, split_limit = 9}
                  from_unwrapped_conclusion [] negated_conclusion_tm of
           (true, SOME [Asm 0]) => true
         | _ => false)
