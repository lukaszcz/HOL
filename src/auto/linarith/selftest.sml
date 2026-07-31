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
    ("linarith ships no arith facts and three num split seeds",
     fn () =>
       null (linarithData.arith_facts ()) andalso
       List.length (linarithData.arith_split_thms ()) = 3)

val num_instance = linarithNum.instance

val _ =
  check
    ("linarithLib registers the num instance at module load",
     fn () =>
       case linarithData.instance_for numSyntax.num of
           SOME instance => #discrete instance
         | NONE => false)

val num_x = Term.mk_var ("linarith_num_x", numSyntax.num)
val num_y = Term.mk_var ("linarith_num_y", numSyntax.num)
val num_z = Term.mk_var ("linarith_num_z", numSyntax.num)
val num_two = numSyntax.mk_numeral (Arbnum.fromInt 2)
val num_three = numSyntax.mk_numeral (Arbnum.fromInt 3)
val num_seven = numSyntax.mk_numeral (Arbnum.fromInt 7)
val num_eight = numSyntax.mk_numeral (Arbnum.fromInt 8)

fun num_plus left right = numSyntax.mk_plus (left, right)
fun num_leq left right = numSyntax.mk_leq (left, right)

fun normalized_rhs tm =
  #2 (boolSyntax.dest_eq (Thm.concl (#norm_conv num_instance tm)))

val _ =
  check
    ("num norm_conv turns a contradictory leq into false",
     fn () =>
       Term.aconv
         (normalized_rhs
            (num_leq (num_plus num_x num_three)
              (num_plus num_x num_two)))
         boolSyntax.F)

val _ =
  check
    ("num norm_conv cancels a common summand",
     fn () =>
       Term.aconv
         (normalized_rhs
            (num_leq (num_plus num_x num_y)
              (num_plus num_y num_z)))
         (num_leq num_x num_z))

val _ =
  check
    ("num norm_conv decides a ground relation",
     fn () =>
       Term.aconv
         (normalized_rhs (numSyntax.mk_less (num_seven, num_eight)))
         boolSyntax.T)

val _ =
  check
    ("num literals include SUC towers",
     fn () =>
       let
         val tower = numSyntax.mk_suc (numSyntax.mk_suc numSyntax.zero_tm)
         val dest_lit = #dest_lit (#dest num_instance)
       in
         dest_lit tower = Arbrat.two andalso
         Term.aconv (#mk_lit (#dest num_instance) Arbrat.two) num_two
       end)

val _ =
  check
    ("num divmod facts specialize DIVISION for a positive literal",
     fn () =>
       case #divmod_facts num_instance of
           NONE => false
         | SOME facts =>
             let
               val div_tm = numSyntax.mk_div (num_x, num_three)
               val mod_tm = numSyntax.mk_mod (num_x, num_three)
             in
               List.length (facts div_tm) = 2 andalso
               List.length (facts mod_tm) = 2 andalso
               null (facts (numSyntax.mk_div
                 (num_x, numSyntax.zero_tm)))
             end)

val num_decomp_relation =
  num_leq
    (num_plus (numSyntax.mk_mult (num_two, num_x)) num_three)
    (num_plus num_x num_y)

val _ =
  check
    ("decomp uses the locally registered num instance",
     fn () =>
       case linarithDecomp.decomp num_decomp_relation of
           SOME
             (Decomp
                {lhs, lhs_const, rel = REL_LE, rhs, rhs_const,
                 discrete = true, negated = false}) =>
               List.length lhs = 1 andalso List.length rhs = 2 andalso
               lhs_const = Arbrat.fromInt 3 andalso
               rhs_const = Arbrat.zero
         | _ => false)

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

fun function_ty domain range = Type.mk_type ("fun", [domain, range])
fun binary_ty domain range =
  function_ty domain (function_ty domain range)

val synth_plus =
  Term.mk_var ("linarith_synth_plus", binary_ty registry_ty registry_ty)
val synth_minus =
  Term.mk_var ("linarith_synth_minus", binary_ty registry_ty registry_ty)
val synth_neg =
  Term.mk_var
    ("linarith_synth_neg", function_ty registry_ty registry_ty)
val synth_mult =
  Term.mk_var ("linarith_synth_mult", binary_ty registry_ty registry_ty)
val synth_div =
  Term.mk_var ("linarith_synth_div", binary_ty registry_ty registry_ty)
val synth_less =
  Term.mk_var ("linarith_synth_less", binary_ty registry_ty Type.bool)
val synth_leq =
  Term.mk_var ("linarith_synth_leq", binary_ty registry_ty Type.bool)
val synth_inj =
  Term.mk_var
    ("linarith_synth_inj", function_ty Type.bool registry_ty)

val synth_zero = Term.mk_var ("linarith_synth_zero", registry_ty)
val synth_one = Term.mk_var ("linarith_synth_one", registry_ty)
val synth_two = Term.mk_var ("linarith_synth_two", registry_ty)
val synth_x = Term.mk_var ("linarith_synth_x", registry_ty)
val synth_y = Term.mk_var ("linarith_synth_y", registry_ty)
val synth_z = Term.mk_var ("linarith_synth_z", registry_ty)
val synth_bool_atom =
  Term.mk_var ("linarith_synth_bool_atom", Type.bool)

fun mk_binary operator left right =
  Term.list_mk_comb (operator, [left, right])

fun dest_binary operator tm =
  let
    val (rator, right) = Term.dest_comb tm
    val (actual, left) = Term.dest_comb rator
  in
    if Term.aconv actual operator then (left, right) else decline tm
  end

fun dest_unary operator tm =
  let
    val (actual, arg) = Term.dest_comb tm
  in
    if Term.aconv actual operator then arg else decline tm
  end

fun synth_lit tm =
  if Term.aconv tm synth_zero then Arbrat.zero
  else if Term.aconv tm synth_one then Arbrat.one
  else if Term.aconv tm synth_two then Arbrat.two
  else decline tm

fun make_decomp_instance dest_minus :
    linarithData.linarith_instance =
  {ty = registry_ty,
   discrete = false,
   dest =
     {dest_plus = dest_binary synth_plus,
      dest_minus = dest_minus,
      dest_neg = SOME (dest_unary synth_neg),
      dest_mult = dest_binary synth_mult,
      dest_div = SOME (dest_binary synth_div),
      dest_suc = NONE,
      dest_lit = synth_lit,
      mk_lit = decline,
      dest_less = dest_binary synth_less,
      dest_leq = dest_binary synth_leq},
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

val decomp_instance =
  make_decomp_instance (SOME (dest_binary synth_minus))

val _ = linarithData.register_instance decomp_instance
val _ =
  linarithData.register_injection
    {from_ty = Type.bool,
     to_ty = registry_ty,
     inj = synth_inj,
     hom =
       {le = boolTheory.TRUTH,
        lt = boolTheory.TRUTH,
        eq = boolTheory.TRUTH,
        add = boolTheory.TRUTH,
        mul = boolTheory.TRUTH}}

fun coefficient atoms atom =
  case List.find (fn (tm, _) => Term.aconv tm atom) atoms of
      SOME (_, value) => value
    | NONE => Arbrat.zero

val synth_linear_lhs =
  mk_binary synth_plus
    (mk_binary synth_mult synth_two synth_x) synth_one
val synth_linear_rhs =
  mk_binary synth_plus synth_x synth_y
val synth_linear_relation =
  mk_binary synth_leq synth_linear_lhs synth_linear_rhs

val _ =
  check
    ("decomp uses synthetic plus, mult, literal, and atom destructors",
     fn () =>
       case linarithDecomp.decomp synth_linear_relation of
           SOME
             (Decomp
                {lhs, lhs_const, rel = REL_LE, rhs, rhs_const,
                 discrete = false, negated = false}) =>
               List.length lhs = 1 andalso List.length rhs = 2 andalso
               coefficient lhs synth_x = Arbrat.two andalso
               coefficient rhs synth_x = Arbrat.one andalso
               coefficient rhs synth_y = Arbrat.one andalso
               lhs_const = Arbrat.one andalso
               rhs_const = Arbrat.zero
         | _ => false)

val synth_signed_expression =
  mk_binary synth_minus
    (Term.mk_comb (synth_neg, synth_x)) synth_y
val synth_signed_relation =
  mk_binary synth_leq synth_signed_expression synth_zero
val synth_cancelled_relation =
  mk_binary synth_leq
    (mk_binary synth_plus synth_x
       (Term.mk_comb (synth_neg, synth_x))) synth_zero

val _ =
  check
    ("poly handles subtraction, negation, and coefficient cancellation",
     fn () =>
       (case linarithDecomp.decomp synth_signed_relation of
            SOME (Decomp {lhs, lhs_const, ...}) =>
              List.length lhs = 2 andalso
              coefficient lhs synth_x = Arbrat.negate Arbrat.one andalso
              coefficient lhs synth_y = Arbrat.negate Arbrat.one andalso
              lhs_const = Arbrat.zero
          | NONE => false) andalso
       (case linarithDecomp.decomp synth_cancelled_relation of
            SOME (Decomp {lhs, lhs_const, ...}) =>
              null lhs andalso lhs_const = Arbrat.zero
          | NONE => false))

val _ =
  linarithData.register_instance (make_decomp_instance NONE)

val _ =
  check
    ("poly keeps subtraction atomic when the instance declines it",
     fn () =>
       case linarithDecomp.decomp synth_signed_relation of
           SOME (Decomp {lhs, lhs_const, ...}) =>
             List.length lhs = 1 andalso
             coefficient lhs synth_signed_expression = Arbrat.one andalso
             lhs_const = Arbrat.zero
         | NONE => false)

val _ = linarithData.register_instance decomp_instance

val synth_left_product =
  mk_binary synth_mult
    (mk_binary synth_mult synth_x synth_y) synth_z
val synth_right_product =
  mk_binary synth_mult synth_x
    (mk_binary synth_mult synth_y synth_z)

val _ =
  check
    ("demult normalizes products to right-associated form",
     fn () =>
       case linarithDecomp.demult
              (synth_left_product, Arbrat.one) of
           (SOME atom, multiplier) =>
             Term.aconv atom synth_right_product andalso
             multiplier = Arbrat.one
         | _ => false)

val _ =
  check
    ("demult scales division only by a nonzero literal divisor",
     fn () =>
       let
         val literal_division =
           mk_binary synth_div synth_x synth_two
         val atom_division = mk_binary synth_div synth_x synth_y
         val zero_division = mk_binary synth_div synth_x synth_zero
         val division_relation =
           mk_binary synth_leq literal_division synth_zero
       in
         (case linarithDecomp.demult
                 (literal_division, Arbrat.one) of
              (SOME atom, multiplier) =>
                Term.aconv atom synth_x andalso
                multiplier = Arbrat./ (Arbrat.one, Arbrat.two)
            | _ => false) andalso
         (case linarithDecomp.demult (atom_division, Arbrat.one) of
              (SOME atom, multiplier) =>
                Term.aconv atom atom_division andalso
                multiplier = Arbrat.one
            | _ => false) andalso
         (case linarithDecomp.demult (zero_division, Arbrat.one) of
              (SOME atom, multiplier) =>
                Term.aconv atom zero_division andalso
                multiplier = Arbrat.one
            | _ => false) andalso
         (case linarithDecomp.decomp division_relation of
              SOME (Decomp {lhs, lhs_const, ...}) =>
                List.length lhs = 1 andalso
                coefficient lhs synth_x =
                  Arbrat./ (Arbrat.one, Arbrat.two) andalso
                lhs_const = Arbrat.zero
            | NONE => false)
       end)

val synth_injected = Term.mk_comb (synth_inj, synth_bool_atom)
val synth_injected_relation =
  mk_binary synth_leq synth_injected synth_zero
val synth_mixed_product =
  mk_binary synth_mult synth_injected synth_x
val synth_scaled_mixed_product =
  mk_binary synth_mult synth_injected
    (mk_binary synth_mult synth_x synth_two)

val _ =
  check
    ("poly and demult unwrap registered injections",
     fn () =>
       (case linarithDecomp.decomp synth_injected_relation of
            SOME (Decomp {lhs, lhs_const, ...}) =>
              List.length lhs = 1 andalso
              coefficient lhs synth_bool_atom = Arbrat.one andalso
              lhs_const = Arbrat.zero
          | NONE => false) andalso
       (case linarithDecomp.demult
               (mk_binary synth_mult synth_injected synth_two,
                Arbrat.one) of
            (SOME atom, multiplier) =>
              Term.aconv atom synth_bool_atom andalso
              multiplier = Arbrat.two
          | _ => false) andalso
       (case linarithDecomp.demult
               (synth_scaled_mixed_product, Arbrat.one) of
            (SOME atom, multiplier) =>
              Term.aconv atom synth_mixed_product andalso
              multiplier = Arbrat.two
          | _ => false))

val synth_negated_less =
  boolSyntax.mk_neg (mk_binary synth_less synth_x synth_y)
val synth_negated_leq =
  boolSyntax.mk_neg (mk_binary synth_leq synth_x synth_y)
val synth_negated_eq =
  boolSyntax.mk_neg (boolSyntax.mk_eq (synth_x, synth_y))

fun relation_flags tm =
  case linarithDecomp.decomp tm of
      SOME (Decomp {rel, negated, ...}) => SOME (rel, negated)
    | NONE => NONE

val _ =
  check
    ("decomp handles positive and negated synthetic relations",
     fn () =>
       relation_flags (mk_binary synth_less synth_x synth_y) =
         SOME (REL_LT, false) andalso
       relation_flags (boolSyntax.mk_eq (synth_x, synth_y)) =
         SOME (REL_EQ, false) andalso
       relation_flags synth_negated_less = SOME (REL_LT, true) andalso
       relation_flags synth_negated_leq = SOME (REL_LE, true) andalso
       relation_flags synth_negated_eq = SOME (REL_NEQ, false))

val _ =
  check
    ("unregistered relation carriers are declined",
     fn () =>
       case linarithDecomp.decomp
              (boolSyntax.mk_eq (synth_bool_atom, boolSyntax.T)) of
           NONE => true
         | SOME _ => false)

val _ =
  check
    ("is_relevant is exactly successful decomposition",
     fn () =>
       linarithDecomp.is_relevant synth_linear_relation andalso
       not (linarithDecomp.is_relevant synth_bool_atom))

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

(* Golden kernel-replay tests.  These construct certificates directly so
   every replay constructor and every currently shipped num kit slot is
   exercised independently of Fourier--Motzkin search. *)

fun num_less left right = numSyntax.mk_less (left, right)
fun num_eq left right = boolSyntax.mk_eq (left, right)
fun num_not tm = boolSyntax.mk_neg tm

val num_zero = numSyntax.zero_tm
val num_one = numSyntax.mk_numeral Arbnum.one

fun replay terms justification =
  linarithReplay.mkthm
    (linarithReplay.mk_instance_env terms)
    (List.map Thm.ASSUME terms) justification

fun replay_is_false terms justification =
  Term.aconv (Thm.concl (replay terms justification)) boolSyntax.F

val _ =
  check
    ("replay golden: Asm",
     fn () => replay_is_false [num_leq num_one num_zero] (Asm 0))

val _ =
  check
    ("replay rejects a certificate that does not derive false",
     fn () =>
       ((ignore (replay [num_leq num_x num_x] (Asm 0)); false)
        handle Feedback.HOL_ERR error =>
          Feedback.message_of error =
            "Linear arithmetic should have refuted the assumptions " ^
            "but failed to."))

val _ =
  check
    ("replay golden: Nonneg",
     fn () =>
       replay_is_false
         [num_leq (num_plus num_x num_three) num_two]
         (Added (Nonneg 0, Asm 0)))

val _ =
  check
    ("replay atom indices agree with search lhs-before-rhs order",
     fn () =>
       replay_is_false
         [num_leq num_x num_y,
          num_leq (num_plus num_x num_three) num_two]
         (Added (Nonneg 0, Asm 1)))

val _ =
  check
    ("replay golden: LessD",
     fn () => replay_is_false [num_less num_zero num_zero]
                              (LessD (Asm 0)))

val _ =
  check
    ("replay golden: NotLessD",
     fn () => replay_is_false [num_not (num_less num_zero num_one)]
                              (NotLessD (Asm 0)))

val _ =
  check
    ("replay golden: NotLeD",
     fn () => replay_is_false [num_not (num_leq num_zero num_zero)]
                              (NotLeD (Asm 0)))

val _ =
  check
    ("replay golden: NotLeDD",
     fn () => replay_is_false [num_not (num_leq num_zero num_zero)]
                              (NotLeDD (Asm 0)))

fun add_replay relation1 relation2 =
  replay_is_false
    [relation1 (num_plus num_x num_three)
       (num_plus num_y num_two),
     relation2 num_y num_x]
    (Added (Asm 0, Asm 1))

val _ =
  check
    ("replay golden: Added with le/le add_mono",
     fn () => add_replay num_leq num_leq)

val _ =
  check
    ("replay golden: Added with lt/lt add_mono",
     fn () => add_replay num_less num_less)

val _ =
  check
    ("replay golden: Added with le/lt add_mono",
     fn () => add_replay num_leq num_less)

val _ =
  check
    ("replay golden: Added with lt/le add_mono",
     fn () => add_replay num_less num_leq)

val _ =
  check
    ("replay golden: Multiplied with le mult_mono",
     fn () =>
       replay_is_false [num_leq num_one num_zero]
         (Multiplied (two, Asm 0)))

val _ =
  check
    ("replay golden: Multiplied with positive-premise lt mult_mono",
     fn () =>
       replay_is_false
         [num_less (num_plus num_x num_three)
            (num_plus num_x num_two)]
         (Multiplied (two, Asm 0)))

fun num_instance_with_mult_mono mult_mono =
  let
    val dest = #dest num_instance
    val kit = #kit num_instance
  in
    {ty = #ty num_instance,
     discrete = #discrete num_instance,
     dest = dest,
     kit =
       {add_mono = #add_mono kit,
        mult_mono = mult_mono,
        lessD = #lessD kit,
        not_less = #not_less kit,
        not_le = #not_le kit,
        neqE = #neqE kit,
        nonneg = #nonneg kit},
     norm_conv = #norm_conv num_instance,
     pre_split = #pre_split num_instance,
     divmod_facts = #divmod_facts num_instance} :
      linarithData.linarith_instance
  end

val _ =
  check
    ("replay golden: Multiplied falls back to iterated addition",
     fn () =>
       let
         val _ =
           linarithData.register_instance
             (num_instance_with_mult_mono [])
         val result =
           replay_is_false [num_less num_zero num_zero]
             (Multiplied (two, Asm 0))
         val _ = linarithData.register_instance num_instance
       in
         result
       end)

val _ =
  check
    ("replay scales equality with AP_TERM and no mult_mono lemma",
     fn () =>
       let
         val _ =
           linarithData.register_instance
             (num_instance_with_mult_mono [])
         val result =
           replay_is_false [num_eq num_one num_zero]
             (Multiplied (two, Asm 0))
         val _ = linarithData.register_instance num_instance
       in
         result
       end)

val _ =
  check
    ("replay scales equality by a negative multiplier",
     fn () =>
       replay_is_false [num_eq num_one num_zero]
         (Multiplied (Arbint.~ two, Asm 0)))

val _ =
  check
    ("replay generalizes and restores one shared complex atom",
     fn () =>
       let
         val atom = numSyntax.mk_div (num_x, num_three)
         val terms =
           [num_leq (num_plus atom num_three) num_two,
            num_leq num_zero atom]
         val shared = ref false
         fun prove generalized =
           let
             val (left_expression, _) =
               numSyntax.dest_leq (List.nth (generalized, 0))
             val (left_atom, _) =
               numSyntax.dest_plus left_expression
             val (_, right_atom) =
               numSyntax.dest_leq (List.nth (generalized, 1))
             val _ =
               shared :=
                 (Term.is_var left_atom andalso
                  Term.aconv left_atom right_atom)
           in
             replay generalized (Added (Asm 0, Asm 1))
           end
         val theorem = linarithReplay.generalize terms prove
       in
         !shared andalso
         Term.aconv (Thm.concl theorem) boolSyntax.F andalso
         List.all
           (fn tm => List.exists (Term.aconv tm) (Thm.hyp theorem)) terms
       end)

(* TODO: Add the injection add-fallback golden with the first real cross-type
   instance kit.  The only injection available here is decomposition-only;
   its placeholder hom theorems are not valid replay rules. *)

val split_x = Term.mk_var ("linarith_split_x", numSyntax.num)
val split_y = Term.mk_var ("linarith_split_y", numSyntax.num)
val split_x_neq_one = num_not (num_eq split_x num_one)
val split_y_neq_one = num_not (num_eq split_y num_one)
val split_x_upper = num_leq split_x num_one
val split_x_lower = num_leq num_one split_x
val split_y_upper = num_leq split_y num_one
val split_y_lower = num_leq num_one split_y
val split_conclusion = num_leq split_x num_one

val one_split_config : linarithData.linarith_config =
  {neq_limit = 1, split_limit = 9}
val two_split_config : linarithData.linarith_config =
  {neq_limit = 2, split_limit = 9}

fun forward_with disequalities =
  linarithReplay.fwd_prove two_split_config
    (List.map Thm.ASSUME
      (disequalities @
        [split_x_upper, split_x_lower,
         split_y_upper, split_y_lower]))
    split_conclusion

fun tactic_replay_succeeds config assumptions conclusion =
  case linarithSolve.prove config linarithDecomp.decomp
         assumptions conclusion of
      (_, NONE) => false
    | (split_neq, SOME justifications) =>
        let
          val (goals, _) =
            Tactical.VALID
              (linarithReplay.refute_tac split_neq justifications)
              (assumptions, conclusion)
        in
          null goals
        end

val _ =
  check
    ("forward replay proves a num consequence with one neq split",
     fn () =>
       let
         val theorem =
           linarithReplay.fwd_prove one_split_config
             (List.map Thm.ASSUME
               [split_x_neq_one, split_x_upper, split_x_lower])
             split_conclusion
       in
         Term.aconv (Thm.concl theorem) split_conclusion andalso
         List.exists (Term.aconv split_x_neq_one) (Thm.hyp theorem)
       end)

val _ =
  check
    ("forward replay handles nested neq splits at the configured limit",
     fn () =>
       let
         val theorem =
           forward_with [split_x_neq_one, split_y_neq_one]
       in
         Term.aconv (Thm.concl theorem) split_conclusion
       end)

val _ =
  check
    ("permuting num neq premises preserves both replay styles",
     fn () =>
       let
         val orders =
           [[split_x_neq_one, split_y_neq_one],
            [split_y_neq_one, split_x_neq_one]]
         fun forward_succeeds assumptions =
           Term.aconv (Thm.concl (forward_with assumptions))
             split_conclusion
         fun tactic_succeeds assumptions =
           tactic_replay_succeeds two_split_config
             (assumptions @
               [split_x_upper, split_x_lower,
                split_y_upper, split_y_lower])
             split_conclusion
       in
         List.all forward_succeeds orders andalso
         List.all tactic_succeeds orders
       end)

val _ =
  check
    ("tactic replay closes an explicit neq goal through Tactical.VALID",
     fn () =>
       tactic_replay_succeeds one_split_config
         [split_x_neq_one, split_x_upper, split_x_lower]
         split_conclusion)

(* Public no-preprocessing surface. *)

fun valid_closes tactic goal =
  case #1 (Tactical.VALID tactic goal) of
      [] => true
    | _ => false

val public_x = Term.mk_var ("linarith_public_x", numSyntax.num)
val public_y = Term.mk_var ("linarith_public_y", numSyntax.num)
val public_z = Term.mk_var ("linarith_public_z", numSyntax.num)
val public_x_le_y = num_leq public_x public_y
val public_y_le_z = num_leq public_y public_z
val public_x_le_z = num_leq public_x public_z

val forward_tm =
  boolSyntax.list_mk_forall
    ([public_x, public_y, public_z],
     boolSyntax.mk_imp
       (boolSyntax.mk_conj (public_x_le_y, public_y_le_z),
        public_x_le_z))

val _ =
  check
    ("num norm_conv refutes a successor self-bound",
     fn () =>
       Term.aconv
         (normalized_rhs
           (num_leq (num_plus public_z num_one) public_z))
         boolSyntax.F)

val _ =
  check
    ("LINARITH_PROVE strips universals and atomizes conjunctive premises",
     fn () =>
       let val theorem = linarithLib.LINARITH_PROVE forward_tm
       in
         null (Thm.hyp theorem) andalso
         Term.aconv (Thm.concl theorem) forward_tm
       end)

val true_conv_tm =
  boolSyntax.mk_imp
    (public_x_le_y,
     num_leq public_x (num_plus public_y num_one))

val _ =
  check
    ("LINARITH_CONV proves a linear implication",
     fn () =>
       let
         val theorem = linarithLib.LINARITH_CONV true_conv_tm
         val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
       in
         Term.aconv left true_conv_tm andalso
         Term.aconv right boolSyntax.T
       end)

val false_conv_tm = num_less num_three num_two

val _ =
  check
    ("LINARITH_CONV disproves a false arithmetic relation",
     fn () =>
       let
         val theorem = linarithLib.LINARITH_CONV false_conv_tm
         val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
       in
         Term.aconv left false_conv_tm andalso
         Term.aconv right boolSyntax.F
       end)

val _ =
  check
    ("SIMPLE_LINARITH_TAC uses discreteness through Tactical.VALID",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([num_less public_x public_y],
          num_leq (num_plus public_x num_one) public_y))

val public_x_neq_one = num_not (num_eq public_x num_one)

val _ =
  check
    ("SIMPLE_LINARITH_TAC splits disequalities through Tactical.VALID",
     fn () =>
       valid_closes (linarithLib.SIMPLE_LINARITH_TAC [])
         ([public_x_neq_one, num_leq public_x num_one],
          num_less public_x num_one))

fun marker_error_name marker =
  ((ignore (linarithLib.SIMPLE_LINARITH_TAC [marker]); false)
   handle Feedback.HOL_ERR error =>
     String.isSubstring "SIMPLE_LINARITH_TAC"
       (Feedback.message_of error))

val _ =
  check
    ("SIMPLE_LINARITH_TAC loudly rejects foreign argument markers",
     fn () =>
       List.all marker_error_name
         [markerLib.Split (hd (#pre_split num_instance)),
          clasetLib.Intro boolTheory.TRUTH,
          clasetLib.Simp boolTheory.TRUTH,
          clasetLib.Iff boolTheory.TRUTH,
          clasetLib.Norm boolTheory.TRUTH])

(* Full num preprocessing battery.  All positive tactic tests go through
   VALID so the generated proof is checked against the original goal. *)

val irrelevant_premise =
  Term.mk_var ("linarith_irrelevant_premise", Type.bool)
val connective_premise =
  boolSyntax.mk_conj (public_x_le_y, public_y_le_z)
val existential_premise =
  boolSyntax.mk_exists
    (public_z,
     boolSyntax.mk_conj (public_x_le_y, public_y_le_z))
val total_order_goal =
  boolSyntax.mk_disj (public_x_le_y, num_leq public_y public_x)
val iff_premise = boolSyntax.mk_eq (boolSyntax.T, public_x_le_y)

val _ =
  check
    ("full preprocessing filters relevance and flattens connectives",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([irrelevant_premise, connective_premise], public_x_le_z) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], total_order_goal) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([existential_premise], public_x_le_y) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([iff_premise], public_x_le_y))

val public_min = numSyntax.mk_min (public_x, public_y)
val public_max = numSyntax.mk_max (public_x, public_y)
val min_le_left = num_leq public_min public_x
val left_le_max = num_leq public_x public_max

val _ =
  check
    ("LINARITH_TAC eliminates num MIN and MAX",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC []) ([], min_le_left) andalso
       valid_closes (linarithLib.LINARITH_TAC []) ([], left_le_max))

val _ =
  check
    ("full preprocessing is strictly stronger than SIMPLE on MIN",
     fn () =>
       let
         val simple_fails =
           ((ignore
               (Tactical.VALID
                 (linarithLib.SIMPLE_LINARITH_TAC [])
                 ([], min_le_left));
             false)
            handle Feedback.HOL_ERR _ => true)
       in
         simple_fails andalso
         valid_closes (linarithLib.LINARITH_TAC []) ([], min_le_left)
       end)

val subtraction_zero =
  num_eq (numSyntax.mk_minus (public_x, public_y)) num_zero

val _ =
  check
    ("LINARITH_TAC splits natural subtraction",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([num_less public_x public_y], subtraction_zero))

val public_div_three = numSyntax.mk_div (public_x, num_three)
val public_mod_three = numSyntax.mk_mod (public_x, num_three)
val div_equation =
  Thm.concl
    (hd ((valOf (#divmod_facts num_instance)) public_div_three))
val mod_bound = num_less public_mod_three num_three

val _ =
  check
    ("LINARITH_TAC augments literal DIV/MOD atoms with DIVISION facts",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([num_less num_zero public_x], mod_bound) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], div_equation))

val one_pipeline_round : linarithLib.linarith_config =
  {neq_limit = 9, split_limit = 1}
val zero_pipeline_rounds : linarithLib.linarith_config =
  {neq_limit = 9, split_limit = 0}
val two_pipeline_rounds : linarithLib.linarith_config =
  {neq_limit = 9, split_limit = 2}
val nine_pipeline_rounds : linarithLib.linarith_config =
  {neq_limit = 9, split_limit = 9}

fun tactic_fails tactic goal =
  ((ignore (Tactical.VALID tactic goal); false)
   handle Feedback.HOL_ERR _ => true)

val _ =
  check
    ("div/mod augmentation is bounded by split_limit",
     fn () =>
       tactic_fails
         (linarithLib.CFG_LINARITH_TAC zero_pipeline_rounds [])
         ([], mod_bound) andalso
       valid_closes
         (linarithLib.CFG_LINARITH_TAC one_pipeline_round [])
         ([], mod_bound))

val nested_div =
  numSyntax.mk_div
    (numSyntax.mk_div (public_x, num_three), num_two)
val nested_div_trigger = num_leq nested_div nested_div

val _ =
  check
    ("nested div/mod augmentation reaches a bounded fixpoint",
     fn () =>
       let
         val goal =
           ([nested_div_trigger, num_leq num_one num_zero],
            num_leq public_x public_x)
       in
         tactic_fails
           (linarithLib.CFG_LINARITH_TAC one_pipeline_round []) goal andalso
         valid_closes
           (linarithLib.CFG_LINARITH_TAC two_pipeline_rounds []) goal
       end)

val nested_min =
  numSyntax.mk_min (numSyntax.mk_min (public_x, public_y), public_z)
val nested_min_goal = num_leq nested_min public_x

val _ =
  check
    ("split fixpoint is bounded and accepts a CFG limit override",
     fn () =>
       tactic_fails
         (linarithLib.CFG_LINARITH_TAC one_pipeline_round [])
         ([], nested_min_goal) andalso
       valid_closes
         (linarithLib.CFG_LINARITH_TAC nine_pipeline_rounds [])
         ([], nested_min_goal))

val _ =
  check
    ("LINARITH_TAC accepts a validated per-call Split marker",
     fn () =>
       valid_closes
         (linarithLib.LINARITH_TAC
           [markerLib.Split linarithSeedTheory.NUM_MIN_SPLIT])
         ([], min_le_left))

fun full_marker_error marker =
  ((ignore (linarithLib.LINARITH_TAC [marker]); false)
   handle Feedback.HOL_ERR error =>
     String.isSubstring "LINARITH_TAC" (Feedback.message_of error) orelse
     String.isSubstring "CFG_LINARITH_TAC" (Feedback.message_of error))

val _ =
  check
    ("LINARITH_TAC rejects foreign argument markers",
     fn () =>
       List.all full_marker_error
         [clasetLib.Intro boolTheory.TRUTH,
          clasetLib.Simp boolTheory.TRUTH,
          clasetLib.Norm boolTheory.TRUTH])

val full_neq_one : linarithLib.linarith_config =
  {neq_limit = 1, split_limit = 9}
val full_neq_zero : linarithLib.linarith_config =
  {neq_limit = 0, split_limit = 9}
val neq_goal = num_less public_x num_one
val neq_assumptions = [public_x_neq_one, num_leq public_x num_one]

val _ =
  check
    ("CFG_LINARITH_TAC splits neq at the limit and ignores it above",
     fn () =>
       valid_closes
         (linarithLib.CFG_LINARITH_TAC full_neq_one [])
         (neq_assumptions, neq_goal) andalso
       tactic_fails
         (linarithLib.CFG_LINARITH_TAC full_neq_zero [])
         (neq_assumptions, neq_goal))

val _ =
  check
    ("LINARITH_PROVE performs no MIN preprocessing",
     fn () =>
       ((ignore (linarithLib.LINARITH_PROVE min_le_left); false)
        handle Feedback.HOL_ERR _ => true) andalso
       valid_closes (linarithLib.LINARITH_TAC []) ([], min_le_left))

val nonlinear_goal =
  num_leq (numSyntax.mk_mult (public_x, public_x)) public_x

val _ =
  check
    ("nonlinear goals fail cleanly without leaking global state",
     fn () =>
       let
         val facts_before = List.length (linarithData.arith_facts ())
         val splits_before =
           List.length (linarithData.arith_split_thms ())
         val injections_before =
           List.length (linarithData.injections ())
         val failed =
           ((ignore
               (linarithLib.SIMPLE_LINARITH_TAC [] ([], nonlinear_goal));
             false)
            handle Feedback.HOL_ERR _ => true)
       in
         failed andalso
         facts_before = List.length (linarithData.arith_facts ()) andalso
         splits_before =
           List.length (linarithData.arith_split_thms ()) andalso
         injections_before = List.length (linarithData.injections ()) andalso
         Option.isSome (linarithData.instance_for numSyntax.num)
       end)

val unregistered_ty =
  Type.mk_type ("fun", [numSyntax.num, numSyntax.num])
val unregistered_left =
  Term.mk_var ("linarith_unregistered_left", unregistered_ty)
val unregistered_right =
  Term.mk_var ("linarith_unregistered_right", unregistered_ty)
val unregistered_goal =
  boolSyntax.mk_eq (unregistered_left, unregistered_right)
val unregistered_message =
  "no linarith instance for " ^ Parse.type_to_string unregistered_ty ^
  " (load intLinarith / realLinarith / ratLinarith?)"

fun has_unregistered_message operation =
  ((operation (); false)
   handle Feedback.HOL_ERR error =>
     Feedback.message_of error = unregistered_message)

val _ =
  check
    ("all public entries report the stable unregistered-carrier message",
     fn () =>
       List.all has_unregistered_message
         [fn () =>
            ignore
              (linarithLib.SIMPLE_LINARITH_TAC []
                ([], unregistered_goal)),
          fn () => ignore (linarithLib.LINARITH_PROVE unregistered_goal),
          fn () => ignore (linarithLib.LINARITH_CONV unregistered_goal)])

(* Reducer, solver, and cache integration. *)

fun reducer_conversion theorems tm =
  let
    val {initial, addcontext, apply, ...} =
      Traverse.dest_reducer linarithLib.LINARITH_REDUCER
    val context = addcontext (initial, theorems)
  in
    apply
      {solver = fn _ => Conv.NO_CONV,
       conv = fn _ => Conv.NO_CONV,
       context = context,
       stack = [],
       relation = (boolSyntax.equality, Thm.REFL)} tm
  end

fun reducer_succeeds theorems tm =
  ((ignore (reducer_conversion theorems tm); true)
   handle Feedback.HOL_ERR _ => false)

val _ =
  check
    ("LINARITH_REDUCER admits local arithmetic context",
     fn () =>
       (linarithLib.clear_linarith_caches ();
        reducer_succeeds [Thm.ASSUME public_x_le_y] public_x_le_y andalso
        reducer_succeeds [Thm.ASSUME public_x_le_y] public_x_le_y))

val conjunctive_context =
  HolKernel.CONJ
    (Thm.ASSUME public_x_le_y) (Thm.ASSUME public_y_le_z)

val _ =
  check
    ("CACHED_LINARITH tracks atoms in conjunctive context",
     fn () =>
       (linarithLib.clear_linarith_caches ();
        Term.aconv
          (Thm.concl
            (linarithLib.CACHED_LINARITH
              [conjunctive_context] public_x_le_z))
          (boolSyntax.mk_eq (public_x_le_z, boolSyntax.T))))

val nonlinear_closed_fact = arithmeticTheory.X_LE_X_SQUARED
val nonlinear_closed_goal = Thm.concl nonlinear_closed_fact
val quantified_nonlinear_fact =
  Thm.GEN public_x nonlinear_closed_fact

val _ =
  check
    ("LINARITH_REDUCER applies context admission screens",
     fn () =>
       (linarithLib.clear_linarith_caches ();
        not (reducer_succeeds [nonlinear_closed_fact]
               nonlinear_closed_goal) andalso
        (linarithLib.clear_linarith_caches ();
         not (reducer_succeeds [quantified_nonlinear_fact]
                nonlinear_closed_goal)) andalso
        (linarithLib.clear_linarith_caches ();
         not (reducer_succeeds [boolTheory.TRUTH] public_x_le_y))))

val min_le_rule = hd (Drule.CONJUNCTS arithmeticTheory.MIN_EQ_LE)
val linarith_side_ss =
  simpLib.++
    (simpLib.++ (simpLib.empty_ss, simpLib.rewrites [min_le_rule]),
     linarithLib.LINARITH_ss)
val min_side_goal =
  (boolSyntax.mk_eq (numSyntax.mk_min (public_x, public_z), public_x))

val _ =
  check
    ("LINARITH_ss discharges a conditional rewrite side condition",
     fn () =>
       valid_closes
         (simpLib.FULL_SIMP_TAC linarith_side_ss [])
         ([public_x_le_y, public_y_le_z], min_side_goal))

val _ =
  check
    ("lin_arith solver uses its supplied arithmetic context",
     fn () =>
       let
         val {name, solve} = linarithLib.linarith_solver
         val theorem =
           solve
             {stack = [],
              context_thms =
                [Thm.ASSUME public_x_le_y,
                 Thm.ASSUME public_y_le_z],
              recurse = Conv.NO_CONV} public_x_le_z
       in
         name = "lin_arith" andalso
         Term.aconv (Thm.concl theorem) public_x_le_z
       end)

fun with_arith_export operation =
  case ThmSetData.data_exportfns {settype = "arith"} of
      NONE => false
    | SOME export =>
        let
          val name = {Thy = "arithmetic", Name = "X_LE_X_SQUARED"}
          val remove_name = "arithmetic$X_LE_X_SQUARED"
          fun remove () =
            #remove export {thy = "arithmetic", remove = remove_name}
          val _ = #add export
            {thy = "arithmetic",
             named_thm = (name, nonlinear_closed_fact)}
          val result = operation () handle e =>
            (remove (); raise e)
          val _ = remove ()
        in
          result
        end

val _ =
  check
    ("cached failure is retried after dynamic [arith] growth",
     fn () =>
       let
         val _ = linarithLib.clear_linarith_caches ()
         val failed_before =
           not (reducer_succeeds [] nonlinear_closed_goal)
       in
         failed_before andalso
         with_arith_export
           (fn () => reducer_succeeds [] nonlinear_closed_goal)
       end)
