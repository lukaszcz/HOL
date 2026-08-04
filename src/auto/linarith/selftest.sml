open testutils
open linarithSolve
open linarithCorpus

val two = Arbint.two
val three = Arbint.fromInt 3

fun last xs = hd (rev xs)

val _ =
  check
    ("linarith ships the [arith] and [arith_split] tables empty",
     fn () =>
       null (linarithData.arith_facts ()) andalso
       null (linarithData.arith_split_thms ()))

(* The num split seeds no longer carry [arith_split]: they reach the
   split channel through the instance's pre_split, which is the other
   half of what the split rules union.  Pinned here, where the attribute
   table used to be. *)
val num_split_seeds =
  [linarithSeedTheory.NUM_MIN_SPLIT,
   linarithSeedTheory.NUM_MAX_SPLIT,
   linarithSeedTheory.NUM_SUB_SPLIT]

val _ =
  check
    ("the three num split seeds arrive through the instance channel",
     fn () =>
       let
         val pre_splits =
           List.concat (map #pre_split (linarithData.all_instances ()))
         fun offered seed =
           List.exists
             (fn rule => Term.aconv (Thm.concl rule) (Thm.concl seed))
             pre_splits
       in
         List.all offered num_split_seeds andalso
         List.all (not o splitLib.is_asm_split) num_split_seeds
       end)

val num_instance = linarithNum.instance

val _ =
  check
    ("linarithLib registers the num instance at module load",
     fn () =>
       case linarithData.instance_for numSyntax.num of
           SOME instance => Option.isSome (#discrete instance)
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

(* This directory's suite tests the one carrier it can parse, so the
   shared normalisation helpers are fixed to it here. *)
val normalized_rhs = linarithCorpus.normalized_rhs num_instance
val canonical_form = linarithCorpus.canonical_form num_instance

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

(* Cancellation runs once per Added node of every certificate, so it
   removes the whole common multiset of a relation rather than one
   summand per application: normalized_rhs applies norm_conv once, and
   what comes back has all three common summands gone. *)
val _ =
  check
    ("num norm_conv cancels three common summands in one application",
     fn () =>
       let
         val num_u = Term.mk_var ("linarith_num_u", numSyntax.num)
         val num_v = Term.mk_var ("linarith_num_v", numSyntax.num)
         fun sum terms = List.foldl (fn (t, acc) => num_plus acc t)
                           (hd terms) (tl terms)
         val relation =
           num_leq (sum [num_x, num_y, num_z, num_u])
             (sum [num_y, num_z, num_x, num_v])
       in
         Term.aconv (normalized_rhs relation) (num_leq num_u num_v)
       end)

val _ =
  check
    ("num norm_conv decides a ground relation",
     fn () =>
       Term.aconv
         (normalized_rhs (numSyntax.mk_less (num_seven, num_eight)))
         boolSyntax.T)

(* Replay normalizes the two sides of a derived relation, so norm_conv is
   offered bare expressions as well as relations.  It used to answer
   those by raising UNCHANGED out of the whole conversion, because
   relation_conv signalled "not a relation" that way and ORELSEC catches
   HOL_ERR only. *)
val _ =
  check
    ("num norm_conv canonicalizes a bare expression",
     fn () =>
       Term.aconv
         (canonical_form (num_plus num_three num_x))
         (canonical_form (num_plus num_x num_three)))

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
       let
         val facts = #atom_facts num_instance
         val div_tm = numSyntax.mk_div (num_x, num_three)
         val mod_tm = numSyntax.mk_mod (num_x, num_three)
       in
         List.length (facts div_tm) = 2 andalso
         List.length (facts mod_tm) = 2 andalso
         List.length (facts (numSyntax.mk_div
           (num_x, numSyntax.zero_tm))) = 1
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
      not_less = boolTheory.TRUTH,
      not_le = boolTheory.TRUTH,
      neqE = boolTheory.TRUTH,
      nonneg = (fn _ => NONE)},
   norm_conv = Conv.ALL_CONV,
   nnf_rules = [],
   pre_split = [],
   atom_facts = (fn _ => [])}

val _ = linarithData.register_instance (synthetic_instance NONE)
val _ =
  linarithData.register_instance
    (synthetic_instance (SOME {lessD = [boolTheory.TRUTH]}))

val _ =
  check
    ("instance registration replaces an existing same-type entry",
     fn () =>
       case linarithData.instance_for registry_ty of
           SOME instance => Option.isSome (#discrete instance)
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
   discrete = NONE,
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
      not_less = boolTheory.TRUTH,
      not_le = boolTheory.TRUTH,
      neqE = boolTheory.TRUTH,
      nonneg = (fn _ => NONE)},
   norm_conv = Conv.ALL_CONV,
   nnf_rules = [],
   pre_split = [],
   atom_facts = (fn _ => [])}

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

(* Fourier--Motzkin is reached the way replay reaches it: prove takes
   the hypotheses, a decomposition for each, and the conclusion whose
   negation joins them.  fm_refute states a system as the
   decompositions its rows are built from, so what the checks below
   pin is the certificate the engine derives and not the shape a row
   is held in.

   The conclusion here decomposes to nothing and so contributes no
   row, which leaves the hypothesis in position i as Asm i -- the
   numbering replay resolves against the caller's assumption list. *)
val fm_config : linarithData.linarith_config =
  {neq_limit = 9, split_limit = 9}

val fm_conclusion = Term.mk_var ("linarith_fm_conclusion", Type.bool)

fun fm_refute decomps =
  let
    val hypotheses =
      List.tabulate
        (List.length decomps,
         fn i =>
            Term.mk_var ("linarith_fm_" ^ Int.toString i, Type.bool))
    val table = ListPair.zip (hypotheses, decomps)
    fun decompose tm =
      case List.find (fn (hyp, _) => Term.aconv hyp tm) table of
          SOME (_, decomp) => decomp
        | NONE => NONE
  in
    case prove fm_config decompose (fn _ => false) hypotheses
                fm_conclusion of
        (_, SOME [just]) => SOME just
      | _ => NONE
  end

(* A premise as the decomposition a caller would hand prove for it. *)
fun fm_relation rel (lhs, lhs_const) (rhs, rhs_const) =
  Decomp {lhs = lhs, lhs_const = lhs_const, rel = rel, rhs = rhs,
          rhs_const = rhs_const, discrete = true, negated = false}

val fm_le = fm_relation REL_LE
val fm_eq = fm_relation REL_EQ

val fm_x = Term.mk_var ("linarith_fm_x", numSyntax.num)
val fm_z = Term.mk_var ("linarith_fm_z", numSyntax.num)

val fm_rat = Arbrat.fromInt
val no_atoms : (Term.term * Arbrat.rat) list = []
fun fm_scaled_x c = [(fm_x, fm_rat c)]

(* 0 <= x against 1 <= ~x: the two rows add as they stand to 1 <= 0. *)
val _ =
  check
    ("FM derives the expected unit-coefficient certificate",
     fn () =>
       case fm_refute
              [SOME (fm_le (no_atoms, fm_rat 0)
                       (fm_scaled_x 1, fm_rat 0)),
               SOME (fm_le (no_atoms, fm_rat 1)
                       (fm_scaled_x ~1, fm_rat 0))] of
           SOME (Added (Asm 0, Asm 1)) => true
         | _ => false)

(* 0 <= 2x against 1 <= ~3x: eliminating x scales each row up to the
   two coefficients' lcm, and both multipliers reach the certificate,
   which is what replay scales the assumptions by. *)
val _ =
  check
    ("FM records integer scaling in the certificate",
     fn () =>
       case fm_refute
              [SOME (fm_le (no_atoms, fm_rat 0)
                       (fm_scaled_x 2, fm_rat 0)),
               SOME (fm_le (no_atoms, fm_rat 1)
                       (fm_scaled_x ~3, fm_rat 0))] of
           SOME (Added (Multiplied (m, Asm 0), Multiplied (n, Asm 1))) =>
             m = three andalso n = two
         | _ => false)

(* 0 <= 0 is trivial and says nothing, so a refutation has to come from
   the rows around it; 1 = 0 is trivial and contradictory by itself,
   and is reported against the premise it was built from. *)
val _ =
  check
    ("trivial rows are discarded and contradictory rows detected",
     fn () =>
       (case fm_refute
               [SOME (fm_le (no_atoms, fm_rat 0) (no_atoms, fm_rat 0)),
                SOME (fm_le (no_atoms, fm_rat 0)
                        (fm_scaled_x 1, fm_rat 0)),
                SOME (fm_le (no_atoms, fm_rat 1)
                        (fm_scaled_x ~1, fm_rat 0))] of
            SOME (Added (Asm 1, Asm 2)) => true
          | _ => false) andalso
       (case fm_refute
               [NONE, NONE,
                SOME (fm_eq (no_atoms, fm_rat 1) (no_atoms, fm_rat 0))] of
            SOME (Asm 2) => true
          | _ => false))

(* Elimination that runs out of eliminable columns reports no
   certificate rather than raising, which is how a satisfiable system
   reaches the caller. *)
val _ =
  check
    ("a satisfiable system yields no certificate",
     fn () =>
       case fm_refute
              [SOME (fm_le (no_atoms, fm_rat 0)
                       (fm_scaled_x 1, fm_rat 0))] of
           NONE => true
         | _ => false)

val huge =
  Arbint.fromString "100000000000000000000000000000000000003"
val tiny = Arbrat./ (Arbrat.one, Arbrat.fromAInt huge)

(* A coefficient whose denominator exceeds any machine word is cleared
   by scaling the whole row by that denominator, and the multiplier
   reaches the certificate, where replay owes the assumption exactly
   it. *)
val _ =
  check
    ("row building clears an arbitrary-precision denominator",
     fn () =>
       case fm_refute
              [SOME (fm_le ([(fm_x, tiny)], fm_rat 0)
                       (no_atoms, fm_rat 0)),
               SOME (fm_le (no_atoms, fm_rat 1)
                       (fm_scaled_x 1, fm_rat 0))] of
           SOME (Added (Asm 1, Multiplied (m, Asm 0))) => m = huge
         | _ => false)

(* Rows are built by scattering each side into the columns of one
   shared atom index, so an atom occurring on both sides of a relation
   and again in another premise has to land in the same column
   throughout: 5z + x <= 2z, 1 <= x and 0 <= z is refutable only if it
   does, and only with all three rows.  atoms_of_decomps fixes that
   column order, and replay reads the same ordering. *)
val scattered =
  fm_le ([(fm_z, fm_rat 5), (fm_x, fm_rat 1)], fm_rat 0)
    ([(fm_z, fm_rat 2)], fm_rat 0)

fun rests_on just index =
  let
    fun collect (Asm i) = i = index
      | collect (Nonneg _) = false
      | collect (LessD inner) = collect inner
      | collect (NotLessD inner) = collect inner
      | collect (NotLeD inner) = collect inner
      | collect (NotLeDD inner) = collect inner
      | collect (Multiplied (_, inner)) = collect inner
      | collect (Added (left, right)) =
          collect left orelse collect right
  in
    collect just
  end

val _ =
  check
    ("rows scatter each side into its atom's column",
     fn () =>
       Lib.list_eq Term.aconv (atoms_of_decomps [scattered])
         [fm_z, fm_x] andalso
       (case fm_refute
               [SOME scattered,
                SOME (fm_le (no_atoms, fm_rat 1)
                        (fm_scaled_x 1, fm_rat 0)),
                SOME (fm_le (no_atoms, fm_rat 0)
                        ([(fm_z, fm_rat 1)], fm_rat 0))] of
            SOME just => List.all (rests_on just) [0, 1, 2]
          | NONE => false))

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

(* Splitting a disequality moves its premise to the end of the case it
   generates, so the premises before it move up and the Asm indices of
   the case are the positions in that new order -- which is the order
   replay puts the goal's assumptions in.  Here the contradiction is
   the one premise that survives both splits, so every case is refuted
   by its first premise, and a case that kept the caller's original
   numbering would blame the second instead.  Two disequalities give
   one case per assignment, each with its own justification. *)
val _ =
  check
    ("split premises are renumbered for the case they end up in",
     fn () =>
       case prove {neq_limit = 2, split_limit = 9} unit_decomp
                  (fn _ => false)
                  [dense_neq_tm, contradiction_tm, discrete_neq_tm]
                  conclusion_tm of
           (true, SOME justs) =>
             List.length justs = 4 andalso
             List.all
               (fn Asm 0 => true | _ => false) justs
         | _ => false)

val _ =
  check
    ("prove splits at the neq_limit boundary",
     fn () =>
       case prove {neq_limit = 1, split_limit = 9} unit_decomp
                  (fn _ => false)
                  [dense_neq_tm, contradiction_tm] conclusion_tm of
           (true, SOME justs) => List.length justs = 2
         | _ => false)

val _ =
  check
    ("prove ignores all disequalities when neq_limit is exceeded",
     fn () =>
       case prove {neq_limit = 0, split_limit = 9} unit_decomp
                  (fn _ => false)
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
                  from_negated_conclusion (fn _ => false) []
                  conclusion_tm of
           (true, SOME [Asm 0]) => true
         | _ => false)

val _ =
  check
    ("prove avoids double negation of an already-negated conclusion",
     fn () =>
       case prove {neq_limit = 9, split_limit = 9}
                  from_unwrapped_conclusion (fn _ => false) []
                  negated_conclusion_tm of
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
  linarithReplay.mkthm (List.map Thm.ASSUME terms) justification

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
         (Added (Nonneg num_x, Asm 0)))

val _ =
  check
    ("replay rejects a Nonneg atom the instance declines",
     fn () =>
       ((ignore (replay [num_leq num_one num_zero] (Nonneg synth_x));
         false)
        handle Feedback.HOL_ERR error =>
          Feedback.message_of error =
            "instance declined nonnegative atom " ^
            Parse.term_to_string synth_x))

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
        not_less = #not_less kit,
        not_le = #not_le kit,
        neqE = #neqE kit,
        nonneg = #nonneg kit},
     norm_conv = #norm_conv num_instance,
     nnf_rules = #nnf_rules num_instance,
     pre_split = #pre_split num_instance,
     atom_facts = #atom_facts num_instance} :
      linarithData.linarith_instance
  end

(* Iterated addition builds the multiple by doubling, so a multiplier
   with a set bit above the least significant one -- 12 is 1100, 11 is
   1011 -- exercises more than one arm of the recursion.  The scaled row
   here cancels only against the exact multiple, so a dropped bit is a
   failed replay rather than a differently shaped route to the same
   falsity. *)
val _ =
  check
    ("replay golden: Multiplied falls back to iterated addition",
     fn () =>
       let
         val _ =
           linarithData.register_instance
             (num_instance_with_mult_mono [])
         fun exact n =
           let
             val literal = numSyntax.mk_numeral (Arbnum.fromInt n)
             fun scale tm = numSyntax.mk_mult (literal, tm)
           in
             replay_is_false
               [num_leq (num_plus (scale num_x) num_one) (scale num_y),
                num_leq num_y num_x]
               (Added (Asm 0, Multiplied (Arbint.fromInt n, Asm 1)))
           end
           handle Feedback.HOL_ERR _ => false
         val result =
           replay_is_false [num_less num_zero num_zero]
             (Multiplied (two, Asm 0)) andalso
           List.all exact [2, 11, 12]
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
         val (generalized, restore) = linarithReplay.generalize terms
         val (left_expression, _) =
           numSyntax.dest_leq (List.nth (generalized, 0))
         val (left_atom, _) = numSyntax.dest_plus left_expression
         val (_, right_atom) =
           numSyntax.dest_leq (List.nth (generalized, 1))
         val shared =
           Term.is_var left_atom andalso Term.aconv left_atom right_atom
         val theorem =
           restore (replay generalized (Added (Asm 0, Asm 1)))
       in
         shared andalso
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
  (case linarithReplay.refute config assumptions conclusion of
       NONE => false
     | SOME tactic =>
         null (#1 (Tactical.VALID tactic (assumptions, conclusion))))
  handle Feedback.HOL_ERR _ => false

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

(* The disequality is neither first nor last, so splitting it moves it
   past a premise the certificate then has to name one position
   earlier.  Both replay styles resolve the certificate against the
   assumptions themselves, so a case numbered as the caller wrote it
   rather than as the split left it picks the wrong assumption here and
   derives nothing. *)
val moved_neq_assumptions =
  [split_x_upper, split_x_neq_one, split_y_upper]
val moved_neq_conclusion = num_less split_x num_one

val _ =
  check
    ("a disequality split past a premise still names the right one",
     fn () =>
       let
         val theorem =
           linarithReplay.fwd_prove one_split_config
             (List.map Thm.ASSUME moved_neq_assumptions)
             moved_neq_conclusion
       in
         Term.aconv (Thm.concl theorem) moved_neq_conclusion andalso
         tactic_replay_succeeds one_split_config moved_neq_assumptions
           moved_neq_conclusion
       end)

(* Which disequalities replay splits has to be the test the search
   split them by, since the search emits one justification per case it
   generated and replay owes each of them a goal.  Answering "not this
   one" where the search said otherwise leaves refute_tac's THENL with
   more tactics than goals, and the arity mismatch is the whole of what
   the user then sees.  So an instance whose neqE does not apply to a
   disequality that passed the test is ill-formed, and is named. *)
fun num_instance_with_neqE neqE =
  let
    val kit = #kit num_instance
  in
    {ty = #ty num_instance,
     discrete = #discrete num_instance,
     dest = #dest num_instance,
     kit =
       {add_mono = #add_mono kit,
        mult_mono = #mult_mono kit,
        not_less = #not_less kit,
        not_le = #not_le kit,
        neqE = neqE,
        nonneg = #nonneg kit},
     norm_conv = #norm_conv num_instance,
     nnf_rules = #nnf_rules num_instance,
     pre_split = #pre_split num_instance,
     atom_facts = #atom_facts num_instance} :
      linarithData.linarith_instance
  end

fun replay_failure assumptions conclusion =
  (ignore
     (linarithReplay.fwd_prove one_split_config
       (List.map Thm.ASSUME assumptions) conclusion);
   NONE)
  handle Feedback.HOL_ERR error => SOME (Feedback.top_function_of error)

val _ =
  check
    ("an inapplicable neqE is named rather than left to THENL",
     fn () =>
       let
         val _ =
           linarithData.register_instance
             (num_instance_with_neqE boolTheory.TRUTH)
         val failure =
           replay_failure
             [split_x_neq_one, split_x_upper, split_x_lower]
             split_conclusion
           handle e =>
             (linarithData.register_instance num_instance; raise e)
         val _ = linarithData.register_instance num_instance
       in
         failure = SOME "split_assumption"
       end)

(* Public no-preprocessing surface. *)

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

val public_fact_positive =
  num_less num_zero (numSyntax.mk_fact public_x)
val public_fact_positive_theorem =
  Thm.SPEC public_x arithmeticTheory.FACT_LESS

val _ =
  check
    ("plain tactic arguments are inserted as arithmetic facts",
     fn () =>
       tactic_fails (linarithLib.SIMPLE_LINARITH_TAC [])
         ([], public_fact_positive) andalso
       valid_closes
         (linarithLib.SIMPLE_LINARITH_TAC
           [public_fact_positive_theorem])
         ([], public_fact_positive))

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

(* Choosing which disjunction to eliminate scores every disjunct
   against the same literals.  The goal below is the one that scoring
   has to work through: a chain of literals no disjunct closes on its
   own, so every disjunct is scored against all of them and every
   branch of the chosen disjunction is then searched. *)
val chain_vars =
  List.tabulate
    (9, fn i =>
       Term.mk_var ("linarith_chain_" ^ Int.toString i, numSyntax.num))
val chain_target = Term.mk_var ("linarith_chain_target", numSyntax.num)
val chain_literals =
  List.tabulate
    (8, fn i =>
       num_leq (List.nth (chain_vars, i)) (List.nth (chain_vars, i + 1)))
val chain_disjunction =
  boolSyntax.list_mk_disj
    (List.tabulate
       (5, fn i =>
          num_leq
            (num_plus (last chain_vars)
               (numSyntax.mk_numeral (Arbnum.fromInt (i + 1))))
            chain_target))

val _ =
  check
    ("a scored disjunction is eliminated and the chain closed",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         (chain_literals @ [chain_disjunction],
          num_leq (hd chain_vars) chain_target))

(* Conditionals are the propositional form the old six-theorem rewrite
   list could not reach; normalForms.NNF_CONV splits them on both sides
   of the turnstile. *)
val cond_condition =
  Term.mk_var ("linarith_cond_condition", Type.bool)
val cond_premise =
  boolSyntax.mk_cond
    (cond_condition, public_x_le_y, num_less public_x public_y)
val cond_goal =
  boolSyntax.mk_cond
    (cond_condition, public_x_le_y,
     num_leq public_x (numSyntax.mk_suc public_y))

val _ =
  check
    ("full preprocessing splits conditionals in premise and goal",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([cond_premise], public_x_le_y) andalso
       valid_closes (linarithLib.LINARITH_TAC [])
         ([num_less public_x public_y], cond_goal))

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
    (hd (#atom_facts num_instance public_div_three))
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
val nine_pipeline_rounds : linarithLib.linarith_config =
  {neq_limit = 9, split_limit = 9}

val _ =
  check
    ("default_config freezes both public limits at nine",
     fn () =>
       let
         val {neq_limit, split_limit} = linarithLib.default_config
       in
         neq_limit = 9 andalso split_limit = 9
       end)

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

(* The inner quotient is not an atom of either side, so closing this
   needs the facts the outer atom's own facts introduce: augmentation
   has to reach a fixpoint rather than stop after the atoms it was
   handed. *)
val nested_div_goal =
  ([num_less num_zero nested_div],
   num_less num_zero (numSyntax.mk_div (public_x, num_three)))

val _ =
  check
    ("nested div/mod augmentation reaches a bounded fixpoint",
     fn () =>
       tactic_fails
         (linarithLib.CFG_LINARITH_TAC zero_pipeline_rounds [])
         nested_div_goal andalso
       valid_closes
         (linarithLib.CFG_LINARITH_TAC one_pipeline_round [])
         nested_div_goal)

(* The certificate for this one scales a row twice, so replay builds
   q * 2 * 3 while the other side carries q * 6.  Cancellation matches
   summands syntactically, so until scaling renormalized its result and
   num canonicalized products, the solver reported a refutation that
   replay then could not derive falsity from. *)
val _ =
  check
    ("a doubly scaled row replays to falsity",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([], boolSyntax.mk_imp
                (num_less num_zero nested_div,
                 num_leq (numSyntax.mk_numeral (Arbnum.fromInt 6))
                   public_x)))

(* Splitting on demand means the rounds are spent only when the
   arithmetic cannot close the goal without them: a goal refutable as it
   stands is closed even where no round is allowed at all, however much
   nested div/mod its assumptions carry. *)
val _ =
  check
    ("no augmentation round is spent on an already refutable goal",
     fn () =>
       valid_closes
         (linarithLib.CFG_LINARITH_TAC zero_pipeline_rounds [])
         ([nested_div_trigger, num_leq num_one num_zero],
          num_leq public_x public_x))

val nested_min =
  numSyntax.mk_min (numSyntax.mk_min (public_x, public_y), public_z)
val nested_min_goal = num_leq nested_min public_x

val _ =
  check
    ("operator splitting is bounded and accepts a CFG limit override",
     fn () =>
       tactic_fails
         (linarithLib.CFG_LINARITH_TAC one_pipeline_round [])
         ([], nested_min_goal) andalso
       valid_closes
         (linarithLib.CFG_LINARITH_TAC nine_pipeline_rounds [])
         ([], nested_min_goal))

val public_condition =
  Term.mk_var ("linarith_public_condition", Type.bool)
val public_conditional =
  boolSyntax.mk_cond (public_condition, public_x, public_y)
val public_conditional_bound = num_leq public_conditional public_z
val public_bool_split = TypeBase.case_pred_disj_of ``:bool``

val _ =
  check
    ("LINARITH_TAC consumes a per-call Split rule absent from its seeds",
     fn () =>
       let
         val goal =
           ([public_x_le_z, public_y_le_z], public_conditional_bound)
       in
         tactic_fails (linarithLib.LINARITH_TAC []) goal andalso
         valid_closes
           (linarithLib.LINARITH_TAC
             [markerLib.Split public_bool_split]) goal
       end)

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

(* The carrier read off a conclusion is a guess about where to look for
   arithmetic, not a precondition on the goal: a contradictory context
   refutes a conclusion of any type. *)
val list_ty = listSyntax.mk_list_type Type.alpha
val list_l1 = Term.mk_var ("linarith_l1", list_ty)
val list_l2 = Term.mk_var ("linarith_l2", list_ty)

val _ =
  check
    ("a contradictory context closes a goal at an unregistered carrier",
     fn () =>
       valid_closes (linarithLib.LINARITH_TAC [])
         ([num_less public_x num_zero],
          boolSyntax.mk_eq (list_l1, list_l2)))

val unregistered_ty =
  Type.mk_type ("fun", [numSyntax.num, numSyntax.num])
val unregistered_left =
  Term.mk_var ("linarith_unregistered_left", unregistered_ty)
val unregistered_right =
  Term.mk_var ("linarith_unregistered_right", unregistered_ty)
val unregistered_goal =
  boolSyntax.mk_eq (unregistered_left, unregistered_right)
(* Built from the registry, like the hint itself: a roster spelled out
   here would go stale the moment a carrier is added. *)
val unregistered_message =
  "linear arithmetic found no proof (no linarith instance for " ^
  Parse.type_to_string unregistered_ty ^ "; registered: " ^
  String.concatWith ", "
    (map (Parse.type_to_string o #ty) (linarithData.all_instances ())) ^
  ")"

fun has_unregistered_message operation =
  ((operation (); false)
   handle Feedback.HOL_ERR error =>
     Feedback.message_of error = unregistered_message)

val _ =
  check
    ("all public entries report the same unregistered-carrier failure",
     fn () =>
       List.all has_unregistered_message
         [fn () =>
            ignore
              (linarithLib.LINARITH_TAC [] ([], unregistered_goal)),
          fn () =>
            ignore
              (linarithLib.SIMPLE_LINARITH_TAC []
                ([], unregistered_goal)),
          fn () =>
            ignore
              (linarithLib.CFG_LINARITH_TAC
                linarithLib.default_config [] ([], unregistered_goal)),
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

(* The branch cache_check does not take: a plain boolean atom is neither
   relevant nor F, so the solver keeps the direct forward call and can
   still discharge it from a contradictory arithmetic context. *)
val public_p = Term.mk_var ("linarith_public_p", Type.bool)
val public_successor_bound =
  num_leq (num_plus public_z num_one) public_z

val _ =
  check
    ("lin_arith solver discharges a non-arithmetic side condition",
     fn () =>
       let
         val {solve, ...} = linarithLib.linarith_solver
         val outside_guard =
           not (linarithDecomp.is_relevant public_p) andalso
           not (Term.aconv public_p boolSyntax.F)
         val theorem =
           solve
             {stack = [],
              context_thms = [Thm.ASSUME public_successor_bound],
              recurse = Conv.NO_CONV} public_p
       in
         outside_guard andalso
         Term.aconv (Thm.concl theorem) public_p
       end)

(* The [arith] tests below drive the table through the export the
   attribute itself uses, so what they exercise is the table a user's
   annotation reaches rather than a private hook.  NONE is "this
   session has no such export", which is a failed assertion wherever it
   is asked for. *)
fun with_arith_exports named_thms operation =
  case ThmSetData.data_exportfns {settype = "arith"} of
      NONE => NONE
    | SOME export =>
        let
          fun add named_thm =
            #add export {thy = "arithmetic", named_thm = named_thm}
          fun remove ({Thy, Name}, _) =
            #remove export
              {thy = "arithmetic", remove = Thy ^ "$" ^ Name}
          fun remove_all () = List.app remove named_thms
          val _ = List.app add named_thms
          val result = operation () handle e => (remove_all (); raise e)
          val _ = remove_all ()
        in
          SOME result
        end

fun with_arith_export operation =
  case with_arith_exports
         [({Thy = "arithmetic", Name = "X_LE_X_SQUARED"},
           nonlinear_closed_fact)]
         operation of
      NONE => false
    | SOME result => result

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

(* A call the reducer's guard admits carries the whole [arith] table
   into its context, assumed.  Splitting the table into literals and
   assuming them is a pure function of the table and is derived once
   per state of it, so what a repeated call spends on the table is the
   discharge of its result against those literals and nothing else.

   A bound rather than a count: one more [arith] fact costs a repeated
   call at most one PROVE_HYP, and what a PROVE_HYP costs is measured
   here rather than written down.  Inference counting is a global
   kernel flag, off in a fresh session and put back off. *)
fun counted work =
  let
    val meter = Count.mk_meter ()
    val _ = work ()
    val prims = #prims (Count.read meter)
    val _ = Count.counting_thms false
  in
    prims
  end

val discharge_prims =
  let
    val left = Thm.ASSUME public_x_le_y
    val right = Thm.ASSUME public_y_le_z
  in
    counted (fn () => ignore (Drule.PROVE_HYP left right))
  end

val envelope_rounds = 4

(* One warming call, uncounted: what the repeats after it spend is the
   envelope, since the cache answers the goal itself. *)
fun envelope_prims named_thms =
  let
    val {solve, ...} = linarithLib.linarith_solver
    val context = [Thm.ASSUME public_x_le_y, Thm.ASSUME public_y_le_z]
    fun call () =
      ignore
        (solve
          {stack = [], context_thms = context, recurse = Conv.NO_CONV}
          public_x_le_z)
    fun repeat 0 = ()
      | repeat rounds = (call (); repeat (rounds - 1))
  in
    with_arith_exports named_thms
      (fn () =>
        (linarithLib.clear_linarith_caches ();
         call ();
         counted (fn () => repeat envelope_rounds)))
  end

(* One literal apiece: a conjunctive fact contributes a discharge per
   conjunct, and the bound is stated per fact. *)
val envelope_facts =
  [({Thy = "arithmetic", Name = "LESS_EQ_REFL"},
    arithmeticTheory.LESS_EQ_REFL),
   ({Thy = "arithmetic", Name = "ZERO_LESS_EQ"},
    arithmeticTheory.ZERO_LESS_EQ),
   ({Thy = "arithmetic", Name = "LESS_EQ_ADD"},
    arithmeticTheory.LESS_EQ_ADD)]

val _ =
  check
    ("a repeated call pays the [arith] table its discharge and no more",
     fn () =>
       case (envelope_prims [], envelope_prims envelope_facts) of
           (SOME bare, SOME loaded) =>
             0 < discharge_prims andalso
             loaded - bare <=
               envelope_rounds * length envelope_facts * discharge_prims
         | _ => false)

(* Data the tactic layer derives from the registry and from the
   [arith_split] table is built once per state of them rather than once
   per call, so the failure to watch for is a stale rule that silently
   does not fire.  The two tests below assert the transitions: each
   state decides the very next tactic call, with no call in between to
   warm anything. *)
fun num_instance_with nnf_rules pre_split =
  {ty = #ty num_instance,
   discrete = #discrete num_instance,
   dest = #dest num_instance,
   kit = #kit num_instance,
   norm_conv = #norm_conv num_instance,
   nnf_rules = nnf_rules,
   pre_split = pre_split,
   atom_facts = #atom_facts num_instance} :
     linarithData.linarith_instance

fun with_num_instances stages =
  let
    fun restore () = linarithData.register_instance num_instance
    fun run [] = true
      | run ((instance, assertion) :: rest) =
          (linarithData.register_instance instance;
           assertion () andalso run rest)
    val result = run stages handle e => (restore (); raise e)
    val _ = restore ()
  in
    result
  end

(* A tactic that raises has not closed the goal, and reporting that as
   a failed assertion rather than an escaping exception keeps a stale
   rule legible as the test that noticed it. *)
fun linarith_closes tm =
  valid_closes (linarithLib.LINARITH_TAC []) ([], tm)
  handle Feedback.HOL_ERR _ => false

fun linarith_fails tm =
  tactic_fails (linarithLib.LINARITH_TAC []) ([], tm)

(* Only nnf_rules closes this one once pre_split is empty: with the
   split seeds gone, x - y is an atom the search knows nothing about. *)
val subtraction_implication =
  boolSyntax.mk_imp (subtraction_zero, public_x_le_y)

val bare_num_instance = num_instance_with [] []

val nnf_only_num_instance =
  num_instance_with (#nnf_rules num_instance) []

val _ =
  check
    ("a fresh registration decides the very next tactic call",
     fn () =>
       with_num_instances
         [(bare_num_instance,
           fn () =>
             linarith_fails subtraction_implication andalso
             linarith_fails min_le_left),
          (nnf_only_num_instance,
           fn () =>
             linarith_closes subtraction_implication andalso
             linarith_fails min_le_left)] andalso
       linarith_closes min_le_left)

fun with_split_export theorem operation =
  case ThmSetData.data_exportfns {settype = "arith_split"} of
      NONE => false
    | SOME export =>
        let
          val name = {Thy = "linarithSeed", Name = "NUM_MIN_SPLIT"}
          fun remove () =
            #remove export
              {thy = "linarithSeed",
               remove = "linarithSeed$NUM_MIN_SPLIT"}
          val _ = #add export
            {thy = "linarithSeed", named_thm = (name, theorem)}
          val result = operation () handle e => (remove (); raise e)
          val _ = remove ()
        in
          result
        end

(* The [arith_split] table is the half no registration counter sees:
   AncestryData installs a whole table on an ancestry change without
   applying a delta, so what the split rules are keyed on is the
   table's key set. *)
val _ =
  check
    ("an [arith_split] change decides the very next tactic call",
     fn () =>
       with_num_instances
         [(nnf_only_num_instance,
           fn () =>
             linarith_fails min_le_left andalso
             with_split_export linarithSeedTheory.NUM_MIN_SPLIT
               (fn () => linarith_closes min_le_left) andalso
             linarith_fails min_le_left)] andalso
       null (linarithData.arith_split_thms ()) andalso
       Option.isSome (linarithData.instance_for numSyntax.num))

(* An atom fact in equivalence form is the shape that lets fact
   augmentation and disjunction elimination feed each other:
   normalization replaces the equivalence by its disjuncts, the
   elimination consumes those, and the atom is still an atom on the
   branch below, so nothing in the goal records that the fact has
   already been contributed.  A goal the arithmetic cannot refute is
   reported, never searched for ever. *)
fun num_instance_with_atom_facts atom_facts =
  {ty = #ty num_instance,
   discrete = #discrete num_instance,
   dest = #dest num_instance,
   kit = #kit num_instance,
   norm_conv = #norm_conv num_instance,
   nnf_rules = #nnf_rules num_instance,
   pre_split = #pre_split num_instance,
   atom_facts = atom_facts} :
     linarithData.linarith_instance

fun positivity_facts tm =
  if Term.is_var tm andalso
     linarithData.same_type (Term.type_of tm) numSyntax.num
  then [Thm.SPEC tm arithmeticTheory.NOT_ZERO_LT_ZERO]
  else []

val equivalence_fact_instance =
  num_instance_with_atom_facts positivity_facts

(* The message is part of the assertion: a search that only ran out of
   budget reports the limit, and a search that alternated for ever
   reports nothing at all. *)
fun reports_no_proof tm =
  ((ignore (linarithLib.LINARITH_TAC [] ([], tm)); false)
   handle Feedback.HOL_ERR error =>
     Feedback.message_of error = "linear arithmetic found no proof")

val _ =
  check
    ("an equivalence-shaped atom fact still reports no proof",
     fn () =>
       with_num_instances
         [(equivalence_fact_instance,
           fn () => reports_no_proof (num_less public_x num_three))])

(* A tactic value built before a change and applied after it.  The
   entry points read the registry and the two tables where they are
   applied, so the hoisted value decides the goal the same way the same
   expression written out at the call site would; reading them where
   the value was built answers with the state of an hour ago. *)
val _ =
  check
    ("a hoisted tactic value reads the [arith] table where applied",
     fn () =>
       let
         val hoisted_full = linarithLib.LINARITH_TAC []
         val hoisted_simple = linarithLib.SIMPLE_LINARITH_TAC []
         val hoisted_cfg =
           linarithLib.CFG_LINARITH_TAC linarithLib.default_config []
         fun closes tactic =
           valid_closes tactic ([], nonlinear_closed_goal)
           handle Feedback.HOL_ERR _ => false
       in
         not (closes hoisted_full) andalso
         with_arith_export
           (fn () =>
              closes hoisted_full andalso closes hoisted_simple andalso
              closes hoisted_cfg) andalso
         not (closes hoisted_full)
       end)

val _ =
  check
    ("a hoisted tactic value reads the registry where applied",
     fn () =>
       let
         val hoisted = linarithLib.LINARITH_TAC []
         fun closes tm =
           valid_closes hoisted ([], tm)
           handle Feedback.HOL_ERR _ => false
         fun fails tm = tactic_fails hoisted ([], tm)
       in
         with_num_instances
           [(bare_num_instance,
             fn () =>
               fails subtraction_implication andalso fails min_le_left),
            (nnf_only_num_instance,
             fn () =>
               closes subtraction_implication andalso
               fails min_le_left andalso
               with_split_export linarithSeedTheory.NUM_MIN_SPLIT
                 (fn () => closes min_le_left))] andalso
         closes min_le_left
       end)

(* The result cache records failures, so a registration that turns a
   failure into a proof has to reach it, and the library rather than
   the caller is what has to notice.  Discreteness is the registry-only
   half of the decision: the cached entries run the forward procedure,
   which does no operator splitting and reads no table, so a dense num
   instance decides this goal the other way. *)
val dense_num_instance =
  {ty = #ty num_instance,
   discrete = NONE,
   dest = #dest num_instance,
   kit = #kit num_instance,
   norm_conv = #norm_conv num_instance,
   nnf_rules = #nnf_rules num_instance,
   pre_split = #pre_split num_instance,
   atom_facts = #atom_facts num_instance} :
     linarithData.linarith_instance

val public_x_lt_y = num_less public_x public_y
val public_successor_le_y = num_leq (num_plus public_x num_one) public_y

val _ =
  check
    ("a registry change invalidates a cached failure",
     fn () =>
       let
         val _ = linarithLib.clear_linarith_caches ()
         fun decided () =
           (ignore
              (linarithLib.CACHED_LINARITH [Thm.ASSUME public_x_lt_y]
                 public_successor_le_y);
            true)
           handle Feedback.HOL_ERR _ => false
       in
         with_num_instances
           [(dense_num_instance, fn () => not (decided ())),
            (num_instance, fn () => decided ())]
       end)

(* Traverse offers the solver every side condition of every conditional
   rewrite, and one outside the cache guard is discharged only from a
   contradictory context -- the same question whatever the condition
   was.  So the answer is cached rather than re-derived per condition,
   which an instance counting the atoms the procedure asks it about can
   state without reading the cache. *)
val nonneg_calls = ref 0

val counting_num_instance =
  let
    val kit = #kit num_instance
    fun nonneg tm =
      (nonneg_calls := !nonneg_calls + 1; #nonneg kit tm)
  in
    {ty = #ty num_instance,
     discrete = #discrete num_instance,
     dest = #dest num_instance,
     kit =
       {add_mono = #add_mono kit,
        mult_mono = #mult_mono kit,
        not_less = #not_less kit,
        not_le = #not_le kit,
        neqE = #neqE kit,
        nonneg = nonneg},
     norm_conv = #norm_conv num_instance,
     nnf_rules = #nnf_rules num_instance,
     pre_split = #pre_split num_instance,
     atom_facts = #atom_facts num_instance} :
       linarithData.linarith_instance
  end

fun solver_discharges_public_p () =
  let
    val {solve, ...} = linarithLib.linarith_solver
  in
    Term.aconv
      (Thm.concl
        (solve
          {stack = [],
           context_thms = [Thm.ASSUME public_successor_bound],
           recurse = Conv.NO_CONV} public_p))
      public_p
  end

val _ =
  check
    ("a non-arithmetic side condition is decided once and then cached",
     fn () =>
       with_num_instances
         [(counting_num_instance,
           fn () =>
             let
               val _ = linarithLib.clear_linarith_caches ()
               val _ = nonneg_calls := 0
               val first = solver_discharges_public_p ()
               val after_first = !nonneg_calls
               val repeats =
                 List.all (fn _ => solver_discharges_public_p ())
                   [1, 2, 3]
             in
               first andalso repeats andalso 0 < after_first andalso
               !nonneg_calls = after_first
             end)])

(* One decision asks for the same decompositions several times over: the
   result cache screens the goal, reads its atoms and those of every
   context theorem, and the procedure behind it screens the goal again.
   So a term is decomposed once and the answer remembered, which an
   instance counting the additions its destructor is asked to take apart
   states without reading the memo -- reaching the answer decomposes,
   and repeating the decision decomposes nothing further.  The count
   itself is not asserted: what is bounded is the growth, not the
   number of destructor calls one decision happens to make. *)
val plus_dest_calls = ref 0

val counting_dest_num_instance =
  let
    val dest = #dest num_instance
    fun dest_plus tm =
      (plus_dest_calls := !plus_dest_calls + 1; #dest_plus dest tm)
  in
    {ty = #ty num_instance,
     discrete = #discrete num_instance,
     dest =
       {dest_plus = dest_plus,
        dest_minus = #dest_minus dest,
        dest_neg = #dest_neg dest,
        dest_mult = #dest_mult dest,
        dest_div = #dest_div dest,
        dest_suc = #dest_suc dest,
        dest_lit = #dest_lit dest,
        mk_lit = #mk_lit dest,
        dest_less = #dest_less dest,
        dest_leq = #dest_leq dest},
     kit = #kit num_instance,
     norm_conv = #norm_conv num_instance,
     nnf_rules = #nnf_rules num_instance,
     pre_split = #pre_split num_instance,
     atom_facts = #atom_facts num_instance} :
       linarithData.linarith_instance
  end

val _ =
  check
    ("a repeated decision decomposes nothing further",
     fn () =>
       with_num_instances
         [(counting_dest_num_instance,
           fn () =>
             let
               val _ = linarithLib.clear_linarith_caches ()
               fun decided () =
                 (ignore
                    (linarithLib.CACHED_LINARITH
                       [Thm.ASSUME public_x_lt_y] public_successor_le_y);
                  true)
                 handle Feedback.HOL_ERR _ => false
               val _ = plus_dest_calls := 0
               val first = decided ()
               val after_first = !plus_dest_calls
               val repeats = List.all (fn _ => decided ()) [1, 2, 3]
             in
               first andalso repeats andalso 0 < after_first andalso
               !plus_dest_calls = after_first
             end)])

(* The 34 num/bool goals among the 54 lemma goals in Isabelle's
   Arith_Examples.thy at f7e02b7e1f31, which linarithCorpus states along
   with the driver, the budgets and the canonical numbering.  The
   instances suite runs all 54 and checks that vendored total; running
   the core partition here is what puts the strength corpus where the
   num instance is built, and the numbering check below pins the list to
   the core subset of the numbering.

   On 2026-08-02 the full core selftest took 13.2s at level 2 versus
   12.2s at level 1 on an AMD Ryzen 9 9950X.  The 90s suite budget,
   30s goal budget, and 5s boundary budget leave ample headroom. *)

val _ =
  check_numbering
    {suite = "Arith_Examples core", numbering = core_numbering}
    core_arith_examples

val _ =
  if selftest_level () >= 2 then
    run_suite
      {suite = "Arith_Examples core",
       tactic = fn () => linarithLib.LINARITH_TAC [],
       suite_budget = Time.fromSeconds 90,
       expected_successes = 33,
       expected_boundaries = 1}
      core_arith_examples
  else ()
