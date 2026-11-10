structure SmtLib_GraphScalarPreprocessPublic :> SmtLib_GraphScalarPreprocessPublic =
struct
  open SmtReplayGraph SmtReplayCanonGraph SmtReplayImport SmtLib
  structure G = SmtReplayGraph
  structure C = SmtReplayCanonGraph
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphScalarPreprocessPublic"
  datatype stage = NumAlgebra | Polymorphic | RealDivision | Reflexivity
    | PositiveLiteralPower | NumeralPower
  val stages = [NumAlgebra,PositiveLiteralPower,Polymorphic,NumeralPower,
                RealDivision,Reflexivity]
  fun name NumAlgebra = "num-algebra"
    | name Polymorphic = "polymorphic-simp"
    | name RealDivision = "real-div-simp"
    | name Reflexivity = "refl-simp"
    | name PositiveLiteralPower = "real-pow-positive-literal"
    | name NumeralPower = "real-pow-numeral"
  val real_pow_three =
  let
    val _ = List.app (fn theorem =>
      case SmtReplayImport.bounded_raw_size 8192 (Thm.concl theorem) of
        SOME _ => () | NONE => raise ERR "fixed_power_law"
          "expanded closed real-power derivation source")
      [realTheory.pow,realTheory.POW_2,realTheory.REAL_MUL_ASSOC]
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
  fun numeral_power tm =
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
    val rhs_th = Conv.DEPTH_CONV numeral_power rhs
      handle Conv.UNCHANGED => Thm.REFL rhs
  in
    Thm.TRANS th rhs_th
  end

  fun laws NumAlgebra =
        [HolSmtTheory.num_sub_assoc,HolSmtTheory.num_floor_zero,
         HolSmtTheory.num_ceiling_zero,arithmeticTheory.MAX_0,
         arithmeticTheory.MIN_0,boolTheory.REFL_CLAUSE]
    | laws Polymorphic =
        [pairTheory.PAIR_EQ,pairTheory.FST,pairTheory.SND,
         combinTheory.UPDATE_APPLY1,combinTheory.APPLY_UPDATE_THM,
         combinTheory.UPDATE_EQ,boolTheory.REFL_CLAUSE,
         HolSmtTheory.ALL_DISTINCT_NIL,HolSmtTheory.ALL_DISTINCT_CONS,
         listTheory.MEM,realTheory.POW_1,realTheory.POW_2,real_pow_three,
         realTheory.pow,
         integerTheory.INT_MAX,integerTheory.INT_MIN,
         HolSmtTheory.real_div_smt_rdiv,HolSmtTheory.smt_rdiv_zero]
    | laws RealDivision =
        [HolSmtTheory.smt_rdiv_zero,HolSmtTheory.smt_rdiv_refl,
         HolSmtTheory.smt_rdiv_one,HolSmtTheory.smt_rdiv_neg_refl,
         HolSmtTheory.smt_rdiv_neg_one]
    | laws Reflexivity = [boolTheory.REFL_CLAUSE]
    | laws PositiveLiteralPower =
        [realTheory.REAL_POW_LT,intrealTheory.real_of_int_num,
         intrealTheory.real_of_int_lt]
    | laws NumeralPower = [realTheory.pow]
  fun positive_literal term =
    let
      val _ = if realSyntax.is_less term then () else raise Conv.UNCHANGED
      val (zero,power) = realSyntax.dest_less term
      val _ = if realSyntax.is_pow power then () else raise Conv.UNCHANGED
      val (base,exponent) = realSyntax.dest_pow power
      val _ = if realSyntax.is_real_literal zero andalso
          realSyntax.is_real_literal base andalso
          realSyntax.int_of_term zero = Arbint.zero andalso
          Arbint.< (Arbint.zero,realSyntax.int_of_term base) then () else
        raise Conv.UNCHANGED
      val positive = Tactical.TAC_PROOF
        (([],realSyntax.mk_less (zero,base)),
         Tactical.THEN
           (simpLib.SIMP_TAC pureSimps.pure_ss
             [Conv.GSYM intrealTheory.real_of_int_num,
              intrealTheory.real_of_int_lt],intLib.ARITH_TAC))
      val proof = Thm.MP
        (Thm.SPEC exponent (Thm.SPEC base realTheory.REAL_POW_LT)) positive
    in Drule.EQT_INTRO proof end
  fun conversion NumAlgebra =
        simpLib.SIMP_CONV pureSimps.pure_ss (laws NumAlgebra)
    | conversion Polymorphic =
        simpLib.SIMP_CONV pureSimps.pure_ss (laws Polymorphic)
    | conversion RealDivision =
        simpLib.SIMP_CONV realSimps.real_ss (laws RealDivision)
    | conversion Reflexivity =
        simpLib.SIMP_CONV pureSimps.pure_ss (laws Reflexivity)
    | conversion PositiveLiteralPower = positive_literal
    | conversion NumeralPower = numeral_power
  fun propose graph scope stage {template_limit,prefix_depth,check_type} =
    let
      val _ = G.validate_scope graph scope
      val _ = if template_limit > 0 andalso prefix_depth >= 0 then () else
        raise ERR "propose" "invalid scalar prefix contract"
      fun bounded terms = List.app (fn term =>
        case SmtReplayImport.bounded_raw_size template_limit term of
          SOME _ => () | NONE => raise ERR "propose"
            "scalar schema exceeds template contract") terms
      fun types [] = ()
        | types (term :: pending) =
            (check_type (Term.type_of term);
             if Term.is_comb term then
               let val (head,arg) = Term.dest_comb term in
                 types (head :: arg :: pending) end
             else if Term.is_abs term then
               let val (variable,body) = Term.dest_abs term in
                 types (variable :: body :: pending) end
             else types pending)
      val theorems = laws stage
      val fixed = List.map Thm.concl theorems
      (* Every whole fixed law precedes type traversal and construction of
         the simplifier. No actual operand enters these small schemas. *)
      val _ = bounded fixed
      val _ = types fixed
      val convert = conversion stage
      fun preflight_power term = if stage <> NumeralPower then () else
        let
          val _ = if realSyntax.is_pow term then () else raise Conv.UNCHANGED
          val (base,exponent) = realSyntax.dest_pow term
          val _ = if numSyntax.is_numeral exponent then () else
            raise Conv.UNCHANGED
          val source_size = valOf
            (SmtReplayImport.bounded_raw_size template_limit term)
          val base_size = valOf
            (SmtReplayImport.bounded_raw_size template_limit base)
          val available = template_limit-source_size-6
          val maximum = Int.max (0,available div (base_size+3))
          (* The existing conversion expands numeral powers linearly. Admit
             its entire prospective equality before calling that recursion.
             Larger prefixes need a separate compact power continuation. *)
          val _ = if Arbnum.compare (numSyntax.dest_numeral exponent,
              Arbnum.fromInt maximum) <> GREATER then () else
            raise Conv.UNCHANGED
        in () end
      fun checked term =
        let val _ = bounded [term]
            val _ = preflight_power term
            val _ = types [term]
            val theorem = convert term
            val actual = Thm.concl theorem :: Thm.hyp theorem
            val _ = bounded actual
            val _ = types actual
        in theorem end
      fun build node =
        let val _ = G.validate_scope graph scope
            val _ = if G.scope_visible graph scope
                (G.node_scope graph node) then () else
              raise ERR "propose" "scalar node escapes scope"
        in case C.graph_schema_conversion graph scope
            {conversion = checked,template_limit = template_limit,
             prefix_depth = prefix_depth} node of NONE => NONE
          | SOME schema =>
              if C.graph_schema_source schema = node then SOME schema else
                raise ERR "propose" "scalar source endpoint differs"
        end
    in build end
end
