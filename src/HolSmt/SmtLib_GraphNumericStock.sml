(* Exact fixed legacy provider; no arbitrary theorem catalogue. *)
structure SmtLib_GraphNumericStock :> SmtLib_GraphNumericStock =
struct
  val exp_one_rewrites =
  let
    val th = Drule.SPEC_ALL arithmeticTheory.EXP_1
  in
    List.map Drule.GEN_ALL [Thm.CONJUNCT1 th, Thm.CONJUNCT2 th]
  end

  val INT_EXP_1 =
  let
    val i = Term.mk_var ("i", intSyntax.int_ty)
    val th =
      Thm.SPEC numSyntax.zero_tm
        (Thm.SPEC i (Thm.CONJUNCT2 integerTheory.int_exp))
  in
    Drule.GEN_ALL
      (simpLib.SIMP_RULE pureSimps.pure_ss
        [Thm.CONJUNCT1 integerTheory.int_exp, integerTheory.INT_MUL_RID,
         Conv.GSYM arithmeticTheory.ONE]
        th)
  end

  val INT_EXP_BASE_1 =
  let
    val n = Term.mk_var ("n", numSyntax.num)
    val one = numSyntax.mk_numeral Arbnum.one
    val th = Thm.SPEC n (Thm.SPEC one integerTheory.INT_EXP)
  in
    Drule.GEN_ALL
      (simpLib.SIMP_RULE pureSimps.pure_ss
        [List.hd exp_one_rewrites, integerTheory.INT] th)
  end

  val INT_EXP_2 =
  let
    val i = Term.mk_var ("i", intSyntax.int_ty)
    val one = numSyntax.mk_numeral Arbnum.one
    val th =
      Thm.SPEC one (Thm.SPEC i (Thm.CONJUNCT2 integerTheory.int_exp))
  in
    Drule.GEN_ALL
      (simpLib.SIMP_RULE pureSimps.pure_ss
         [INT_EXP_1, Conv.GSYM arithmeticTheory.TWO] th)
  end

  val INT_EXP_3 =
  let
    val i = Term.mk_var ("i", intSyntax.int_ty)
    val two = numSyntax.mk_numeral (Arbnum.fromInt 2)
    val th =
      numLib.REDUCE_RULE
        (Thm.SPEC two (Thm.SPEC i (Thm.CONJUNCT2 integerTheory.int_exp)))
  in
    Drule.GEN_ALL
      (simpLib.SIMP_RULE pureSimps.pure_ss
        [INT_EXP_2, integerTheory.INT_MUL_ASSOC] th)
  end

  val num_transfer_rewrites = [
    HolSmtTheory.int_num_floor_total,
    HolSmtTheory.int_num_ceiling_total,
    HolSmtTheory.num_floor_to_int_eq,
    HolSmtTheory.num_ceiling_to_int_eq,
    HolSmtTheory.num_floor_nonpos,
    HolSmtTheory.num_sub_assoc,
    integerTheory.NUM_OF_INT,
    integerTheory.Num_EQ_ABS,
    integerTheory.INT_ABS,
    (* Prefer the guarded cancellation when a transferred natural has its
       standard non-negativity hypothesis; Num_EQ_ABS remains the total
       fallback for genuinely unguarded integer-to-natural conversions. *)
    HolSmtTheory.NUM_TO_INT_GUARDED,
    intrealTheory.INT_NUM_FLOOR,
    intrealTheory.INT_NUM_CEILING,
    realTheory.NUM_CEILING_BASE,
    (* Eliminate symbolic natural exponents whenever their real base makes
       the result independent of the exponent or establishes its sign. *)
    realTheory.POW_ONE,
    realTheory.REAL_POW_LT,
    (* These definitions can be introduced by ADD_THEOREMS_TAC after the
       first transfer pass.  Keep the final pass in the SMT-LIB fragment
       rather than serializing their quantified HOL definitions. *)
    integerTheory.INT_MAX,
    integerTheory.INT_MIN,
    HolSmtTheory.real_div_smt_rdiv,
    integerTheory.INT_POS,
    Conv.GSYM integerTheory.INT_INJ,
    Conv.GSYM integerTheory.INT_LE,
    Conv.GSYM integerTheory.INT_LT,
    Conv.GSYM integerTheory.INT_ADD,
    Conv.GSYM integerTheory.INT_MUL
  ] @ exp_one_rewrites @
    (* These equations only match syntactic numerals.  Keeping both base and
       step equations lets SIMP unfold every literal exponent, rather than
       the historical 1/2/3 subset, while leaving symbolic exponents alone. *)
    [Thm.CONJUNCT1 arithmeticTheory.EXP,
     Thm.CONJUNCT2 arithmeticTheory.EXP,
     Thm.CONJUNCT1 integerTheory.int_exp,
     Thm.CONJUNCT2 integerTheory.int_exp] @ [
    arithmeticTheory.ZERO_LT_EXP,
    Conv.GSYM integerTheory.INT_EXP,
    INT_EXP_1,
    INT_EXP_BASE_1,
    INT_EXP_2,
    INT_EXP_3,
    integerTheory.INT,
    int_arithTheory.INT_NUM_SUB,
    HolSmtTheory.INT_NUM_EDIV,
    HolSmtTheory.INT_NUM_EMOD,
    Conv.GSYM int_arithTheory.INT_NUM_DIVIDES,
    int_arithTheory.INT_NUM_COND,
    arithmeticTheory.GREATER_DEF,
    arithmeticTheory.GREATER_EQ,
    (* Rewrite inequalities against MAX before num-to-int transfer.  This
       keeps tautological bounds such as [y <= MAX x y] out of the much more
       expensive integer/absolute-value encoding. *)
    Thm.CONJUNCT1 (Drule.SPEC_ALL arithmeticTheory.MAX_LE),
    arithmeticTheory.MAX_DEF,
    arithmeticTheory.MIN_DEF,
    Drule.GEN_ALL (Thm.SYM intrealTheory.real_of_int_num)
  ]

  local
    structure A = arithmeticTheory
    structure I = integerTheory
    structure IR = intrealTheory
    structure R = realTheory
    structure RA = realaxTheory
  in
    fun thms_per_const preserve_num const =
    let
      val { Thy, Name, Ty } = Term.dest_thy_const const
      val bool = Type.bool
      val num = numSyntax.num
      val op--> = Type.-->
      infixr 3 -->
    in
      (* NOTE: when adding a theorem to the list below, make sure that it
         doesn't have any free var -- otherwise, ASSUME_TAC will specialize
         the theorem to any free var in the goal that happens to have the same
         name, which very often is not what is desired. As an example,
         integerTheory's `INT_POW` should not be added -- instead, add
         `int_exp`. If no appropriate quantified theorem is available,
         `Drule.GEN_ALL` can be used to quantify all free vars in a theorem.

         Also, make sure the theorem is really needed -- some theorems seem to
         cause an explosion in the time needed to solve some goals, often
         making Z3 unable to solve them -- and it's not always easy to tell a
         priori which ones do. As an example, arithmeticTheory.EXP_1 doesn't
         seem to cause issues, but EXP_2 prevents Z3 from solving
         ``x DIV 42 <= x``. *)
      case (Thy, Name) of
        ("arithmetic", "*") =>
          if preserve_num then [I.NUM_INT_MUL] else []
      | ("arithmetic", "+") => if preserve_num then [I.INT_ADD] else []
      | ("arithmetic", "-") =>
          if preserve_num then [int_arithTheory.INT_NUM_SUB] else []
      | ("arithmetic", "<=") => if preserve_num then [I.INT_LE] else []
      | ("arithmetic", ">") => if preserve_num then [A.GREATER_DEF] else []
      | ("arithmetic", ">=") => if preserve_num then [A.GREATER_EQ] else []
      | ("arithmetic", "DIV") =>
          if preserve_num then [I.NUM_INT_EDIV] else []
      | ("arithmetic", "EXP") =>
          if preserve_num then [A.EXP, A.EXP_1, A.EXP_POS] else []
      | ("arithmetic", "MAX") => if preserve_num then [A.MAX_DEF] else []
      | ("arithmetic", "MIN") => if preserve_num then [A.MIN_DEF] else []
      | ("arithmetic", "MOD") =>
          if preserve_num then [I.NUM_INT_EMOD] else []
      | ("integer", "Num") =>
          if preserve_num then [I.INT_OF_NUM, I.NUM_OF_INT] else []
      | ("integer", "int_div") => [ I.INT_DIV_EDIV ]
      | ("integer", "int_exp") => [ I.int_exp ]
      | ("integer", "int_max") => [ I.INT_MAX ]
      | ("integer", "int_min") => [ I.INT_MIN ]
      | ("integer", "int_mod") => [ I.INT_MOD_EMOD ]
      | ("integer", "int_of_num") =>
          if preserve_num then [I.INT_OF_NUM, I.INT_POS, I.NUM_OF_INT]
          else []
      | ("integer", "int_quot") => [ I.INT_QUOT_EDIV ]
      | ("integer", "int_rem") => [ I.INT_REM_EMOD ]
      | ("intreal", "INT_CEILING") => []
      | ("marker", "Abbrev") => [ markerTheory.Abbrev_def ]
      | ("min", "=") =>
          if preserve_num andalso
             Type.compare (Ty, num --> num --> bool) = EQUAL then
            [I.INT_INJ]
          else
            []
      | ("num", "SUC") => if preserve_num then [I.INT] else []
      | ("prim_rec", "<") => if preserve_num then [I.INT_LT] else []
      | ("realax", "/") => [ HolSmtTheory.real_div_smt_rdiv ]
      | ("realax", "NUM_CEILING") => [ IR.INT_NUM_CEILING, R.NUM_CEILING_BASE ]
      | ("realax", "NUM_FLOOR") => [ IR.INT_NUM_FLOOR, R.NUM_FLOOR_BASE ]
      | ("realax", "abs") => [ R.abs ]
      | ("realax", "inv") => [ R.REAL_INV_1OVER ]
      | ("realax", "max") => [ RA.real_max ]
      | ("realax", "min") => [ RA.real_min ]
      | ("realax", "pow") => [ R.POW_2, R.POW_ONE, R.REAL_POW_LT, RA.real_pow ]
      | ("realax", "real_of_num") =>
          [ Drule.GEN_ALL (Thm.SYM IR.real_of_int_num) ]
      | _ => []
    end
  end

  val rewrites = num_transfer_rewrites
  val for_head_preserving_num = thms_per_const
  val for_head = thms_per_const false
  (* Opaque exact selector occurrence. This is no Source/Work receipt;
     admission, policy and construction remain the consuming owner's work. *)
  datatype selection = Selection of
    {head : Term.term,laws : Thm.thm list,types : int,symbols : int}
  fun select head =
    let val types = Type.type_epoch () val symbols = Term.term_epoch ()
        val laws = for_head head
        val _ = if Type.type_epoch () = types andalso
            Term.term_epoch () = symbols then () else
          raise Feedback.mk_HOL_ERR "SmtLib_GraphNumericStock" "select"
            "declaration retirement during stock selection"
    in Selection {head = head,laws = laws,types = types,symbols = symbols} end
  fun selection_data (Selection {head,laws,types,symbols}) =
    if Type.type_epoch () = types andalso Term.term_epoch () = symbols
    then {head = head,laws = laws} else
      raise Feedback.mk_HOL_ERR "SmtLib_GraphNumericStock" "selection_data"
        "selected declaration epoch retired"
  val _=SmtReplayNativeContract.for_work
  val _=SmtReplayInvocationWork.spend_policy
  structure StockPolicyWork=SmtReplayInvocationWork
  structure StockPolicyContract=SmtReplayNativeContract
  (* Only one old selector arm constructs a theorem at invocation time.
     Admit that exact fixed auxiliary programme before entering old for_head.
     Other arms borrow existing fixed laws. The dead equality arm returns []
     directly rather than construct a Type to return [] on both branches. *)
  fun select_with_policy work native head=
    let
      val data=StockPolicyContract.for_work work native
      val symbols=Term.term_epoch()val types=Type.type_epoch()
      fun guard()=
        (StockPolicyContract.validate_for work native;
         if symbols=Term.term_epoch()andalso types=Type.type_epoch()then ()
         else raise Feedback.mk_HOL_ERR "SmtLib_GraphNumericStock"
           "select_with_policy" "declaration retired during selection")
      fun spend n=(guard();StockPolicyWork.spend_policy work n;guard())
      fun invoke action=(guard();let val value=action()in guard();value end)
      val {Thy,Name,...}=invoke(fn()=>Term.dest_thy_const head)
      fun admit_constructed()=
        let
          val cap=IntInf.fromInt(#template_limit(#semantic_limits data))
          val ceiling=IntInf.fromInt(#type_work_limit data)
          fun bounded n=if n<=ceiling then n else
            raise Feedback.mk_HOL_ERR "SmtLib_GraphNumericStock"
              "select_with_policy" "fixed selector Type work exceeds native"
          fun tyweight ty=
            (spend 1;
             if Type.is_vartype ty then
               (spend(IntInf.fromInt(String.size(Type.dest_vartype ty)));1)
             else let val {Thy,Tyop,Args}=Type.dest_thy_type ty
                      val _=spend(IntInf.fromInt
                        (String.size Thy+String.size Tyop))
                  in List.foldl(fn(child,total)=>
                    bounded(total+tyweight child))1 Args end)
          fun shape current=
            let val _=spend 1 val ty=Term.type_of current
                val own=tyweight ty
                val value=if Term.is_comb current then
                    let val(f,x)=Term.dest_comb current
                        val(a,b,c)=shape f val(d,e,h)=shape x
                    in(1+a+d,1+b+e,bounded(own+c+h))end
                  else if Term.is_abs current then
                    let val(domain,_)=Type.dom_rng ty
                        val binder=tyweight domain
                        val(a,b,c)=shape(invoke(fn()=>
                          #2(Term.dest_abs current)))
                    in(1+a,2+b,bounded(own+binder+c))end
                  else(1,1,own)
                val(raw,inc,_)=value
            in if raw<=cap andalso inc<=cap then value else
              raise Feedback.mk_HOL_ERR "SmtLib_GraphNumericStock"
                "select_with_policy" "fixed selector exceeds native template"
            end
          val original=intrealTheory.real_of_int_num
          val _=if null(Thm.hyp original)then ()else
            raise Feedback.mk_HOL_ERR "SmtLib_GraphNumericStock"
              "select_with_policy" "fixed theorem gained hypotheses"
          val term=Thm.concl original
          val _=if IntInf.fromInt(Term.term_size term)<=cap then ()else
            raise Feedback.mk_HOL_ERR "SmtLib_GraphNumericStock"
              "select_with_policy" "fixed operand exceeds native template"
          val initial=shape term
          (* The fixed theorem is now admitted before the real FV operation.
             SYM preserves this shape. Each GEN adds forall/Abs/App plus the
             binder annotation. Monotonic forecasts admit each intermediate. *)
          val variables=invoke(fn()=>Term.FVL[term]Term.empty_tmset)
          fun quantify(variable,(raw,inc,ann,total))=
            let val domain=tyweight(Term.type_of variable)
                val next_ann=bounded(ann+3*domain+7)
                val next=(raw+3,inc+4,next_ann,bounded(total+next_ann))
                val(r,i,_,_)=next
            in if r<=cap andalso i<=cap then next else
              raise Feedback.mk_HOL_ERR "SmtLib_GraphNumericStock"
                "select_with_policy" "fixed GEN result exceeds template"
            end
          val(raw,inc,ann)=initial
          val(_,_,_,ann)=HOLset.foldl quantify
            (raw,inc,ann,bounded(2*ann))variables
          val _=if ann<=ceiling then ()else
            raise Feedback.mk_HOL_ERR "SmtLib_GraphNumericStock"
              "select_with_policy" "fixed GEN Type footprint exceeds native"
        in guard()end
      val _=if Thy="realax"andalso Name="real_of_num"then
          admit_constructed()else ()
      val laws=if Thy="min"andalso Name="="then []else
        invoke(fn()=>for_head head)
      val _=guard()
    in Selection{head=head,laws=laws,types=types,symbols=symbols}end
    handle primary=>(StockPolicyWork.close work;raise primary)
end
