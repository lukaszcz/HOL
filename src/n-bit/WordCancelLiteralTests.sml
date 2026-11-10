(* Copyright (c) 2026 The HOL4 contributors. *)
structure WordCancelLiteralTests =
struct
  open HolKernel testutils
  fun require message yes = if yes then () else raise Fail message
  fun negative term = Lib.can Drule.EQT_ELIM
    (wordsLib.WORD_EVAL_CONV (wordsSyntax.mk_word_msb term))
  fun minimum term = Lib.can Drule.EQT_ELIM (wordsLib.WORD_EVAL_CONV
    (boolSyntax.mk_eq (term,wordsSyntax.mk_word_L (wordsSyntax.dim_of term))))
  fun classify term = case WordCancelLiteral.classify term of
      NONE => raise Fail "bounded coefficient unexpectedly declined"
    | SOME info =>
        (require "coefficient sign differs from native evaluation"
           (#negative info = negative term);
         require "minimum coefficient differs from native evaluation"
           (#minimum info = minimum term))
  fun check_width width =
    let
      val dim = fcpSyntax.mk_int_numeric_type width
      val modulus = Arbnum.pow (Arbnum.two,Arbnum.fromInt width)
      val half = Arbnum.div2 modulus
      val numbers = [Arbnum.zero,Arbnum.one,Arbnum.two,
        Arbnum.- (half,Arbnum.one),half,Arbnum.+ (half,Arbnum.one),
        Arbnum.- (modulus,Arbnum.one),modulus,
        Arbnum.+ (modulus,Arbnum.one),
        Arbnum.+ (Arbnum.pow (Arbnum.two,Arbnum.fromInt (width+3)),
          Arbnum.fromInt 99)]
      val terms = List.map (fn number => wordsSyntax.mk_n2w
        (numSyntax.mk_numeral number,dim)) numbers
      val _ = List.app classify terms
      val _ = List.app (classify o wordsSyntax.mk_word_2comp) terms
    in List.app (fn left => List.app (fn right => classify
         (wordsSyntax.mk_word_sub (left,right))) terms) terms end
  fun declined term = require "optional coefficient domain widened"
    (not (Option.isSome (WordCancelLiteral.classify term)))
  fun cancellation ty =
    let
      val x = Term.mk_var ("literal_cancel_x",ty)
      val y = Term.mk_var ("literal_cancel_y",ty)
      val z = Term.mk_var ("literal_cancel_z",ty)
      val source = boolSyntax.mk_eq
        (wordsSyntax.mk_word_add (x,z),wordsSyntax.mk_word_add (y,z))
      val law = wordsLib.WORD_CANCEL_CONV source
      val _ = require "cancellation source changed"
        (Term.aconv source (boolSyntax.lhs (Thm.concl law)))
      val _ = require "cancellation retained hypotheses" (null (Thm.hyp law))
      val _ = let val (tags,_) = Tag.dest_tag (Thm.tag law)
          in require "cancellation acquired tags"
            (List.all (fn tag => tag="DISK_THM") tags andalso
             null (Tag.axioms_of (Thm.tag law))) end
      val dim = wordsSyntax.dest_word_type ty
      val one = wordsSyntax.mk_n2w (numLib.term_of_int 1,dim)
      val expected = if negative one then
          let val minus = wordsSyntax.mk_word_2comp one
          in boolSyntax.mk_eq
            (wordsSyntax.mk_word_add (x,wordsSyntax.mk_word_mul (minus,y)),
             wordsSyntax.mk_n2w (numLib.term_of_int 0,dim)) end
        else boolSyntax.mk_eq (x,y)
    in require ("cancellation normal form changed: " ^
         Parse.type_to_string ty ^ " actual=" ^
         Parse.term_to_string (boolSyntax.rhs (Thm.concl law)) ^
         " expected=" ^ Parse.term_to_string expected)
         (Term.aconv expected (boolSyntax.rhs (Thm.concl law))) end

  fun run () =
    let
      val _ = tprint "Literal coefficient signs match native word evaluation"
      val _ = List.app check_width (List.tabulate (32,fn n => n+1))
      val _ = OK ()
      val _ = tprint "Coefficient bounds and original cancellation fallbacks"
      fun literal dim = wordsSyntax.mk_n2w (numLib.term_of_int 9,dim)
      val _ = List.app (fn width => declined
        (literal (fcpSyntax.mk_int_numeric_type width))) [33,64,256]
      val ty = wordsSyntax.mk_int_word_type 8
      val _ = declined (Term.mk_var ("unknown_coefficient",ty))
      val _ = declined (literal Type.alpha)
      val _ = declined (literal Type.bool)
      val base = literal (fcpSyntax.mk_int_numeric_type 8)
      fun nested 0 term = term
        | nested n term = nested (n-1) (wordsSyntax.mk_word_2comp term)
      val _ = classify (nested 3 base)
      val _ = declined (nested 4 base)
      (* A small Type can encode a huge cardinality. Do not evaluate it. *)
      fun tower 0 = fcpSyntax.mk_int_numeric_type 2
        | tower n = Type.mk_type ("fun",[tower (n-1),
            fcpSyntax.mk_int_numeric_type 2])
      val _ = Timeout.apply (Time.fromSeconds 2)
        (fn () => declined (literal (tower 6))) ()
      val name = "bit0"
      val _ = Theory.new_type (name,1)
      val _ = Portable.finally (fn () => Theory.delete_type name)
        (fn () => declined (literal (Type.mk_thy_type
          {Thy=Theory.current_theory (),Tyop=name,
           Args=[fcpSyntax.mk_int_numeric_type 1]}))) ()
      val _ = List.app cancellation
        [wordsSyntax.mk_int_word_type 1,ty,
         wordsSyntax.mk_int_word_type 32,wordsSyntax.mk_int_word_type 33,
         wordsSyntax.mk_word_type Type.alpha]
    in OK () end
end
