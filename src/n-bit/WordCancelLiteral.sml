(* Copyright (c) 2026 The HOL4 contributors. *)

(* Coefficient routing only. No classification establishes a HOL equality;
   the caller still executes the ordinary checked cancellation laws. *)
structure WordCancelLiteral :> WordCancelLiteral =
struct
  type classification = {negative:bool,minimum:bool}
  exception Decline
  fun type_id n = #Tyop (Type.dest_thy_typeid
    (fcpSyntax.mk_int_numeric_type n))
  val one_id = type_id 1
  val even_id = type_id 2
  val odd_id = type_id 3
  fun small_type ty =
    let val remaining = ref 64
        fun visit ty = if !remaining = 0 then false else
          (remaining := !remaining - 1;
           Type.is_vartype ty orelse
             List.all visit (#Args (Type.dest_thy_typeid ty)))
    in visit ty andalso Type.uptodate_type ty end
  fun width ty =
    if Type.is_vartype ty then raise Decline else
    let val {Tyop,Args,...} = Type.dest_thy_typeid ty
        fun same held = KernelSig.id_compare (Tyop,held) = EQUAL
        fun child () = case Args of [arg] => width arg | _ => raise Decline
    in if same one_id andalso null Args then 1
       else if same even_id then
         let val n = child () in if n <= 16 then 2*n else raise Decline end
       else if same odd_id then
         let val n = child () in if n < 16 then 2*n+1 else raise Decline end
       else raise Decline
    end
  fun classify term =
    let
      val _ = if small_type (Term.type_of term) then () else raise Decline
      val dimension = case Lib.total wordsSyntax.dim_of term of
          SOME ty => ty | NONE => raise Decline
      val bits = width dimension
      val modulus = Arbnum.pow (Arbnum.two,Arbnum.fromInt bits)
      fun value 0 _ = raise Decline
        | value fuel input =
          case Lib.total wordsSyntax.dest_word_literal input of
            SOME number => Arbnum.mod (number,modulus)
          | NONE => (case Lib.total wordsSyntax.dest_word_2comp input of
              SOME operand => Arbnum.mod
                (Arbnum.- (modulus,value (fuel-1) operand),modulus)
            | NONE => (case Lib.total wordsSyntax.dest_word_sub input of
                SOME (left,right) => Arbnum.mod
                  (Arbnum.- (Arbnum.+ (modulus,value (fuel-1) left),
                    value (fuel-1) right),modulus)
              | NONE => raise Decline))
      val number = value 4 term
      val half = Arbnum.div2 modulus
    in SOME {negative=Arbnum.compare (number,half)<>LESS,
      minimum=number=half} end
    handle Decline => NONE
  (* Copy of wordsLib's WORD_CANCEL_CONV0, WORD_CANCEL_CONV and
     WORD_CANCEL_ss.  Only the two coefficient tests consult classify first;
     every theorem still comes from the original cancellation laws.  The
     wordsLib definitions themselves are not changed. *)
  local
    open Conv Lib
    val ERR = Feedback.mk_HOL_ERR "wordsLib"
    val is_known_word_size = not o Type.is_vartype o wordsSyntax.dim_of
    fun is_word_literal t =
      case Lib.total wordsSyntax.dest_word_2comp t of
         SOME n => wordsSyntax.is_word_literal n
       | NONE => wordsSyntax.is_word_literal t
    fun is_eq_word_L tm =
      let
        val ty = wordsSyntax.dim_of tm
        val tm = boolSyntax.mk_eq (tm, wordsSyntax.mk_word_L ty)
      in
        Lib.can Drule.EQT_ELIM (wordsLib.WORD_EVAL_CONV tm)
      end
    fun is_negative tm =
      Lib.can Drule.EQT_ELIM
        (wordsLib.WORD_EVAL_CONV (wordsSyntax.mk_word_msb tm))
    fun gen_dest_word_literal t =
      case Lib.total wordsSyntax.dest_word_2comp t of
         SOME n =>
           Arbint.negate (Arbint.fromNat (wordsSyntax.dest_word_literal n))
       | NONE => Arbint.fromNat (wordsSyntax.dest_word_literal t)
    fun gen_is_negative pick_word_l tm =
      if is_known_word_size tm then
        (case classify tm of
            SOME {negative,minimum} =>
              negative andalso (pick_word_l orelse not minimum)
          | NONE => is_negative tm andalso
              (pick_word_l orelse not (is_eq_word_L tm)))
      else Arbint.<= (gen_dest_word_literal tm, Arbint.fromInt ~1)
    fun is_zero tm =
      case Lib.total gen_dest_word_literal tm of
         SOME i => i = Arbint.zero
       | NONE => false
    fun pick_left_coeff x z =
      if is_known_word_size x
        then gen_is_negative false (wordsSyntax.mk_word_sub (x, z))
      else Arbint.< (gen_dest_word_literal x, gen_dest_word_literal z)
    fun partition_same t l = List.partition (fn (_, y) => Term.aconv y t) l
    fun pick_coeff_terms a =
      fn ([], l) => a @ List.filter (gen_is_negative true o fst) l
       | ((x, y) :: t, l) =>
         (case partition_same y l of
             ([], _) =>
               pick_coeff_terms
                 (if gen_is_negative false x then (x, y) :: a else a) (t, l)
           | ([(z, _)], r) =>
               pick_coeff_terms
                 ((if pick_left_coeff x z then x else z, y) :: a) (t, r)
           | _ => raise ERR "pick_coeff_terms" "")
    fun join_coeff_terms (z as (_, y)) l =
      if Lib.all (fn (_, x) => not (Term.aconv x y)) l then z::l
      else raise ERR "join_coeff_terms" ""
    fun mk_one tm =
      wordsSyntax.mk_n2w (numSyntax.mk_numeral Arbnum.one,
                          wordsSyntax.dim_of tm)
    fun get_coeff_terms a tm =
      case Lib.total boolSyntax.dest_strip_comb tm of
         SOME ("words$word_add", [l, r]) =>
           get_coeff_terms (get_coeff_terms a l) r
       | SOME ("words$word_mul", [l, r]) =>
           if is_zero l
             then raise ERR "get_coeff_terms" "zero"
           else if is_word_literal l
             then join_coeff_terms (l, r) a
           else join_coeff_terms (mk_one tm, tm) a
       | _ => if is_zero tm
                then raise ERR "get_coeff_terms" "zero"
              else if is_word_literal tm
                then join_coeff_terms (tm, mk_one tm) a
              else join_coeff_terms (mk_one tm, tm) a
    val lcancel_sub = Conv.GSYM wordsTheory.WORD_LCANCEL_SUB
    fun mk_cancel_thm x =
      let
        val p = wordsSyntax.mk_word_mul x
        val ty = Term.type_of p
        val fvs = Term.free_vars p
        val x = Term.variant fvs (Term.mk_var ("x", ty))
        val y = Term.variant fvs (Term.mk_var ("y", ty))
      in
        Drule.SPECL [x, p, y]
          (Thm.INST_TYPE
             [Lib.|-> (Type.alpha, wordsSyntax.dest_word_type ty)]
             lcancel_sub)
      end
    fun compare_coeff (x, y) =
      Term.compare (wordsSyntax.mk_word_mul x, wordsSyntax.mk_word_mul y)
    val is_lit_coeff = fn [r] => wordsSyntax.is_word_literal (snd r)
                        | _ => false
    fun is_word_L_lit tm = is_word_literal tm andalso
      (case classify tm of
          SOME {minimum,...} => minimum
        | NONE => is_eq_word_L tm)
    fun swap_sides l =
      fn [] => false
       | r =>
          not (is_lit_coeff r)
          andalso
            let
              val (xl, fl) = List.partition (is_word_L_lit o fst) l
            in
              if List.null xl
                then case Int.compare (List.length l, List.length r) of
                        EQUAL =>
                          Lib.list_compare compare_coeff (r, l) = GREATER
                      | LESS => true
                      | GREATER => false
              else case Int.compare
                          (List.length l, List.length xl + List.length r) of
                     EQUAL => Lib.list_compare compare_coeff (r, fl) = GREATER
                   | LESS => false
                   | GREATER => true
            end
    fun WORD_CANCEL_CONV0 tm =
      let
        val (l, r) = boolSyntax.dest_eq tm
        val _ = wordsSyntax.is_word_type (Term.type_of l)
                orelse raise ERR "WORD_CANCEL_CONV" "Is not a word equality"
        val _ = not (wordsSyntax.is_word_sub l)
                orelse raise ERR "WORD_CANCEL_CONV" "Is subtraction"
        val l = if is_zero l then [] else get_coeff_terms [] l
        val r = if is_zero r then [] else get_coeff_terms [] r
      in
        case pick_coeff_terms [] (l, r) of
           [] => if swap_sides l r
                   then Conv.REWR_CONV boolTheory.EQ_SYM_EQ tm
                 else raise ERR "WORD_CANCEL_CONV" "Nothing to cancel"
         | ps => (List.foldl
                    (fn (p, cnv) => cnv THENC Conv.REWR_CONV (mk_cancel_thm p))
                    Conv.ALL_CONV ps) tm
      end
    val WORD_MULT_RID =
      Lib.el 4 (Drule.CONJUNCTS (Drule.SPEC_ALL wordsTheory.WORD_MULT_CLAUSES))
    fun normsubs t =
      (REWR_CONV wordsTheory.word_sub_def THENC
       RAND_CONV (REWR_CONV wordsTheory.WORD_NEG_LMUL THENC
                  Rewrite.PURE_REWRITE_CONV
                    [WORD_MULT_RID, wordsTheory.WORD_NEG_NEG]) THENC
       TRY_CONV (LAND_CONV normsubs)) t
    val word_alpha = wordsSyntax.mk_word_type Type.alpha
  in
    val WORD_CANCEL_CONV =
      WORD_CANCEL_CONV0 THENC
      BINOP_CONV (TRY_CONV (normsubs THENC wordsLib.WORD_ADD_CANON_CONV))
    val WORD_CANCEL_ss =
      simpLib.named_merge_ss "word cancel"
        [simpLib.rewrites
           [wordsTheory.WORD_LEFT_ADD_DISTRIB,
            wordsTheory.WORD_RIGHT_ADD_DISTRIB, wordsTheory.WORD_NOT,
            hd (Drule.CONJUNCTS wordsTheory.SHIFT_ZERO)],
         simpLib.std_conv_ss
           {conv = WORD_CANCEL_CONV,
            name = "WORD_CANCEL_CONV",
            pats = [boolSyntax.mk_eq (Term.mk_var ("w", word_alpha),
                                      Term.mk_var ("y", word_alpha))]}]
  end
end
