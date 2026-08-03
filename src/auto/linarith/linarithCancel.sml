structure linarithCancel :> linarithCancel =
struct

open Abbrev HolKernel Conv Drule

val ERR = mk_HOL_ERR "linarithCancel"

type ac_ops = {
  dest_less : term -> term * term,
  dest_leq : term -> term * term,
  strip_plus : term -> term list,
  mk_plus : term * term -> term,
  assoc : thm,
  comm : thm,
  rid : thm,
  ac_fallback : conv option
}

type norm_spec = {
  ac : ac_ops,
  ty : hol_type,
  leq_cancel : thm,
  less_cancel : thm,
  eq_cancel : thm,
  expression_conv : conv,
  reduce_conv : conv,
  refl_thms : thm list
}

fun remove_aconv tm items =
  Option.map #2 (Lib.total (Lib.pluck (Term.aconv tm)) items)

fun common_summand [] _ = NONE
  | common_summand (item :: rest) right =
      case remove_aconv item right of
          SOME right' => SOME (item, rest, right')
        | NONE =>
            Option.map
              (fn (common, left, right') =>
                  (common, item :: left, right'))
              (common_summand rest right)

(* Only ever asked for the non-empty remainder of a cancellation; the
   emptied side is handled by the identity theorem instead. *)
fun mk_sum (ops : ac_ops) terms =
  list_mk_lbinop (curry (#mk_plus ops)) terms

fun relation_sides (ops : ac_ops) tm =
  case Lib.total (#dest_leq ops) tm of
      SOME sides => sides
    | NONE =>
        (case Lib.total (#dest_less ops) tm of
             SOME sides => sides
           | NONE => boolSyntax.dest_eq tm)

fun ac_equality (ops : ac_ops) left right =
  if Term.aconv left right then Thm.REFL left
  else
    let
      val equality = boolSyntax.mk_eq (left, right)
      fun fallback () =
        case #ac_fallback ops of
            NONE => raise ERR "ac_equality" "AC rearrangement failed"
          | SOME canon =>
              EQT_ELIM
                ((BINOP_CONV canon THENC
                  REWR_CONV boolTheory.EQ_REFL) equality)
    in
      EQT_ELIM (AC_CONV (#assoc ops, #comm ops) equality)
      handle HOL_ERR _ => fallback ()
    end

fun cancel_common (ops : ac_ops) cancel tm =
  let
    val operator = Term.rator (Term.rator tm)
    val (left, right) = relation_sides ops tm
    fun summands expression =
      case #strip_plus ops expression of
          [] => [expression]
        | terms => terms
  in
    case common_summand (summands left) (summands right) of
        NONE => raise UNCHANGED
      | SOME (_, [], []) => raise UNCHANGED
      | SOME (common, left', right') =>
          let
            (* An emptied side becomes common + 0 so that both sides share
               the cancellation theorem's shape. *)
            fun cancellation_side original [] =
                  Thm.TRANS (ac_equality ops original common)
                    (Thm.SYM (Thm.SPEC common (#rid ops)))
              | cancellation_side original rest =
                  ac_equality ops original
                    (#mk_plus ops (common, mk_sum ops rest))
            val relation_thm =
              Thm.MK_COMB
                (Thm.AP_TERM operator (cancellation_side left left'),
                 cancellation_side right right')
            val cancel_thm =
              REWR_CONV cancel
                (#2 (boolSyntax.dest_eq (Thm.concl relation_thm)))
          in
            Thm.TRANS relation_thm cancel_thm
          end
  end

fun mk_norm_conv (spec : norm_spec) =
  let
    val ops = #ac spec
    val expression_conv = #expression_conv spec
    fun cancel_rule tm =
      if Lib.can (#dest_leq ops) tm then SOME (#leq_cancel spec)
      else if Lib.can (#dest_less ops) tm then SOME (#less_cancel spec)
      else if boolSyntax.is_eq tm andalso
              Term.type_of (#1 (boolSyntax.dest_eq tm)) = #ty spec
      then SOME (#eq_cancel spec)
      else NONE
    val finish =
      TRY_CONV (#reduce_conv spec) THENC
      TRY_CONV (simpLib.SIMP_CONV boolSimps.bool_ss (#refl_thms spec))
  in
    fn tm =>
      case cancel_rule tm of
          NONE => expression_conv tm
        | SOME cancel =>
            (BINOP_CONV expression_conv THENC
             REPEATC (cancel_common ops cancel) THENC finish) tm
  end

end
