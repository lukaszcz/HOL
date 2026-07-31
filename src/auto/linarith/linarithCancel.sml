structure linarithCancel :> linarithCancel =
struct

open Abbrev HolKernel Conv Drule

val ERR = mk_HOL_ERR "linarithCancel"

type ac_ops = {
  dest_less : term -> term * term,
  dest_leq : term -> term * term,
  strip_plus : term -> term list,
  mk_plus : term * term -> term,
  zero : term,
  assoc : thm,
  comm : thm,
  rid : thm,
  ac_fallback : conv option
}

fun remove_aconv _ [] = NONE
  | remove_aconv tm (item :: rest) =
      if Term.aconv tm item then SOME rest
      else Option.map (fn rest' => item :: rest') (remove_aconv tm rest)

fun common_summand [] _ = NONE
  | common_summand (item :: rest) right =
      case remove_aconv item right of
          SOME right' => SOME (item, rest, right')
        | NONE =>
            Option.map
              (fn (common, left, right') =>
                  (common, item :: left, right'))
              (common_summand rest right)

fun mk_sum (ops : ac_ops) [] = #zero ops
  | mk_sum ops terms = list_mk_lbinop (curry (#mk_plus ops)) terms

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

end
