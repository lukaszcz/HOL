structure linarithDecomp :> linarithDecomp =
struct

open Abbrev HolKernel

type polynomial = (term * Arbrat.rat) list * Arbrat.rat

val rat_zero = Arbrat.zero
val rat_one = Arbrat.one

fun same_type left right = Type.compare (left, right) = EQUAL

fun binary_parts tm =
  let
    val (rator, right) = Term.dest_comb tm
    val (operator, left) = Term.dest_comb rator
  in
    (operator, left, right)
  end

fun unary_parts tm = Term.dest_comb tm

fun mk_binary operator left right =
  Term.list_mk_comb (operator, [left, right])

fun instance_of tm = linarithData.instance_for (Term.type_of tm)

fun injection_arg tm =
  case Lib.total unary_parts tm of
      NONE => NONE
    | SOME (operator, arg) =>
        (case linarithData.injection_by_const operator of
             NONE => NONE
           | SOME injection =>
               let
                 fun supported source tm =
                   let
                     val dest = #dest source
                   in
                     case Lib.total (#dest_plus dest) tm of
                         SOME (left, right) =>
                           supported source left andalso
                           supported source right
                       | NONE =>
                           (case Lib.total (#dest_mult dest) tm of
                                SOME (left, right) =>
                                  supported source left andalso
                                  supported source right
                              | NONE =>
                                  Option.isSome
                                    (Lib.total (#dest_lit dest) tm) orelse
                                  not
                                    (Option.isSome
                                       (case #dest_minus dest of
                                            NONE => NONE
                                          | SOME f => Lib.total f tm) orelse
                                     Option.isSome
                                       (case #dest_neg dest of
                                            NONE => NONE
                                          | SOME f => Lib.total f tm) orelse
                                     Option.isSome
                                       (case #dest_div dest of
                                            NONE => NONE
                                          | SOME f => Lib.total f tm) orelse
                                     Option.isSome
                                       (case #dest_suc dest of
                                            NONE => NONE
                                          | SOME f => Lib.total f tm)))
                   end
               in
                 if same_type (Term.type_of arg) (#from_ty injection) andalso
                    same_type (Term.type_of tm) (#to_ty injection)
                 then
                   case linarithData.instance_for (#from_ty injection) of
                       SOME source =>
                         if supported source arg then SOME arg else NONE
                     | NONE => SOME arg
                 else NONE
               end)

fun dest_mult tm =
  case instance_of tm of
      NONE => NONE
    | SOME instance => Lib.total (#dest_mult (#dest instance)) tm

fun dest_div tm =
  case instance_of tm of
      NONE => NONE
    | SOME instance =>
        (case #dest_div (#dest instance) of
             NONE => NONE
           | SOME dest => Lib.total dest tm)

fun dest_neg tm =
  case instance_of tm of
      NONE => NONE
    | SOME instance =>
        (case #dest_neg (#dest instance) of
             NONE => NONE
           | SOME dest => Lib.total dest tm)

fun dest_lit tm =
  case instance_of tm of
      NONE => NONE
    | SOME instance => Lib.total (#dest_lit (#dest instance)) tm

fun dest_suc tm =
  case instance_of tm of
      NONE => NONE
    | SOME instance =>
        (case #dest_suc (#dest instance) of
             NONE => NONE
           | SOME dest => Lib.total dest tm)

fun try_product operator left right =
  Lib.total (fn () => mk_binary operator left right) ()

fun restore_factor_type original atom =
  let
    val original_ty = Term.type_of original
    val atom_ty = Term.type_of atom
  in
    if same_type original_ty atom_ty then SOME atom
    else
      case linarithData.injection_for atom_ty original_ty of
          NONE => NONE
        | SOME injection =>
            Lib.total (fn () => Term.mk_comb (#inj injection, atom)) ()
  end

(* Products are normalized to right-associated form while their literal
   factors are accumulated in the Arbrat multiplier. *)
fun demult (tm, multiplier) =
  case dest_mult tm of
      SOME (left, right) =>
        (case dest_mult left of
             SOME (left1, left2) =>
               let
                 val (operator, _, _) = binary_parts tm
               in
                 case try_product operator left2 right of
                     NONE => (SOME tm, multiplier)
                   | SOME nested =>
                       (case try_product operator left1 nested of
                            NONE => (SOME tm, multiplier)
                          | SOME rotated =>
                              demult (rotated, multiplier))
               end
           | NONE =>
               let
                 val (operator, _, _) = binary_parts tm
                 val (left_atom, multiplier') =
                   demult (left, multiplier)
               in
                 case left_atom of
                     SOME left' =>
                       let
                         val (right_atom, multiplier'') =
                           demult (right, multiplier')
                       in
                         case right_atom of
                             SOME right' =>
                               (case
                                  (restore_factor_type left left',
                                   restore_factor_type right right')
                                of
                                    (SOME left'', SOME right'') =>
                                      (case
                                         try_product operator left'' right''
                                       of
                                           SOME product =>
                                             (SOME product, multiplier'')
                                         | NONE => (SOME tm, multiplier))
                                  | _ => (SOME tm, multiplier))
                           | NONE => (SOME left', multiplier'')
                       end
                   | NONE => demult (right, multiplier')
               end)
    | NONE =>
        (case dest_div tm of
             SOME (numerator, denominator) =>
               (case demult (denominator, rat_one) of
                    (NONE, divisor) =>
                      if divisor = rat_zero then (SOME tm, multiplier)
                      else
                        let
                          val (atom, numerator_multiplier) =
                            demult (numerator, multiplier)
                        in
                          (atom,
                           Arbrat.*
                             (numerator_multiplier,
                              Arbrat.inv divisor))
                        end
                  | (SOME _, _) => (SOME tm, multiplier))
           | NONE =>
               (case dest_neg tm of
                    SOME arg =>
                      demult (arg, Arbrat.negate multiplier)
                  | NONE =>
                      (case dest_lit tm of
                           SOME literal =>
                             (NONE, Arbrat.* (multiplier, literal))
                         | NONE =>
                             (case injection_arg tm of
                                  SOME arg => demult (arg, multiplier)
                                | NONE => (SOME tm, multiplier)))))

fun add_atom atom coefficient (atoms, constant) =
  let
    fun add [] =
          if coefficient = rat_zero then [] else [(atom, coefficient)]
      | add ((item as (old_atom, old_coefficient)) :: rest) =
          if Term.aconv old_atom atom then
            let
              val coefficient' =
                Arbrat.+ (old_coefficient, coefficient)
            in
              if coefficient' = rat_zero then rest
              else (old_atom, coefficient') :: rest
            end
          else item :: add rest
  in
    (add atoms, constant)
  end

fun add_constant multiplier literal (atoms, constant) =
  (atoms, Arbrat.+ (constant, Arbrat.* (multiplier, literal)))

fun poly_acc (tm, multiplier, polynomial) =
  case instance_of tm of
      NONE =>
        (case injection_arg tm of
             SOME arg => poly_acc (arg, multiplier, polynomial)
           | NONE => add_atom tm multiplier polynomial)
    | SOME instance =>
        let
          val dest = #dest instance
        in
          case Lib.total (#dest_plus dest) tm of
              SOME (left, right) =>
                poly_acc
                  (left, multiplier,
                   poly_acc (right, multiplier, polynomial))
            | NONE =>
                (case #dest_minus dest of
                     SOME dest_minus =>
                       (case Lib.total dest_minus tm of
                            SOME (left, right) =>
                              poly_acc
                                (left, multiplier,
                                 poly_acc
                                   (right, Arbrat.negate multiplier,
                                    polynomial))
                          | NONE => poly_other (tm, multiplier, polynomial))
                   | NONE => poly_other (tm, multiplier, polynomial))
        end
and poly_other (tm, multiplier, polynomial) =
  case dest_suc tm of
      SOME arg =>
        poly_acc
          (arg, multiplier,
           add_constant multiplier rat_one polynomial)
    | NONE => poly_non_suc (tm, multiplier, polynomial)
and poly_non_suc (tm, multiplier, polynomial) =
  case dest_neg tm of
      SOME arg => poly_acc (arg, Arbrat.negate multiplier, polynomial)
    | NONE =>
        (case dest_lit tm of
             SOME literal => add_constant multiplier literal polynomial
           | NONE =>
               (case dest_mult tm of
                    SOME _ =>
                      let
                        val (atom, coefficient) = demult (tm, multiplier)
                      in
                        case atom of
                            SOME atom' =>
                              if Term.aconv atom' tm then
                                add_atom atom' coefficient polynomial
                              else
                                poly_acc (atom', coefficient, polynomial)
                          | NONE =>
                              add_constant rat_one coefficient polynomial
                      end
                  | NONE =>
                      (case dest_div tm of
                           SOME _ =>
                             let
                               val (atom, coefficient) =
                                 demult (tm, multiplier)
                             in
                               case atom of
                                   SOME atom' =>
                                     if Term.aconv atom' tm then
                                       add_atom atom' coefficient polynomial
                                     else
                                       poly_acc
                                         (atom', coefficient, polynomial)
                                 | NONE =>
                                     add_constant rat_one coefficient
                                       polynomial
                             end
                         | NONE =>
                             (case injection_arg tm of
                                  SOME arg =>
                                    poly_acc (arg, multiplier, polynomial)
                                | NONE =>
                                    add_atom tm multiplier polynomial))))

fun poly tm = poly_acc (tm, rat_one, ([], rat_zero))

fun relation tm =
  case Lib.total boolSyntax.dest_eq tm of
      SOME (left, right) => SOME (linarithSolve.REL_EQ, left, right)
    | NONE =>
        (case Lib.total binary_parts tm of
             NONE => NONE
           | SOME (_, left, _) =>
               (case linarithData.instance_for (Term.type_of left) of
                    NONE => NONE
                  | SOME instance =>
                      let
                        val dest = #dest instance
                      in
                        case Lib.total (#dest_less dest) tm of
                            SOME (lhs, rhs) =>
                              SOME (linarithSolve.REL_LT, lhs, rhs)
                          | NONE =>
                              (case Lib.total (#dest_leq dest) tm of
                                   SOME (lhs, rhs) =>
                                     SOME
                                       (linarithSolve.REL_LE, lhs, rhs)
                                 | NONE => NONE)
                      end))

fun decomp tm =
  let
    val (negated, body) =
      case Lib.total boolSyntax.dest_neg tm of
          SOME inner => (true, inner)
        | NONE => (false, tm)
  in
    case relation body of
        NONE => NONE
      | SOME (rel, lhs, rhs) =>
          (case linarithData.instance_for (Term.type_of lhs) of
               NONE => NONE
             | SOME instance =>
                 let
                   val (lhs_atoms, lhs_const) = poly lhs
                   val (rhs_atoms, rhs_const) = poly rhs
                   val (rel', negated') =
                     if rel = linarithSolve.REL_EQ andalso negated then
                       (linarithSolve.REL_NEQ, false)
                     else (rel, negated)
                 in
                   SOME
                     (linarithSolve.Decomp
                        {lhs = lhs_atoms, lhs_const = lhs_const,
                         rel = rel', rhs = rhs_atoms,
                         rhs_const = rhs_const,
                         discrete = #discrete instance,
                         negated = negated'})
                 end)
  end

fun is_nonnegative tm =
  case linarithData.instance_for (Term.type_of tm) of
      NONE => false
    | SOME instance =>
        Option.isSome (#nonneg (#kit instance) tm)

fun is_relevant tm = Option.isSome (decomp tm)

end
