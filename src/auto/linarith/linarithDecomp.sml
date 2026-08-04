structure linarithDecomp :> linarithDecomp =
struct

open HolKernel

type polynomial = (term * Arbrat.rat) list * Arbrat.rat

val rat_zero = Arbrat.zero
val rat_one = Arbrat.one

val same_type = linarithData.same_type

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

(* An injection may be stripped only from an argument built out of the
   operators it distributes over -- sums, products, successors and
   literals.  A successor qualifies because it is the sum SUC k = k + 1,
   which is also how poly_other reads it, so an injection with an add
   homomorphism carries it too.  Every other operator of the source
   carrier keeps the injection, and the injected term stays an atom: num
   subtraction is the standard reason, since &(m - n) is not &m - &n. *)
fun supported source tm =
  let
    val dest = #dest source
    (* Read off the carrier's registration, and read off once for the
       whole traversal rather than per subterm. *)
    val compound = linarithData.compound_ops source
    fun keeps_injection tm =
      List.exists (fn recognises => recognises tm) compound
    fun ok tm =
      case Lib.total (#dest_plus dest) tm of
          SOME (left, right) => ok left andalso ok right
        | NONE =>
      case Lib.total (#dest_mult dest) tm of
          SOME (left, right) => ok left andalso ok right
        | NONE =>
      case Option.mapPartial (fn dest_suc => Lib.total dest_suc tm)
             (#dest_suc dest) of
          SOME argument => ok argument
        | NONE =>
          Option.isSome (Lib.total (#dest_lit dest) tm) orelse
          not (keeps_injection tm)
  in
    ok tm
  end

fun injection_arg tm =
  case Lib.total unary_parts tm of
      NONE => NONE
    | SOME (operator, arg) =>
        (case linarithData.injection_by_const operator of
             NONE => NONE
           | SOME injection =>
               if same_type (Term.type_of arg) (#from_ty injection) andalso
                  same_type (Term.type_of tm) (#to_ty injection)
               then
                 case linarithData.instance_for (#from_ty injection) of
                     SOME source =>
                       if supported source arg then SOME arg else NONE
                   | NONE => SOME arg
               else NONE)

(* Every destructor lookup is "find the term's carrier, then try that
   instance's operator"; the optional ones answer NONE for a carrier
   that has no such operator at all. *)
fun dest_mandatory select tm =
  case instance_of tm of
      NONE => NONE
    | SOME instance => Lib.total (select (#dest instance)) tm

fun dest_optional select tm =
  case instance_of tm of
      NONE => NONE
    | SOME instance =>
        (case select (#dest instance) of
             NONE => NONE
           | SOME dest => Lib.total dest tm)

fun dest_mult tm = dest_mandatory #dest_mult tm
fun dest_lit tm = dest_mandatory #dest_lit tm
fun dest_div tm = dest_optional #dest_div tm
fun dest_neg tm = dest_optional #dest_neg tm
fun dest_suc tm = dest_optional #dest_suc tm

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

fun decompose tm =
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
                         discrete = Option.isSome (#discrete instance),
                         negated = negated'})
                 end)
  end

(* Decomposing a term is a pure function of it and of the instance and
   injection registries, and one decision asks for the same terms
   several times over.  The result cache in linarithLib alone asks
   is_relevant of the goal, then the atoms of the goal and of every
   context theorem's conclusion -- twice, once to split the context into
   connected components and once to attach each theorem to its own --
   and the procedure behind it asks is_relevant once more.  So the
   answers are remembered, keyed on the registry generation the lookups
   inside them read, exactly as the registry's own derivations are.

   The table is bounded, because this sits under the simplifier and is
   offered every boolean subterm of every simplification: an unbounded
   one would grow with the length of the session rather than with the
   work in hand.  What it exists to hold is one decision's working set
   -- a goal, its context theorems, and the subterms of both -- and
   enough neighbouring decisions that a simplifier pass over a goal
   finds its own earlier answers, which a capacity in the thousands is
   generously above either way.  Overflow discards the table rather than
   evicting an entry: it is the same recovery as a registry change, it
   costs no per-entry bookkeeping on the path that matters, and a
   working set this far below the capacity reaches it rarely enough that
   which entry is dropped cannot be worth deciding. *)
val memo_capacity = 2000

val decomp_memo =
  ref (0, Termtab.empty : linarithSolve.decomp option Termtab.table)

fun decomp tm =
  let
    val current = linarithData.generation ()
    val (recorded, remembered) = !decomp_memo
    val table = if recorded = current then remembered else Termtab.empty
  in
    case Termtab.lookup table tm of
        SOME answer => answer
      | NONE =>
          let
            val answer = decompose tm
            val kept =
              if Termtab.size table < memo_capacity then table
              else Termtab.empty
          in
            decomp_memo := (current, Termtab.update (tm, answer) kept);
            answer
          end
  end

fun is_nonnegative tm =
  case linarithData.instance_for (Term.type_of tm) of
      NONE => false
    | SOME instance =>
        Option.isSome (#nonneg (#kit instance) tm)

fun is_relevant tm = Option.isSome (decomp tm)

end
