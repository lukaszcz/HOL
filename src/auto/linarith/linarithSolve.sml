structure linarithSolve :> linarithSolve =
struct

val ERR = Feedback.mk_HOL_ERR "linarithSolve"

(* Nonneg generalizes upstream Nat (fast_lin_arith.ML:191-202). *)
datatype lineq_type = Eq | Le | Lt

datatype injust =
    Asm of int
  | Nonneg of Term.term
  | LessD of injust
  | NotLessD of injust
  | NotLeD of injust
  | NotLeDD of injust
  | Multiplied of Arbint.int * injust
  | Added of injust * injust

datatype lineq =
  Lineq of Arbint.int * lineq_type * Arbint.int list * injust

type history = int list
datatype result = Success of injust | Failure of history

type linarith_config = linarithData.linarith_config

(* Relations and negation are structured rather than upstream strings
   (fast_lin_arith.ML:510-541). *)
datatype relation = REL_LE | REL_LT | REL_EQ | REL_NEQ

datatype decomp = Decomp of {
  lhs : (Term.term * Arbrat.rat) list,
  lhs_const : Arbrat.rat,
  rel : relation,
  rhs : (Term.term * Arbrat.rat) list,
  rhs_const : Arbrat.rat,
  discrete : bool,
  negated : bool
}

type int_decomp = {
  lhs : (Term.term * Arbint.int) list,
  lhs_const : Arbint.int,
  rel : relation,
  rhs : (Term.term * Arbint.int) list,
  rhs_const : Arbint.int,
  discrete : bool,
  negated : bool
}

val zero = Arbint.zero
val one = Arbint.one
val negone = Arbint.~ one

fun ai_eq x y = x = y
fun ai_zero x = ai_eq x zero
fun ai_one x = ai_eq x one
fun ai_neg x = Arbint.< (x, zero)
fun ai_pos x = Arbint.> (x, zero)

fun find_add_type (Eq, ty) = ty
  | find_add_type (ty, Eq) = ty
  | find_add_type (_, Lt) = Lt
  | find_add_type (Lt, _) = Lt
  | find_add_type (Le, Le) = Le

(* Scaling a row that is already scaled composes the two literals rather
   than nesting the justifications.  mklineq scales by a denominator LCM
   and elimination then scales that row again, so the nested form would
   reach replay as t * 2 * 3 and leave every instance's norm_conv obliged
   to recognize it as the t * 6 on the other side. *)
fun mk_multiplied n just =
  if ai_one n then just
  else
    case just of
        Multiplied (m, inner) => mk_multiplied (Arbint.* (n, m)) inner
      | _ => Multiplied (n, just)

fun multiply_ineq n (ineq as Lineq (k, ty, coeffs, just)) =
  if ai_one n then ineq
  else if ai_zero n andalso ty = Lt then
    raise ERR "multiply_ineq" "zero multiplier on a strict inequality"
  else if ai_neg n andalso (ty = Le orelse ty = Lt) then
    raise ERR "multiply_ineq" "negative multiplier on an inequality"
  else
    Lineq (Arbint.* (n, k), ty,
           List.map (fn c => Arbint.* (n, c)) coeffs,
           mk_multiplied n just)

fun add_ineq (Lineq (k1, ty1, coeffs1, just1))
             (Lineq (k2, ty2, coeffs2, just2)) =
  Lineq (Arbint.+ (k1, k2), find_add_type (ty1, ty2),
         ListPair.mapEq Arbint.+ (coeffs1, coeffs2),
         Added (just1, just2))

fun elim_var v (ineq1 as Lineq (_, ty1, coeffs1, _))
                   (ineq2 as Lineq (_, ty2, coeffs2, _)) =
  let
    val c1 = List.nth (coeffs1, v)
    val c2 = List.nth (coeffs2, v)
    val m = Arbint.lcm (Arbint.abs c1, Arbint.abs c2)
    val m1 = Arbint.div (m, Arbint.abs c1)
    val m2 = Arbint.div (m, Arbint.abs c2)
    val (n1, n2) =
      if ai_neg c1 = ai_neg c2 then
        if ty1 = Eq then (Arbint.~ m1, m2)
        else if ty2 = Eq then (m1, Arbint.~ m2)
        else raise ERR "elim_var" "no eliminable coefficient pair"
      else (m1, m2)
    val (p1, p2) =
      if ty1 = Eq andalso ty2 = Eq andalso
         (ai_eq n1 negone orelse ai_eq n2 negone)
      then (Arbint.~ n1, Arbint.~ n2)
      else (n1, n2)
  in
    add_ineq (multiply_ineq p1 ineq1) (multiply_ineq p2 ineq2)
  end

fun is_trivial (Lineq (_, _, coeffs, _)) = List.all ai_zero coeffs

fun is_contradictory (Lineq (k, ty, _, _)) =
  case ty of
      Eq => not (ai_zero k)
    | Le => ai_pos k
    | Lt => Arbint.>= (k, zero)

(* The equation pivot is a coefficient of least magnitude among the
   nonzero entries of the equations; ties (only ever c against ~c) go
   to the one met first in row-then-column order.  The single pass
   carries the position, so the rule holds by construction: searching
   the rows again for the winning coefficient's value would have to
   answer what a row holding its negation means, and would need a
   handler for a value that cannot have gone missing.

   NONE means no equation has a nonzero coefficient.  elim reaches
   this only with nontrivial rows, so that is exactly "no equations",
   and the caller's inequality branch is what NONE asks for. *)
fun pivot_equation rows =
  let
    fun in_row _ [] best = best
      | in_row j (c :: cs) best =
          let
            val magnitude = Arbint.abs c
            val best' =
              if ai_zero c then best
              else
                case best of
                    NONE => SOME (j, magnitude)
                  | SOME (_, m) =>
                      if Arbint.< (magnitude, m) then SOME (j, magnitude)
                      else best
          in
            in_row (j + 1) cs best'
          end
    fun over_rows _ [] best = best
      | over_rows i (Lineq (_, _, coeffs, _) :: rest) best =
          let
            val best' =
              case (in_row 0 coeffs NONE, best) of
                  (NONE, _) => best
                | (SOME (j, magnitude), NONE) => SOME (i, j, magnitude)
                | (SOME (j, magnitude), SOME (_, _, m)) =>
                    if Arbint.< (magnitude, m) then SOME (i, j, magnitude)
                    else best
          in
            over_rows (i + 1) rest best'
          end
    (* Splitting the pivot row out by index leaves the other equations
       in their original order, as Lib.pluck did. *)
    fun split _ [] _ = NONE
      | split 0 (row :: rest) prefix =
          SOME (row, List.revAppend (prefix, rest))
      | split i (row :: rest) prefix = split (i - 1) rest (row :: prefix)
    fun located (i, j, _) =
      Option.map (fn (row, others) => (j, row, others)) (split i rows [])
  in
    Option.mapPartial located (over_rows 0 rows NONE)
  end

(* One pass tallies the sign counts of every column; the pivot is the
   column with the smallest nonzero product, favouring earlier columns. *)
fun tally (c, (pos, neg)) =
  if ai_pos c then (pos + 1, neg)
  else if ai_neg c then (pos, neg + 1)
  else (pos, neg)

fun choose_blowup [] = NONE
  | choose_blowup (first :: rest) =
      let
        val counts =
          List.foldl
            (fn (row, acc) =>
                ListPair.mapEq tally (row, acc))
            (List.map (fn c => tally (c, (0, 0))) first) rest
        fun pick _ [] best = best
          | pick i ((pos, neg) :: more) best =
              let
                val blow = pos * neg
                val best' =
                  if blow = 0 then best
                  else
                    case best of
                        NONE => SOME (blow, i)
                      | SOME (old, _) =>
                          if blow < old then SOME (blow, i) else best
              in
                pick (i + 1) more best'
              end
      in
        pick 0 counts NONE
      end

(* Eliminating a variable emits |pos| x |neg| rows per round, and the same
   row is reachable along many paths; without this the set grows
   geometrically while the distinct rows stay few. *)
fun row_key (Lineq (k, ty, coeffs, _)) =
  (case ty of Eq => 0 | Le => 1 | Lt => 2, k, coeffs)

fun compare_key ((ty1, k1, cs1), (ty2, k2, cs2)) =
  case Int.compare (ty1, ty2) of
      EQUAL =>
        (case Arbint.compare (k1, k2) of
             EQUAL => Lib.list_compare Arbint.compare (cs1, cs2)
           | order => order)
    | order => order

fun distinct_rows rows =
  let
    fun add (row, (seen, kept)) =
      let
        val key = row_key row
      in
        if HOLset.member (seen, key) then (seen, kept)
        else (HOLset.add (seen, key), row :: kept)
      end
    val (_, kept) =
      List.foldl add (HOLset.empty compare_key, []) rows
  in
    List.rev kept
  end

(* Elimination traces one line per pivot, so the message is built only
   once the level has asked for it. *)
fun trace message =
  if linarithData.tracing 2 then linarithData.trace 2 (message ()) else ()

fun elim (ineqs, hist) =
  let
    val (triv, nontriv) = List.partition is_trivial ineqs
  in
    if not (List.null triv) then
      (case List.find is_contradictory triv of
           SOME (Lineq (_, _, _, just)) => Success just
         | NONE => elim (nontriv, hist))
    else if List.null nontriv then Failure hist
    else
      let
        val (eqs, noneqs) =
          List.partition
            (fn Lineq (_, ty, _, _) => ty = Eq) nontriv
      in
        case pivot_equation eqs of
            SOME (v, eq, other_eqs) =>
              let
                val (independent, dependent) =
                  List.partition
                    (fn Lineq (_, _, cs, _) => ai_zero (List.nth (cs, v)))
                    (other_eqs @ noneqs)
                val others =
                  List.map (elim_var v eq) dependent @ independent
              in
                trace (fn () => "equation pivot " ^ Int.toString v);
                elim (others, v :: hist)
              end
          | NONE =>
              let
                val coeff_lists =
                  List.map (fn Lineq (_, _, cs, _) => cs) noneqs
              in
                case choose_blowup coeff_lists of
                    NONE => Failure (~1 :: hist)
                  | SOME (_, v) =>
                      let
                        val (independent, dependent) =
                          List.partition
                            (fn Lineq (_, _, cs, _) =>
                                ai_zero (List.nth (cs, v))) ineqs
                        val (pos, neg) =
                          List.partition
                            (fn Lineq (_, _, cs, _) =>
                                ai_pos (List.nth (cs, v))) dependent
                        fun products [] = []
                          | products (p :: ps) =
                              List.map (elim_var v p) neg @ products ps
                      in
                        trace
                          (fn () => "inequality pivot " ^ Int.toString v);
                        elim (distinct_rows (independent @ products pos),
                              v :: hist)
                      end
              end
      end
  end

fun scale m rat =
  let
    val n = Arbrat.numerator rat
    val d = Arbint.fromNat (Arbrat.denominator rat)
  in
    Arbint.* (n, Arbint.div (m, d))
  end

fun integ (Decomp {lhs, lhs_const, rel, rhs, rhs_const,
                    discrete, negated}) =
  let
    val rats =
      lhs_const :: rhs_const ::
      List.map #2 lhs @ List.map #2 rhs
    val m =
      List.foldl
        (fn (rat, acc) =>
            Arbint.lcm
              (acc, Arbint.fromNat (Arbrat.denominator rat)))
        one rats
    fun mult (tm, rat) = (tm, scale m rat)
  in
    (m, {lhs = List.map mult lhs, lhs_const = scale m lhs_const,
         rel = rel, rhs = List.map mult rhs,
         rhs_const = scale m rhs_const, discrete = discrete,
         negated = negated})
  end

(* Termtab is keyed on Term.compare, whose EQUAL is exactly Term.aconv
   (both ignore a bound variable's name and compare its type), so the
   index classifies atoms the same way the linear search it replaces
   did. *)
type atom_index = {width : int, column : int Termtab.table}

fun atom_index atoms =
  let
    fun add (atom, (i, columns)) =
      (i + 1, Termtab.update (atom, i) columns)
    val (width, columns) =
      List.foldl add (0, Termtab.empty) atoms
  in
    {width = width, column = columns}
  end

(* Scattering the polynomial into its columns costs
   O(A + |poly| * log A), against the O(A * |poly|) of one linear
   search of the polynomial per column.  Atoms outside the index have
   no column and are dropped, as they were by mapping over the atom
   list.  The entries are placed back to front so that the first
   occurrence of a repeated atom wins, as List.find did. *)
fun scatter ({width, column} : atom_index) poly =
  let
    val row = Array.array (width, zero)
    fun place (tm, c) =
      case Termtab.lookup column tm of
          NONE => ()
        | SOME i => Array.update (row, i, c)
  in
    List.app place (List.rev poly); row
  end

fun mklineq index (item, asm_index) =
  let
    val (m, {lhs, lhs_const, rel, rhs, rhs_const,
             discrete, negated}) = integ item
    val lhs_coeffs = scatter index lhs
    val rhs_coeffs = scatter index rhs
    val diff =
      List.tabulate
        (#width index,
         fn i =>
            Arbint.- (Array.sub (rhs_coeffs, i),
                      Array.sub (lhs_coeffs, i)))
    val c = Arbint.- (lhs_const, rhs_const)
    val just = Asm asm_index
    fun lineq (constant, ty, cs, why) =
      Lineq (constant, ty, cs, mk_multiplied m why)
    fun negate cs = List.map Arbint.~ cs
  in
    case (rel, negated) of
        (REL_LE, false) => lineq (c, Le, diff, just)
      | (REL_LE, true) =>
          if discrete then
            lineq (Arbint.- (one, c), Le, negate diff,
                   NotLeDD just)
          else
            lineq (Arbint.~ c, Lt, negate diff, NotLeD just)
      | (REL_LT, false) =>
          if discrete then
            lineq (Arbint.+ (c, one), Le, diff, LessD just)
          else lineq (c, Lt, diff, just)
      | (REL_LT, true) =>
          lineq (Arbint.~ c, Le, negate diff, NotLessD just)
      (* The two equational relations arrive unnegated -- see the
         invariant on decomp in linarithSolve.sig -- so each is one
         arm, not two. *)
      | (REL_EQ, _) => lineq (c, Eq, diff, just)
      | (REL_NEQ, _) => raise ERR "mklineq" "unsplit disequality"
  end

(* Nonneg is the registry-extensible replacement for upstream mknat
   (fast_lin_arith.ML:549-553). *)
fun mknonneg is_nonnegative width (index, atom) =
  if is_nonnegative atom then
    SOME
      (Lineq
         (zero, Le,
          List.tabulate (width, fn i => if i = index then one else zero),
          Nonneg atom))
  else NONE

fun is_neq (Decomp {rel, ...}) = rel = REL_NEQ

fun is_discrete (Decomp {discrete, ...}) = discrete

fun less_decomp (Decomp {lhs, lhs_const, rhs, rhs_const,
                          discrete, ...}) =
  Decomp {lhs = lhs, lhs_const = lhs_const, rel = REL_LT,
          rhs = rhs, rhs_const = rhs_const, discrete = discrete,
          negated = false}

fun swap_less (Decomp {lhs, lhs_const, rhs, rhs_const,
                        discrete, ...}) =
  Decomp {lhs = rhs, lhs_const = rhs_const, rel = REL_LT,
          rhs = lhs, rhs_const = lhs_const, discrete = discrete,
          negated = false}

(* Unlike upstream's neqE-list ordering, each premise is discriminated by
   the discreteness its own decomposition carries
   (fast_lin_arith.ML:574-629). *)
fun elim_neq items =
  let
    fun pass _ [] = [[]]
      | pass discrete_only ((item as (tm, NONE)) :: rest) =
          List.map (fn xs => item :: xs) (pass discrete_only rest)
      | pass discrete_only
          ((item as (tm, SOME decomp)) :: rest) =
          if is_neq decomp andalso
             (not discrete_only orelse is_discrete decomp)
          then
            pass discrete_only
              (rest @ [(tm, SOME (less_decomp decomp))]) @
            pass discrete_only
              (rest @ [(tm, SOME (swap_less decomp))])
          else
            List.map (fn xs => item :: xs) (pass discrete_only rest)
  in
    List.concat (List.map (pass false) (pass true items))
  end

fun ignore_neq (tm, NONE) = (tm, NONE)
  | ignore_neq (tm, SOME decomp) =
      if is_neq decomp then (tm, NONE) else (tm, SOME decomp)

fun number_hyps items =
  let
    fun number _ [] = []
      | number n ((_, NONE) :: rest) = number (n + 1) rest
      | number n ((_, SOME decomp) :: rest) =
          (decomp, n) :: number (n + 1) rest
  in
    number 0 items
  end

fun split_items split_neq items =
  let
    val cases =
      if split_neq then elim_neq items
      else [List.map ignore_neq items]
  in
    List.map number_hyps cases
  end

(* Coefficient rows follow this order, so every row built for one
   split system must come from this one function. *)
fun atoms_of_decomps decomps =
  let
    fun add ((tm, _), acc as (seen, atoms)) =
      if Termtab.defined seen tm then acc
      else (Termtab.update (tm, ()) seen, tm :: atoms)
    fun add_decomp (Decomp {lhs, rhs, ...}, acc) =
      List.foldl add (List.foldl add acc lhs) rhs
    val (_, atoms) =
      List.foldl add_decomp (Termtab.empty, []) decomps
  in
    List.rev atoms
  end

fun refutes is_nonnegative systems =
  let
    fun refute [] justs = SOME (List.rev justs)
      | refute (items :: rest) justs =
          let
            val atoms = atoms_of_decomps (List.map #1 items)
            val index = atom_index atoms
            val nonnegative =
              List.mapPartial
                (mknonneg is_nonnegative (#width index))
                (Lib.enumerate 0 atoms)
            val ineqs =
              List.map (mklineq index) items @ nonnegative
          in
            case elim (ineqs, []) of
                Success just => refute rest (just :: justs)
              | Failure _ => NONE
          end
  in
    refute systems []
  end

fun negate tm =
  if boolSyntax.is_neg tm then boolSyntax.dest_neg tm
  else boolSyntax.mk_neg tm

fun prove_decomposed ({neq_limit, split_limit = _} : linarith_config)
                     decompose is_nonnegative hypotheses conclusion =
  case (SOME (negate conclusion)
        handle Feedback.HOL_ERR _ => NONE) of
      NONE => (false, NONE)
    | SOME negated_conclusion =>
        let
          val items =
            hypotheses @
            [(negated_conclusion, decompose negated_conclusion)]
          fun neq (_, SOME decomp) = is_neq decomp
            | neq (_, NONE) = false
          val neq_count = List.length (List.filter neq items)
          val split_neq = neq_count <= neq_limit
          val systems = split_items split_neq items
          val _ =
            if split_neq then ()
            else trace
                   (fn () =>
                      "neq_limit exceeded (current value is " ^
                      Int.toString neq_limit ^
                      "); ignoring disequalities")
        in
          (split_neq, refutes is_nonnegative systems)
        end

fun prove config decompose is_nonnegative hypotheses conclusion =
  prove_decomposed config decompose is_nonnegative
    (List.map (fn tm => (tm, decompose tm)) hypotheses) conclusion

end
