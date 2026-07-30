structure linarithSolve :> linarithSolve =
struct

(* Nonneg generalizes upstream Nat (fast_lin_arith.ML:191-202). *)
datatype lineq_type = Eq | Le | Lt

datatype injust =
    Asm of int
  | Nonneg of int
  | LessD of injust
  | NotLessD of injust
  | NotLeD of injust
  | NotLeDD of injust
  | Multiplied of Arbint.int * injust
  | Added of injust * injust

datatype lineq =
  Lineq of Arbint.int * lineq_type * Arbint.int list * injust

type history = (int * lineq list) list
datatype result = Success of injust | Failure of history

type linarith_config = {neq_limit : int, split_limit : int}

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

type neq_selector = Term.term -> bool option

val zero = Arbint.zero
val one = Arbint.one
val negone = Arbint.~ one

fun ai_eq x y = x = y
fun ai_zero x = ai_eq x zero
fun ai_one x = ai_eq x one
fun ai_neg x = Arbint.< (x, zero)
fun ai_pos x = Arbint.> (x, zero)

fun map2 f ([], []) = []
  | map2 f (x :: xs, y :: ys) = f (x, y) :: map2 f (xs, ys)
  | map2 _ _ = raise Fail "linarithSolve: unequal row lengths"

fun nth (x :: _, 0) = x
  | nth (_ :: xs, n) = nth (xs, n - 1)
  | nth _ = raise Subscript

fun find_add_type (Eq, ty) = ty
  | find_add_type (ty, Eq) = ty
  | find_add_type (_, Lt) = Lt
  | find_add_type (Lt, _) = Lt
  | find_add_type (Le, Le) = Le

fun multiply_ineq n (ineq as Lineq (k, ty, coeffs, just)) =
  if ai_one n then ineq
  else if ai_zero n andalso ty = Lt then
    raise Fail "linarithSolve.multiply_ineq"
  else if ai_neg n andalso (ty = Le orelse ty = Lt) then
    raise Fail "linarithSolve.multiply_ineq"
  else
    Lineq (Arbint.* (n, k), ty,
           List.map (fn c => Arbint.* (n, c)) coeffs,
           Multiplied (n, just))

fun add_ineq (Lineq (k1, ty1, coeffs1, just1))
             (Lineq (k2, ty2, coeffs2, just2)) =
  Lineq (Arbint.+ (k1, k2), find_add_type (ty1, ty2),
         map2 Arbint.+ (coeffs1, coeffs2), Added (just1, just2))

fun elim_var v (ineq1 as Lineq (_, ty1, coeffs1, _))
                   (ineq2 as Lineq (_, ty2, coeffs2, _)) =
  let
    val c1 = nth (coeffs1, v)
    val c2 = nth (coeffs2, v)
    val m = Arbint.lcm (Arbint.abs c1, Arbint.abs c2)
    val m1 = Arbint.div (m, Arbint.abs c1)
    val m2 = Arbint.div (m, Arbint.abs c2)
    val (n1, n2) =
      if ai_neg c1 = ai_neg c2 then
        if ty1 = Eq then (Arbint.~ m1, m2)
        else if ty2 = Eq then (m1, Arbint.~ m2)
        else raise Fail "linarithSolve.elim_var"
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

fun calc_blowup coeffs =
  let
    val nonzero = List.filter (not o ai_zero) coeffs
    val (pos, neg) = List.partition ai_pos nonzero
  in
    List.length pos * List.length neg
  end

fun extract_first pred items =
  let
    fun extract _ [] = raise List.Empty
      | extract prefix (item :: rest) =
          if pred item then (item, prefix @ rest)
          else extract (item :: prefix) rest
  in
    extract [] items
  end

fun first_some _ [] = NONE
  | first_some pred (x :: xs) =
      if pred x then SOME x else first_some pred xs

fun distinct_coeffs rows =
  let
    fun add c cs =
      if List.exists (ai_eq c) cs then cs else c :: cs
    fun add_row (Lineq (_, _, coeffs, _), cs) =
      List.foldl (fn (c, acc) => add c acc) cs coeffs
  in
    List.foldl add_row [] rows
  end

fun min_abs (c :: cs) =
  let
    fun better (x, best) =
      if Arbint.< (Arbint.abs x, Arbint.abs best) then x else best
  in
    List.foldl better c cs
  end
  | min_abs [] = raise List.Empty

fun choose_blowup coeff_lists =
  let
    val width = List.length (hd coeff_lists)
    fun loop i best =
      if i = width then best
      else
        let
          val blow = calc_blowup (List.map (fn row => nth (row, i))
                                           coeff_lists)
          val best' =
            if blow = 0 then best
            else
              case best of
                  NONE => SOME (blow, i)
                | SOME (old, _) =>
                    if blow < old then SOME (blow, i) else best
        in
          loop (i + 1) best'
        end
  in
    loop 0 NONE
  end

(* The trace is deliberately looked up lazily.  linarithData registers it in
   the next layer; this core therefore also compiles and runs on its own. *)
fun trace msg =
  ((if Feedback.get_tracefn "linarith" () > 1 then
      print ("linarith: " ^ msg ^ "\n")
    else ())
   handle Feedback.HOL_ERR _ => ())

fun elim (ineqs, hist) =
  let
    val (triv, nontriv) = List.partition is_trivial ineqs
  in
    if not (List.null triv) then
      (case first_some is_contradictory triv of
           SOME (Lineq (_, _, _, just)) => Success just
         | NONE => elim (nontriv, hist))
    else if List.null nontriv then Failure hist
    else
      let
        val (eqs, noneqs) =
          List.partition
            (fn Lineq (_, ty, _, _) => ty = Eq) nontriv
      in
        if not (List.null eqs) then
          let
            val coeff =
              min_abs
                (List.filter (not o ai_zero) (distinct_coeffs eqs))
            val (eq as Lineq (_, _, eqcoeffs, _), other_eqs) =
              extract_first
                (fn Lineq (_, _, cs, _) => List.exists (ai_eq coeff) cs)
                eqs
            fun index _ [] = raise Fail "linarithSolve.elim: pivot"
              | index i (c :: cs) =
                  if ai_eq c coeff then i else index (i + 1) cs
            val v = index 0 eqcoeffs
            val (independent, dependent) =
              List.partition
                (fn Lineq (_, _, cs, _) => ai_zero (nth (cs, v)))
                (other_eqs @ noneqs)
            val others =
              List.map (elim_var v eq) dependent @ independent
          in
            trace ("equation pivot " ^ Int.toString v);
            elim (others, (v, nontriv) :: hist)
          end
        else
          let
            val coeff_lists =
              List.map (fn Lineq (_, _, cs, _) => cs) noneqs
          in
            case choose_blowup coeff_lists of
                NONE => Failure ((~1, nontriv) :: hist)
              | SOME (_, v) =>
                  let
                    val (independent, dependent) =
                      List.partition
                        (fn Lineq (_, _, cs, _) =>
                            ai_zero (nth (cs, v))) ineqs
                    val (pos, neg) =
                      List.partition
                        (fn Lineq (_, _, cs, _) =>
                            ai_pos (nth (cs, v))) dependent
                    fun products [] = []
                      | products (p :: ps) =
                          List.map (elim_var v p) neg @ products ps
                  in
                    trace ("inequality pivot " ^ Int.toString v);
                    elim (independent @ products pos,
                          (v, nontriv) :: hist)
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

fun coeff poly atom =
  case List.find (fn (tm, _) => Term.aconv tm atom) poly of
      NONE => zero
    | SOME (_, c) => c

fun mklineq atoms (item, index) =
  let
    val (m, {lhs, lhs_const, rel, rhs, rhs_const,
             discrete, negated}) = integ item
    val lhs_coeffs = List.map (coeff lhs) atoms
    val rhs_coeffs = List.map (coeff rhs) atoms
    val diff = map2 Arbint.- (rhs_coeffs, lhs_coeffs)
    val c = Arbint.- (lhs_const, rhs_const)
    val just = Asm index
    fun lineq (constant, ty, cs, why) =
      Lineq (constant, ty, cs,
             if ai_one m then why else Multiplied (m, why))
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
      | (REL_EQ, false) => lineq (c, Eq, diff, just)
      | (REL_EQ, true) =>
          raise Fail "linarithSolve.mklineq: unsplit disequality"
      | (REL_NEQ, false) =>
          raise Fail "linarithSolve.mklineq: unsplit disequality"
      | (REL_NEQ, true) => lineq (c, Eq, diff, just)
  end

(* Nonneg is the registry-extensible replacement for upstream mknat
   (fast_lin_arith.ML:549-553). *)
fun mknonneg is_nonnegative indices (atom, index) =
  if is_nonnegative atom then
    SOME
      (Lineq
         (zero, Le,
          List.map (fn i => if i = index then one else zero) indices,
          Nonneg index))
  else NONE

fun is_neq (Decomp {rel, negated, ...}) =
  (rel = REL_NEQ andalso not negated) orelse
  (rel = REL_EQ andalso negated)

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

(* Unlike upstream's neqE-list ordering, the selector discriminates each
   premise by its own type (fast_lin_arith.ML:574-629). *)
fun elim_neq selector items =
  let
    fun pass _ [] = [[]]
      | pass discrete_only ((item as (tm, NONE)) :: rest) =
          List.map (fn xs => item :: xs) (pass discrete_only rest)
      | pass discrete_only
          ((item as (tm, SOME decomp)) :: rest) =
          if is_neq decomp andalso
             (case selector tm of
                  SOME discrete =>
                    (not discrete_only orelse discrete)
                | NONE => false)
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

fun split_items selector split_neq decompose terms =
  let
    val items = List.map (fn tm => (tm, decompose tm)) terms
    val cases =
      if split_neq then elim_neq selector items
      else [List.map ignore_neq items]
  in
    List.map number_hyps cases
  end

fun add_atom atom atoms =
  if List.exists (Term.aconv atom) atoms then atoms else atoms @ [atom]

fun atoms_of_decomp
      ((Decomp {lhs, rhs, ...}, _), atoms) =
  List.foldl (fn ((tm, _), acc) => add_atom tm acc)
    (List.foldl (fn ((tm, _), acc) => add_atom tm acc) atoms lhs) rhs

fun refutes systems =
  let
    fun refute [] justs = SOME justs
      | refute (items :: rest) justs =
          let
            val atoms = List.foldl atoms_of_decomp [] items
            val count = List.length atoms
            val indices = List.tabulate (count, fn i => i)
            val atom_indices = ListPair.zip (atoms, indices)
            fun nat_atom tm = Term.type_of tm = numSyntax.num
            val nonnegative =
              List.mapPartial (mknonneg nat_atom indices) atom_indices
            val ineqs =
              List.map (mklineq atoms) items @ nonnegative
          in
            case elim (ineqs, []) of
                Success just => refute rest (justs @ [just])
              | Failure _ => NONE
          end
  in
    refute systems []
  end

fun negate tm =
  if boolSyntax.is_neg tm then boolSyntax.dest_neg tm
  else boolSyntax.mk_neg tm

fun prove ({neq_limit, split_limit = _} : linarith_config)
          decompose hypotheses conclusion =
  case (SOME (negate conclusion)
        handle Feedback.HOL_ERR _ => NONE) of
      NONE => (false, NONE)
    | SOME negated_conclusion =>
        let
          val terms = hypotheses @ [negated_conclusion]
          fun neq tm =
            case decompose tm of
                SOME decomp => is_neq decomp
              | NONE => false
          val neq_count = List.length (List.filter neq terms)
          val split_neq = neq_count <= neq_limit
          fun selector tm =
            case decompose tm of
                SOME decomp => SOME (is_discrete decomp)
              | NONE => NONE
          val systems =
            split_items selector split_neq decompose terms
          val _ =
            if split_neq then ()
            else trace ("neq_limit exceeded (current value is " ^
                        Int.toString neq_limit ^
                        "); ignoring disequalities")
        in
          (split_neq, refutes systems)
        end

end
