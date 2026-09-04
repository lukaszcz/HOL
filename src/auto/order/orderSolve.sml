structure orderSolve :> orderSolve =
struct

open HolKernel boolLib orderRulesTheory

val node_limit = ref 50

(* A strict step is taken apart on the way in: [STRORD R x y] is [R x y]
   together with [x <> y], and nothing else about it is used.  So the
   graph carries weak edges only, chaining is transitivity alone, and the
   single closing rule is antisymmetry against a distinction.  That is
   complete for the usual refutation -- a cycle with a strict edge in it
   gives both directions between that edge's ends, so antisymmetry
   identifies them and the edge's own distinction denies it -- and it
   spares the procedure three further chaining cases. *)

type edge = {source : term, target : term, theorem : thm}

fun search f [] = NONE
  | search f (x :: xs) = (case f x of NONE => search f xs | found => found)

fun expand (context : orderData.context) facts =
  let
    val {reflexive, ...} = #axioms context
    fun weak_of_equal theorem =
      case reflexive of
          SOME r => [MATCH_MP (MATCH_MP order_weak_of_equal r) theorem]
        | NONE => []
    fun edge (x, y) theorem = {source = x, target = y, theorem = theorem}
    fun one fact =
      case #literal (fact : orderData.fact) of
          orderData.Weak (x, y) => ([edge (x, y) (#theorem fact)], [], [])
        | orderData.Strict (x, y) =>
            ([edge (x, y) (MATCH_MP order_strict_weak (#theorem fact))],
             [],
             [(x, y, MATCH_MP order_strict_distinct (#theorem fact))])
        | orderData.Equal (x, y) =>
            (List.map (edge (x, y)) (weak_of_equal (#theorem fact)) @
             List.map (edge (y, x)) (weak_of_equal (SYM (#theorem fact))),
             [(x, y, #theorem fact)],
             [])
        | orderData.Distinct (x, y) => ([], [], [(x, y, #theorem fact)])
    val parts = List.map one facts
  in
    (List.concat (List.map #1 parts),
     List.concat (List.map #2 parts),
     List.concat (List.map #3 parts))
  end

fun nodes edges =
  let
    fun add (tm, seen) =
      if List.exists (aconv tm) seen then seen else tm :: seen
  in
    List.foldl
      (fn (e, seen) => add (#target e, add (#source e, seen))) [] edges
  end

(* Everything the source reaches, one theorem per node.  A node is
   settled the first time it is reached: the chain that reached it is a
   witness, and a second one would prove the same thing. *)
fun reachable transitive edges source =
  let
    fun known reached tm =
      Option.map snd (List.find (fn (n, _) => aconv n tm) reached)
  in
    case transitive of
        NONE =>
          List.map (fn e => (#target e, #theorem e))
            (List.filter (fn e => aconv (#source e) source) edges)
      | SOME transitive =>
          let
            val step = MATCH_MP order_weak_trans transitive
            fun chain first second =
              MATCH_MP (MATCH_MP step first) second
            fun relax (e, (reached, changed)) =
              if aconv (#target e) source orelse
                 Option.isSome (known reached (#target e))
              then (reached, changed)
              else if aconv (#source e) source then
                ((#target e, #theorem e) :: reached, true)
              else
                (case known reached (#source e) of
                     SOME theorem =>
                       ((#target e, chain theorem (#theorem e)) :: reached,
                        true)
                   | NONE => (reached, changed))
            fun rounds reached remaining =
              if remaining <= 0 then reached
              else
                let
                  val (reached', changed) =
                    List.foldl relax (reached, false) edges
                in
                  if changed then rounds reached' (remaining - 1) else reached'
                end
          in
            rounds [] (List.length (nodes edges) + 1)
          end
  end

(* Everything a distinction needs: the two chains that meet on it, or an
   equality already stated, or the two sides being the same term. *)
fun reached reached_nodes tm =
  Option.map snd (List.find (fn (n, _) => aconv n tm) reached_nodes)

fun crossing (context : orderData.context) edges (x, y) =
  let
    val {transitive, antisymmetric, ...} = #axioms context
  in
    case antisymmetric of
        NONE => NONE
      | SOME antisymmetric =>
          (case reached (reachable transitive edges x) y of
               NONE => NONE
             | SOME up =>
                 (case reached (reachable transitive edges y) x of
                      NONE => NONE
                    | SOME down =>
                        SOME
                          (MATCH_MP
                             (MATCH_MP
                                (MATCH_MP order_weak_antisymmetric
                                   antisymmetric)
                                up)
                             down)))
  end

fun stated equalities (x, y) =
  search
    (fn (a, b, theorem) =>
       if aconv a x andalso aconv b y then SOME theorem
       else if aconv a y andalso aconv b x then SOME (SYM theorem)
       else NONE)
    equalities

fun close context (edges, equalities) (x, y, distinction) =
  let
    fun contradiction equality = MP (NOT_ELIM distinction) equality
  in
    if aconv x y then SOME (contradiction (REFL x))
    else
      case stated equalities (x, y) of
          SOME equality => SOME (contradiction equality)
        | NONE => Option.map contradiction (crossing context edges (x, y))
  end

fun graph context facts =
  let
    val (edges, equalities, distinctions) = expand context facts
  in
    if List.length (nodes edges) > !node_limit then NONE
    else SOME (edges, equalities, distinctions)
  end

fun refute context facts =
  case graph context facts of
      NONE => NONE
    | SOME (edges, equalities, distinctions) =>
        search (close context (edges, equalities)) distinctions

(* Proving a literal outright is the other half of the procedure.  A
   refutation reads the negated goal as a literal, and a relational atom
   has a negative reading only under totality, so a chain asked for by a
   goal that carries no totality -- [transitive R] and two steps -- is
   reachable this way and no other. *)
fun prove_literal context (edges, equalities, distinctions) target =
  let
    val {reflexive, transitive, ...} = #axioms (context : orderData.context)
    fun weak (x, y) =
      if aconv x y then
        Option.map
          (fn r => MATCH_MP (MATCH_MP order_weak_of_equal r) (REFL x))
          reflexive
      else reached (reachable transitive edges x) y
  in
    case target of
        orderData.Weak pair => weak pair
      | orderData.Equal pair => crossing context edges pair
      | orderData.Strict (x, y) =>
          (case weak (x, y) of
               NONE => NONE
             | SOME step =>
                 (case refute_equation context
                         (edges, equalities, distinctions) (x, y) of
                      NONE => NONE
                    | SOME apart =>
                        SOME (MATCH_MP (MATCH_MP order_strict_intro step)
                                apart)))
      | orderData.Distinct pair =>
          refute_equation context (edges, equalities, distinctions) pair
  end

(* [x <> y] is proved the way any negation is: the equation is assumed
   and the graph it joins is refuted. *)
and refute_equation context (edges, equalities, distinctions) (x, y) =
  let
    val equation = mk_eq (x, y)
    val assumed = ASSUME equation
    val facts = [{literal = orderData.Equal (x, y), theorem = assumed}]
    val (extra_edges, extra_equalities, _) = expand context facts
    val closed =
      search
        (close context (edges @ extra_edges, extra_equalities @ equalities))
        distinctions
  in
    Option.map (fn refutation => NOT_INTRO (DISCH equation refutation)) closed
  end

(* The goal is proved outright where it can be and refuted otherwise.  A
   goal that is already a negation is discharged rather than doubly
   negated, so [~R x y] is a goal this decides and not an atom it fails
   to read. *)
fun attempt context theorems term =
  let
    val equation = orderData.reduce context term
    val target = rhs (concl equation)
    val supplied = orderData.facts_of_all context theorems
    fun carry theorem = EQ_MP (SYM equation) theorem
  in
    case graph context supplied of
        NONE => NONE
      | SOME parts =>
          (case Option.mapPartial (prove_literal context parts)
                  (orderData.literal_of_term context target) of
               SOME theorem => SOME (carry theorem)
             | NONE =>
                 let
                   val (assumption, restore) =
                     case Lib.total dest_neg target of
                         SOME body =>
                           (body, fn r => NOT_INTRO (DISCH body r))
                       | NONE => (mk_neg target, fn r => CCONTR target r)
                   val negated =
                     orderData.facts_of context (ASSUME assumption)
                 in
                   Option.map (carry o restore)
                     (refute context (negated @ supplied))
                 end)
  end

fun prove_using contexts theorems term =
  case search (fn context => attempt context theorems term) contexts of
      SOME theorem => theorem
    | NONE =>
        raise mk_HOL_ERR "orderSolve" "prove_using"
          "no order in the assumptions decides the goal"

fun prove_with theorems term =
  prove_using (orderData.contexts theorems) theorems term

end
