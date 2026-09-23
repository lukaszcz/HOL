structure orderSolve :> orderSolve =
struct

open HolKernel boolLib orderRulesTheory

val node_limit = ref 50

type work =
  {candidate : unit -> unit,
   application : unit -> unit,
   normalization : unit -> unit,
   max_nodes : int option,
   budget : searchBudget.budget option}

fun legacy_work () : work =
  {candidate = fn () => (), application = fn () => (),
   normalization = fn () => (), max_nodes = SOME (!node_limit),
   budget = NONE}

fun budget_work budget : work =
  {candidate = fn () =>
     searchBudget.charge budget searchBudget.Candidate,
   application = fn () =>
     searchBudget.charge budget searchBudget.Application,
   normalization = fn () =>
     searchBudget.charge budget searchBudget.Normalization,
   max_nodes = NONE, budget = SOME budget}

fun candidate (work : work) = #candidate work ()
fun application (work : work) = #application work ()
fun normalization (work : work) = #normalization work ()

fun facts_of work context theorem =
  case #budget (work : work) of
      NONE => orderData.facts_of context theorem
    | SOME budget => orderData.facts_of_budgeted budget context theorem

fun facts_of_all work context theorems =
  case #budget (work : work) of
      NONE => orderData.facts_of_all context theorems
    | SOME budget =>
        orderData.facts_of_all_budgeted budget context theorems

(* A strict step is taken apart on the way in: [STRORD R x y] is [R x y]
   together with [x <> y], and nothing else about it is used.  So the
   graph carries weak edges only, chaining is transitivity alone, and the
   single closing rule is antisymmetry against a distinction.  That is
   complete for the usual refutation -- a cycle with a strict edge in it
   gives both directions between that edge's ends, so antisymmetry
   identifies them and the edge's own distinction denies it -- and it
   spares the procedure three further chaining cases. *)

type edge = {source : term, target : term, theorem : thm}

fun search work f [] = NONE
  | search work f (x :: xs) =
      (candidate work;
       case f x of NONE => search work f xs | found => found)

fun expand work (context : orderData.context) facts =
  let
    val {reflexive, ...} = #axioms context
    fun weak_of_equal theorem =
      case reflexive of
          SOME r =>
            (application work;
             [MATCH_MP (MATCH_MP order_weak_of_equal r) theorem])
        | NONE => []
    fun edge (x, y) theorem = {source = x, target = y, theorem = theorem}
    fun one fact =
      case #literal (fact : orderData.fact) of
          orderData.Weak (x, y) => ([edge (x, y) (#theorem fact)], [], [])
        | orderData.Strict (x, y) =>
            let
              val _ = application work
            in
              ([edge (x, y) (MATCH_MP order_strict_weak (#theorem fact))],
               [],
               [(x, y, MATCH_MP order_strict_distinct (#theorem fact))])
            end
        | orderData.Equal (x, y) =>
            (List.map (edge (x, y)) (weak_of_equal (#theorem fact)) @
             List.map (edge (y, x)) (weak_of_equal (SYM (#theorem fact))),
             [(x, y, #theorem fact)],
             [])
        | orderData.Distinct (x, y) => ([], [], [(x, y, #theorem fact)])
    val parts =
      List.map (fn fact => (candidate work; one fact)) facts
  in
    (List.concat (List.map #1 parts),
     List.concat (List.map #2 parts),
     List.concat (List.map #3 parts))
  end

fun nodes work edges =
  let
    fun add (tm, seen) =
      if Option.isSome
           (search work
             (fn known => if aconv tm known then SOME () else NONE)
             seen)
      then seen else tm :: seen
  in
    List.foldl
      (fn (e, seen) =>
        (candidate work;
         add (#target e, add (#source e, seen)))) [] edges
  end

(* Everything the source reaches, one theorem per node.  A node is
   settled the first time it is reached: the chain that reached it is a
   witness, and a second one would prove the same thing. *)
fun reachable work transitive edges source =
  let
    fun known reached tm =
      Option.map snd
        (search work
          (fn pair as (n, _) =>
            if aconv n tm then SOME pair else NONE)
          reached)
  in
    case transitive of
        NONE =>
          List.map (fn e => (#target e, #theorem e))
            (List.filter
              (fn e => (candidate work; aconv (#source e) source))
              edges)
      | SOME transitive =>
          let
            val step = MATCH_MP order_weak_trans transitive
            fun chain first second =
              (application work;
               MATCH_MP (MATCH_MP step first) second)
            fun relax (e, (reached, changed)) =
              (candidate work;
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
              )
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
            rounds [] (List.length (nodes work edges) + 1)
          end
  end

(* Everything a distinction needs: the two chains that meet on it, or an
   equality already stated, or the two sides being the same term. *)
fun reached work reached_nodes tm =
  Option.map snd
    (search work
      (fn pair as (n, _) =>
        if aconv n tm then SOME pair else NONE)
      reached_nodes)

fun crossing work (context : orderData.context) edges (x, y) =
  let
    val {transitive, antisymmetric, ...} = #axioms context
  in
    case antisymmetric of
        NONE => NONE
      | SOME antisymmetric =>
          (case reached work (reachable work transitive edges x) y of
               NONE => NONE
             | SOME up =>
                 (case reached work (reachable work transitive edges y) x of
                      NONE => NONE
                    | SOME down =>
                        SOME
                          (application work;
                           MATCH_MP
                             (MATCH_MP
                                (MATCH_MP order_weak_antisymmetric
                                   antisymmetric)
                                up)
                             down)))
  end

fun stated work equalities (x, y) =
  search work
    (fn (a, b, theorem) =>
       if aconv a x andalso aconv b y then SOME theorem
       else if aconv a y andalso aconv b x then SOME (SYM theorem)
       else NONE)
    equalities

fun close work context (edges, equalities) (x, y, distinction) =
  let
    fun contradiction equality =
      (application work; MP (NOT_ELIM distinction) equality)
  in
    if aconv x y then SOME (contradiction (REFL x))
    else
      case stated work equalities (x, y) of
          SOME equality => SOME (contradiction equality)
        | NONE =>
            Option.map contradiction
              (crossing work context edges (x, y))
  end

fun graph work context facts =
  let
    val (edges, equalities, distinctions) =
      expand work context facts
  in
    case #max_nodes work of
        SOME maximum =>
          if List.length (nodes work edges) > maximum then NONE
          else SOME (edges, equalities, distinctions)
      | NONE => SOME (edges, equalities, distinctions)
  end

fun refute_with work context facts =
  case graph work context facts of
      NONE => NONE
    | SOME (edges, equalities, distinctions) =>
        search work
          (close work context (edges, equalities)) distinctions

fun refute context facts =
  refute_with (legacy_work ()) context facts

(* Proving a literal outright is the other half of the procedure.  A
   refutation reads the negated goal as a literal, and a relational atom
   has a negative reading only under totality, so a chain asked for by a
   goal that carries no totality -- [transitive R] and two steps -- is
   reachable this way and no other. *)
fun prove_literal work context
      (edges, equalities, distinctions) target =
  let
    val {reflexive, transitive, ...} = #axioms (context : orderData.context)
    fun weak (x, y) =
      if aconv x y then
        Option.map
          (fn r => MATCH_MP (MATCH_MP order_weak_of_equal r) (REFL x))
          reflexive
      else reached work (reachable work transitive edges x) y
  in
    case target of
        orderData.Weak pair => weak pair
      | orderData.Equal pair => crossing work context edges pair
      | orderData.Strict (x, y) =>
          (case weak (x, y) of
               NONE => NONE
             | SOME step =>
                 (case refute_equation work context
                         (edges, equalities, distinctions) (x, y) of
                      NONE => NONE
                    | SOME apart =>
                        (application work;
                         SOME (MATCH_MP (MATCH_MP order_strict_intro step)
                                 apart))))
      | orderData.Distinct pair =>
          refute_equation work context
            (edges, equalities, distinctions) pair
  end

(* [x <> y] is proved the way any negation is: the equation is assumed
   and the graph it joins is refuted. *)
and refute_equation work context
      (edges, equalities, distinctions) (x, y) =
  let
    val equation = mk_eq (x, y)
    val assumed = ASSUME equation
    val facts = [{literal = orderData.Equal (x, y), theorem = assumed}]
    val (extra_edges, extra_equalities, _) =
      expand work context facts
    val closed =
      search work
        (close work context
          (edges @ extra_edges, extra_equalities @ equalities))
        distinctions
  in
    Option.map (fn refutation => NOT_INTRO (DISCH equation refutation)) closed
  end

(* The goal is proved outright where it can be and refuted otherwise.  A
   goal that is already a negation is discharged rather than doubly
   negated, so [~R x y] is a goal this decides and not an atom it fails
   to read. *)
fun attempt work context theorems term =
  let
    val _ = normalization work
    val equation = orderData.reduce context term
    val target = rhs (concl equation)
    val supplied = facts_of_all work context theorems
    fun carry theorem = EQ_MP (SYM equation) theorem
  in
    case graph work context supplied of
        NONE => NONE
      | SOME parts =>
          (case Option.mapPartial (prove_literal work context parts)
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
                     facts_of work context (ASSUME assumption)
                 in
                   Option.map (carry o restore)
                     (refute_with work context (negated @ supplied))
                 end)
  end

fun prove_using_with work contexts theorems term =
  case search work
         (fn context => attempt work context theorems term) contexts of
      SOME theorem => theorem
    | NONE =>
        raise mk_HOL_ERR "orderSolve" "prove_using"
          "no order in the assumptions decides the goal"

fun prove_using contexts theorems term =
  prove_using_with (legacy_work ()) contexts theorems term

fun prove_with theorems term =
  prove_using (orderData.contexts theorems) theorems term

datatype budget_outcome =
    OrderProved of thm
  | OrderExhausted
  | OrderLimitReached of
      {kind : searchBudget.kind, usage : searchBudget.usage}

fun prove_with_budget budget theorems term =
  let
    val work = budget_work budget
    val contexts = orderData.contexts_budgeted budget theorems
  in
    case search work
           (fn context => attempt work context theorems term)
           contexts of
        SOME theorem => OrderProved theorem
      | NONE => OrderExhausted
  end
  handle searchBudget.LimitReached (kind, usage) =>
    OrderLimitReached {kind = kind, usage = usage}

end
