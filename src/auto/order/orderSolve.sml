structure orderSolve :> orderSolve =
struct

open HolKernel boolLib orderRulesTheory

val node_limit = ref 50

type work = {meter : orderData.meter, max_nodes : int option}

fun capped_work () : work =
  {meter = searchBudget.free_charger, max_nodes = SOME (!node_limit)}

fun budget_work budget : work =
  {meter = searchBudget.charger budget, max_nodes = NONE}

fun candidate (work : work) = #candidate (#meter work) ()
fun application (work : work) = #application (#meter work) ()
fun normalization (work : work) = #normalization (#meter work) ()

fun facts_of (work : work) = orderData.facts_of (#meter work)
fun facts_of_all (work : work) = orderData.facts_of_all (#meter work)

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

fun within_node_limit maximum edges =
  let
    fun add tm (state as (count, seen)) =
      if HOLset.member (seen, tm) then state
      else (count + 1, HOLset.add (seen, tm))
    fun scan (state as (count, _)) edges =
      count <= maximum andalso
      (case edges of
           [] => true
         | (e : edge) :: rest =>
             scan (add (#target e) (add (#source e) state)) rest)
  in
    scan (0, HOLset.empty Term.compare) edges
  end

datatype reachability =
    ReachedList of (term * thm) list
  | ReachedIndex of thm Termtab.table

fun reached work (ReachedList reached_nodes) tm =
      Option.map snd
        (search work
          (fn pair as (n, _) =>
            if aconv n tm then SOME pair else NONE)
          reached_nodes)
  | reached _ (ReachedIndex table) tm = Termtab.lookup table tm

fun settle target theorem (ReachedList reached_nodes) =
      ReachedList ((target, theorem) :: reached_nodes)
  | settle target theorem (ReachedIndex table) =
      ReachedIndex (Termtab.update (target, theorem) table)

(* Everything the source reaches, one theorem per node.  A node is
   settled the first time it is reached: the chain that reached it is a
   witness, and a second one would prove the same thing. *)
fun reachable work transitive edges source =
  case transitive of
      NONE =>
        ReachedList
          (List.map (fn e => (#target e, #theorem e))
            (List.filter
              (fn e => (candidate work; aconv (#source e) source))
              edges))
    | SOME transitive =>
        let
          val step = MATCH_MP order_weak_trans transitive
          (* Keep the same settlement and comparison order for metered
             calls.  Ordinary calls can index by alpha-equivalence. *)
          val empty =
            case #max_nodes work of
                NONE => ReachedList []
              | SOME _ => ReachedIndex Termtab.empty
          fun chain first second =
            (application work;
             MATCH_MP (MATCH_MP step first) second)
          fun relax (e, (known, changed)) =
            (candidate work;
             if aconv (#target e) source orelse
               Option.isSome (reached work known (#target e))
             then (known, changed)
             else if aconv (#source e) source then
               (settle (#target e) (#theorem e) known, true)
             else
               (case reached work known (#source e) of
                    SOME theorem =>
                      (settle (#target e) (chain theorem (#theorem e)) known,
                       true)
                  | NONE => (known, changed)))
          (* A changing round settles a new target from the finite
             edge list. *)
          fun rounds reached =
            let
              val (reached', changed) =
                List.foldl relax (reached, false) edges
            in
              if changed then rounds reached' else reached'
            end
        in
          rounds empty
        end

fun reach_from work transitive edges =
  let
    fun compute source = reachable work transitive edges source
    (* Crossing can use two sources. Limit retained reachability tables
       and keep each metered traversal observable. *)
    val from =
      case #max_nodes work of
          NONE => compute
        | SOME _ => memoUtil.bounded_memo 2 aconv compute
  in
    fn source => reached work (from source)
  end

(* The two chains that meet on a distinction. *)
fun crossing work (context : orderData.context) reach (x, y) =
  let
    val {antisymmetric, ...} = #axioms context
  in
    case antisymmetric of
        NONE => NONE
      | SOME antisymmetric =>
          (case reach x y of
               NONE => NONE
             | SOME up =>
                 (case reach y x of
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

fun close work (context : orderData.context) (edges, equalities) =
  let
    val reach = reach_from work (#transitive (#axioms context)) edges
    fun one (x, y, distinction) =
      let
        fun contradiction equality =
          (application work; MP (NOT_ELIM distinction) equality)
      in
        if aconv x y then SOME (contradiction (REFL x))
        else
          case stated work equalities (x, y) of
              SOME equality => SOME (contradiction equality)
            | NONE =>
                Option.map contradiction (crossing work context reach (x, y))
      end
  in
    one
  end

fun bounded_graph (work : work) (parts as (edges, _, _)) =
  case #max_nodes work of
      SOME maximum =>
        if within_node_limit maximum edges then SOME parts else NONE
    | NONE => SOME parts

fun refute_graph work context (edges, equalities, distinctions) =
  search work (close work context (edges, equalities)) distinctions

(* Proving a literal outright is the other half of the procedure.  A
   refutation reads the negated goal as a literal, and a relational atom
   has a negative reading only under totality, so a chain asked for by a
   goal that carries no totality -- [transitive R] and two steps -- is
   reachable this way and no other. *)
fun prove_literal work context
      (edges, equalities, distinctions) target =
  let
    val {reflexive, transitive, ...} = #axioms (context : orderData.context)
    val reach = reach_from work transitive edges
    fun weak (x, y) =
      if aconv x y then
        Option.map
          (fn r => MATCH_MP (MATCH_MP order_weak_of_equal r) (REFL x))
          reflexive
      else reach x y
  in
    case target of
        orderData.Weak pair => weak pair
      | orderData.Equal pair => crossing work context reach pair
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
    case bounded_graph work (expand work context supplied) of
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
                   val refutation_graph =
                     case #max_nodes work of
                         (* Keep the order of charges in the metered path. *)
                         NONE =>
                           bounded_graph work
                             (expand work context (negated @ supplied))
                       | SOME _ =>
                           let
                             val (edges, equalities, distinctions) = parts
                             val (extra_edges, extra_equalities,
                                  extra_distinctions) =
                               expand work context negated
                             val extended =
                               (extra_edges @ edges,
                                extra_equalities @ equalities,
                                extra_distinctions @ distinctions)
                           in
                             if null extra_edges then SOME extended
                             else bounded_graph work extended
                           end
                 in
                   Option.map (carry o restore)
                     (Option.mapPartial (refute_graph work context)
                        refutation_graph)
                 end)
  end

fun prove_using_with work contexts theorems term =
  search work (fn context => attempt work context theorems term) contexts

fun prove_using contexts theorems term =
  case prove_using_with (capped_work ()) contexts theorems term of
      SOME theorem => theorem
    | NONE =>
        raise mk_HOL_ERR "orderSolve" "prove_using"
          "no order in the assumptions decides the goal"

fun prove_with theorems term =
  prove_using (orderData.contexts searchBudget.free_charger theorems)
    theorems term

datatype budget_outcome =
    OrderProved of thm
  | OrderExhausted
  | OrderLimitReached of
      {kind : searchBudget.kind, usage : searchBudget.usage}

fun prove_using_budgeted budget =
  prove_using_with (budget_work budget)

fun prove_with_budget budget theorems term =
  (case prove_using_budgeted budget
          (orderData.contexts (searchBudget.charger budget) theorems)
          theorems term of
       SOME theorem => OrderProved theorem
     | NONE => OrderExhausted)
  handle searchBudget.LimitReached (kind, usage) =>
    OrderLimitReached {kind = kind, usage = usage}

end
