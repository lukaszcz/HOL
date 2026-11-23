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

(* A strict step is taken apart on the way in: [STRORD R x y] is [R x y]
   together with [x <> y], and nothing else about it is used.  So the
   graph carries weak edges only, chaining is transitivity alone, and the
   single closing rule is antisymmetry against a distinction.  That is
   complete for the usual refutation -- a cycle with a strict edge in it
   gives both directions between that edge's ends, so antisymmetry
   identifies them and the edge's own distinction denies it -- and it
   spares the procedure three further chaining cases. *)

datatype path =
    Proved of thm
  | Pending of thm Portable.HOLSusp.susp

fun path_theorem (Proved theorem) = theorem
  | path_theorem (Pending pending) = Portable.HOLSusp.force pending

(* Ordinary graph searches need proofs only along the selected paths.
   Metered calls construct them at the original charged operations. *)
fun derive_path (work : work) derive =
  case #max_nodes work of
      NONE => Proved (derive ())
    | SOME _ => Pending (Portable.HOLSusp.delay derive)

type edge = {source : term, target : term, path : path}

fun search work f [] = NONE
  | search work f (x :: xs) =
      (candidate work;
       case f x of NONE => search work f xs | found => found)

fun expand work (context : orderData.context) facts =
  let
    val {reflexive, ...} = #axioms context
    val intro =
      Option.map
        (fn theorem => Portable.HOLSusp.delay
          (fn () => MATCH_MP order_weak_of_equal theorem))
        reflexive
    fun weak_of_equal introduce equality =
      derive_path work
        (fn () =>
          let val theorem = equality () in
            application work;
            MATCH_MP (Portable.HOLSusp.force introduce) theorem
          end)
    fun edge (x, y) path = {source = x, target = y, path = path}
    fun one (fact : orderData.fact, (edges, equalities, distinctions)) =
      let
        val _ = candidate work
        val theorem = #theorem fact
      in
        case #literal fact of
            orderData.Weak (x, y) =>
              (edge (x, y) (Proved theorem) :: edges, equalities, distinctions)
          | orderData.Strict (x, y) =>
              let
                val _ = application work
                val weak =
                  derive_path work (fn () => MATCH_MP order_strict_weak theorem)
                val distinct =
                  derive_path work
                    (fn () => MATCH_MP order_strict_distinct theorem)
              in
                (edge (x, y) weak :: edges, equalities,
                 (x, y, distinct) :: distinctions)
              end
          | orderData.Equal (x, y) =>
              let
                val edges' =
                  case intro of
                      NONE => edges
                    | SOME r =>
                        let
                          val forward = weak_of_equal r (fn () => theorem)
                          val backward =
                            weak_of_equal r (fn () => SYM theorem)
                        in
                          edge (y, x) backward :: edge (x, y) forward :: edges
                        end
              in
                (edges', (x, y, theorem) :: equalities, distinctions)
              end
          | orderData.Distinct (x, y) =>
              (edges, equalities, (x, y, Proved theorem) :: distinctions)
      end
    val (edges, equalities, distinctions) =
      List.foldl one ([], [], []) facts
  in
    (List.rev edges, List.rev equalities, List.rev distinctions)
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
    ReachedList of (term * path) list
  | ReachedIndex of path Termtab.table

fun reached work (ReachedList reached_nodes) tm =
      Option.map snd
        (search work
          (fn pair as (n, _) =>
            if aconv n tm then SOME pair else NONE)
          reached_nodes)
  | reached _ (ReachedIndex table) tm = Termtab.lookup table tm

fun settle target path (ReachedList reached_nodes) =
      ReachedList ((target, path) :: reached_nodes)
  | settle target path (ReachedIndex table) =
      ReachedIndex (Termtab.update (target, path) table)

fun outgoing_edges edges =
  let
    fun add (edge : edge, (index, outgoing)) =
      (index + 1, Termtab.cons_list (#source edge, (index, edge)) outgoing)
  in
    #2 (List.foldl add (0, Termtab.empty) edges)
  end

(* A scan can use a newly reached node at later edges in the same round.
   Earlier edges must wait for the next round. Schedule just the edges
   that can relax, in the same (round, original position) order, so that
   a node still gets the same first path. Edges from a source reached
   in the initial scans are eligible from round zero. *)
fun indexed_rounds relax outgoing source nodes =
  let
    val empty =
      Redblackmap.mkDict (Lib.pair_compare (Int.compare, Int.compare))
    fun schedule round (index, edge) pending =
      Redblackmap.insert (pending, (round, index), edge)
    fun outgoing_from from =
      Option.getOpt (Termtab.lookup outgoing from, [])
    fun seed from pending =
      List.foldl
        (fn (entry as (_, edge : edge), pending) =>
          if aconv (#target edge) source orelse
             Option.isSome (Termtab.lookup nodes (#target edge)) then
            pending
          else schedule 0 entry pending)
        pending (outgoing_from from)
    val pending =
      Termtab.fold (fn (from, _) => seed from) nodes (seed source empty)
    fun run known pending =
      case Redblackmap.firsti pending of
          NONE => known
        | SOME (key as (round, last), edge) =>
            let
              val (rest, _) = Redblackmap.remove (pending, key)
              val (known', changed) = relax (edge, (known, false))
              val next =
                if changed then
                  let
                    fun add (entry as (position, _), pending) =
                      schedule (if position > last then round else round + 1)
                        entry pending
                  in
                    List.foldl add rest (outgoing_from (#target edge))
                  end
                else rest
            in
              run known' next
            end
  in
    run (ReachedIndex nodes) pending
  end

(* Everything the source reaches, one path per node. A node is settled
   the first time it is reached. Ordinary calls construct proofs only
   along the paths a caller actually needs. *)
fun reachable work transitivity edges outgoing observe source =
  case transitivity of
      NONE =>
        ReachedList
          (List.map (fn e => (#target e, #path e))
            (List.filter
              (fn e => (candidate work; aconv (#source e) source))
              edges))
    | SOME instantiate =>
        let
          val step = instantiate ()
          (* Keep the same settlement and comparison order for metered
             calls.  Ordinary calls can index by alpha-equivalence. *)
          val empty =
            case #max_nodes work of
                NONE => ReachedList []
              | SOME _ => ReachedIndex Termtab.empty
          fun chain first second =
            let
              fun derive () =
                MATCH_MP (MATCH_MP (path_theorem step) (path_theorem first))
                  (path_theorem second)
            in
              application work;
              derive_path work derive
            end
          fun settle_edge target path known =
            (observe (target, path); (settle target path known, true))
          fun relax (e, (known, changed)) =
            (candidate work;
             if aconv (#target e) source orelse
               Option.isSome (reached work known (#target e))
             then (known, changed)
             else if aconv (#source e) source then
               settle_edge (#target e) (#path e) known
             else
               (case reached work known (#source e) of
                    SOME path =>
                      settle_edge (#target e) (chain path (#path e)) known
                  | NONE => (known, changed)))
          (* A changing round settles a new target from the finite
             edge list. *)
          fun rounds left reached =
            let
              val (reached', changed) =
                List.foldl relax (reached, false) edges
            in
              if not changed then reached'
              else
                case reached' of
                    ReachedIndex nodes =>
                      if left = 1 then
                        indexed_rounds relax (Portable.HOLSusp.force outgoing)
                          source nodes
                      else rounds (left - 1) reached'
                  | ReachedList _ => rounds 0 reached'
            end
        in
          (* Small or forward chains often finish before an index pays
             for itself. Metered searches keep the complete scans. *)
          rounds (if Option.isSome (#max_nodes work) then 2 else 0) empty
        end

fun reach_from work transitive edges =
  let
    (* A contradiction can test several starting points on the same graph.
       Build the shared index only if one needs more than two scans. *)
    val outgoing = Portable.HOLSusp.delay (fn () => outgoing_edges edges)
    (* Share the rule across ordinary traversals, and instantiate it only
       when a composed path is used. Metered traversals keep the original
       eager instantiation for each source. *)
    fun transitivity theorem =
      let
        fun derive () = MATCH_MP order_weak_trans theorem
      in
        case #max_nodes work of
            NONE => (fn () => Proved (derive ()))
          | SOME _ =>
              let val step = derive_path work derive
              in fn () => step end
      end
    val step = Option.map transitivity transitive
    fun traverse observe source =
      reachable work step edges outgoing observe source
    val compute = traverse (fn _ => ())
    (* Crossing can use two sources. Limit retained reachability tables
       and keep each metered traversal observable. *)
    val from =
      case #max_nodes work of
          NONE => compute
        | SOME _ => memoUtil.bounded_memo 2 aconv compute
    fun reach source =
      let val known = from source
      in reached work known
      end
    fun reach_one source target =
      case (#max_nodes work, step) of
          (SOME _, SOME _) =>
            let
              (* A weak literal needs only its first path. Scheduling and
                 settlement are the same as for a full traversal. *)
              exception Found of path
              fun observe (node, path) =
                if aconv node target then raise Found path else ()
            in
              (ignore (traverse observe source); NONE)
              handle Found path => SOME path
            end
        | (SOME _, NONE) =>
            search work
              (fn edge =>
                if aconv (#source edge) source andalso
                   aconv (#target edge) target
                then SOME (#path edge) else NONE)
              edges
        | (NONE, _) => reach source target
  in
    {reach = reach, reach_one = reach_one}
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
                        let
                          val up_theorem = path_theorem up
                          val down_theorem = path_theorem down
                        in
                          SOME
                            (application work;
                             MATCH_MP
                               (MATCH_MP
                                  (MATCH_MP order_weak_antisymmetric
                                     antisymmetric)
                                  up_theorem)
                               down_theorem)
                        end))
  end

fun stated work equalities (x, y) =
  search work
    (fn (a, b, theorem) =>
       if aconv a x andalso aconv b y then SOME theorem
       else if aconv a y andalso aconv b x then SOME (SYM theorem)
       else NONE)
    equalities

fun equality_lookup (work : work) equalities =
  case (#max_nodes work, equalities) of
      (SOME _, _ :: _ :: _ :: _ :: _) =>
        let
          fun key (x, y) =
            if Term.compare (x, y) = GREATER then ((y, x), true)
            else ((x, y), false)
          val compare = Lib.pair_compare (Term.compare, Term.compare)
          fun build () =
            let
              fun add ((x, y, theorem), index) =
                let val (pair, reversed) = key (x, y)
                in Redblackmap.insert (index, pair, (theorem, reversed)) end
            in
              List.foldl add (Redblackmap.mkDict compare)
                (List.rev equalities)
            end
          val index = Portable.HOLSusp.delay build
          val scans = ref 8
        in
          fn endpoints =>
            (* Keep early lookups cheap. Repeated misses pay for a
               shared index. The first equality in either direction
               wins, and symmetry is applied only to the chosen proof. *)
            if !scans > 0 then
              (scans := !scans - 1; stated work equalities endpoints)
            else
              let val (pair, reversed) = key endpoints
              in
                Option.map
                  (fn (theorem, orientation) =>
                    if orientation = reversed then theorem else SYM theorem)
                  (Redblackmap.peek (Portable.HOLSusp.force index, pair))
              end
        end
    | _ => stated work equalities

fun close work (context : orderData.context) (edges, equalities) =
  let
    val {reach, ...} = reach_from work (#transitive (#axioms context)) edges
    val lookup = equality_lookup work equalities
    fun one (x, y, distinction) =
      let
        fun contradiction equality =
          (application work;
           MP (NOT_ELIM (path_theorem distinction)) equality)
      in
        if aconv x y then SOME (contradiction (REFL x))
        else
          case lookup (x, y) of
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
    val {reach, reach_one} = reach_from work transitive edges
    fun weak (x, y) =
      if aconv x y then
        Option.map
          (fn r => MATCH_MP (MATCH_MP order_weak_of_equal r) (REFL x))
          reflexive
      else Option.map path_theorem (reach_one x y)
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
    val read = orderData.facts_of (#meter work) context
    val supplied = List.concat (List.map read theorems)
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
                   val negated = read (ASSUME assumption)
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
