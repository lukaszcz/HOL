structure orderLib :> orderLib =
struct

open HolKernel boolLib

val ERR = mk_HOL_ERR "orderLib"

(* An order axiom or edge may carry schematic type parameters even when
   the initial goal uses a concrete relation.  Match the theorem-backed
   invocation view at each relation head actually present in the goal.
   The matcher keeps support and genuinely fixed parameters rigid. *)
fun relation_of term =
  case Lib.total dest_comb term of
      SOME (left, _) =>
        (case Lib.total dest_comb left of
             SOME (relation, _) => SOME relation
           | NONE => NONE)
    | NONE => NONE

fun relation_sites terms =
  let
    val candidates =
      List.concat
        (map (List.mapPartial relation_of o find_terms (fn _ => true))
          terms)
  in
    List.foldl
      (fn (site, seen) =>
        if Lib.op_mem aconv site seen then seen else seen @ [site])
      [] candidates
  end

fun same_theorem left right =
  aconv (Thm.concl left) (Thm.concl right) andalso
  let
    val left_support = Thm.hyp left
    val right_support = Thm.hyp right
  in
    List.all (fn term => Lib.op_mem aconv term right_support)
      left_support andalso
    List.all (fn term => Lib.op_mem aconv term left_support)
      right_support
  end

fun distinct_theorems theorems =
  List.foldl
    (fn (theorem, seen) =>
      if List.exists (same_theorem theorem) seen then seen
      else seen @ [theorem])
    [] theorems

fun order_fact_views_with charge goal theorems =
  let
    val environment =
      clasetFacts.create_with_charge charge goal theorems
    (* Antisymmetry can close an equality whose conclusion contains no
       relation application.  Concrete edges in the context then supply
       the carrier; a schematic citation alone does not. *)
    val sites =
      relation_sites (#2 goal :: #1 goal) @
      List.filter
        (null o type_vars_in_term)
        (relation_sites (map Thm.concl theorems))
    fun views entry =
      let
        val schematic = #theorem (clasetFacts.schematic_view entry)
        val contexts = orderData.contexts [schematic]
        val patterns =
          relation_sites [Thm.concl schematic] @
          map #relation contexts
        val instances =
          List.concat
            (map
              (fn pattern =>
                List.mapPartial
                  (fn site =>
                    (charge searchBudget.Candidate;
                     Option.map #theorem
                       (clasetFacts.match_view entry pattern site)))
                  sites)
              patterns)
      in
        clasetFacts.source entry :: instances
      end
  in
    distinct_theorems
      (List.concat (map views (clasetFacts.facts environment)))
  end

fun order_fact_views goal theorems =
  order_fact_views_with (fn _ => ()) goal theorems

(* The goal's own assumptions are the context: an order arrives as a
   premise, so a tactic that ignored them would decide nothing.  The
   prefix is stripped first, which is what puts the axioms of a goal
   stated as [!R. transitive R ==> ...] into the assumptions. *)
fun solve theorems (goal as (asl, w)) _ =
  let
    val facts = List.map ASSUME asl @ order_fact_views goal theorems
  in
    ([], fn _ => orderSolve.prove_with facts w)
  end

fun ORDER_TAC theorems =
  REPEAT GEN_TAC THEN
  REPEAT (DISCH_THEN STRIP_ASSUME_TAC) THEN
  solve theorems

fun ORDER_PROVE tm =
  let
    val (goals, validation) =
      Tactical.VALID (ORDER_TAC []) ([], tm) (Context.snapshot())
  in
    if null goals then validation []
    else raise ERR "ORDER_PROVE" "unsolved goals"
  end

fun ORDER_CONV tm = EQT_INTRO (ORDER_PROVE tm)

(* Ground contexts are derived once per addition to the simplifier's
   context.  A citation with schematic types gets an extra view only
   when the current atom has a matching relation head.  That view is
   cached under the whole atom and discarded when the context changes;
   an assumed theorem cannot escape its fixed support types. *)
fun make_order_reducer budget =
  let
    fun contexts_of theorems =
      case budget of
          NONE => orderData.contexts theorems
        | SOME owned => orderData.contexts_budgeted owned theorems
    fun prove contexts theorems tm =
      case budget of
          NONE => orderSolve.prove_using contexts theorems tm
        | SOME owned =>
            (case orderSolve.prove_using_budgeted
                    owned contexts theorems tm of
                 orderSolve.OrderProved theorem => theorem
               | orderSolve.OrderExhausted =>
                   raise ERR "ORDER_DP" "no order proof"
               | orderSolve.OrderLimitReached {kind, usage} =>
                   raise searchBudget.LimitReached (kind, usage))
    exception CTXT of
      {theorems : thm list,
       contexts : orderData.context list,
       sites :
         (term * (thm list * orderData.context list)) list ref}
    fun get_context e = (raise e) handle CTXT value => value
    fun addcontext (context, newtheorems) =
      let
        val {theorems, contexts, ...} = get_context context
        val added = List.concat (List.map CONJUNCTS newtheorems)
        val theorems = added @ theorems
        val contexts =
          if orderData.has_order_axiom added then
            contexts_of theorems
          else contexts
      in
        (* A context is derived from order axioms alone, so the
           derivation is repeated only when one arrives.  The
           simplifier adds to its context at every assumption it
           passes, and rewriting each of those with the order
           definitions to find nothing is the cost this avoids. *)
        CTXT {theorems = theorems, contexts = contexts,
              sites = ref []}
      end
    fun apply args tm =
      let
        val {theorems, contexts, sites} =
          get_context (#context args)
        fun equality_domain term =
          case Lib.total dest_eq term of
              SOME (left, _) => SOME (type_of left)
            | NONE =>
                (case Lib.total dest_neg term of
                     SOME body => equality_domain body
                   | NONE => NONE)
        fun context_site_for_equality () =
          (* Only an equality of the order's carrier may borrow a site
             from a concrete context edge.  Matching the theorem view
             still enforces its fixed parameters and support. *)
          case equality_domain tm of
              NONE => []
            | SOME domain =>
                if List.exists
                     (fn context =>
                       let
                         val (pattern, _) =
                           Type.dom_rng
                             (type_of (#relation context))
                       in
                         Lib.can (Type.match_type pattern) domain
                       end)
                     contexts
                then
                  List.filter
                    (null o type_vars_in_term)
                    (relation_sites (map Thm.concl theorems))
                else []
        fun matching_site [] = NONE
          | matching_site (site :: rest) =
              if List.exists
                   (fn context =>
                     Lib.can
                       (Term.match_term (#relation context)) site)
                   contexts
              then SOME site
              else matching_site rest
        fun at_atom () =
          case List.find (fn (key, _) => aconv key tm) (!sites) of
              SOME (_, result) => result
            | NONE =>
                let
                  val charge =
                    case budget of
                        NONE => (fn _ => ())
                      | SOME owned => searchBudget.charge owned
                  val views =
                    order_fact_views_with charge ([], tm) theorems
                  val result = (views, contexts_of views)
                  val previous = !sites
                in
                  sites :=
                    (tm, result) ::
                    List.take (previous, Int.min (length previous, 127));
                  result
                end
      in
        if List.exists (fn c => orderData.is_literal c tm) contexts then
          EQT_INTRO (prove contexts theorems tm)
        else
          case
            matching_site
              (relation_sites [tm] @ context_site_for_equality ())
          of
              NONE =>
                raise ERR "ORDER_DP"
                  "not a literal of an order in the context"
            | SOME _ =>
                let
                  val (views, derived) = at_atom ()
                in
                  if List.exists
                       (fn c => orderData.is_literal c tm) derived
                  then EQT_INTRO (prove derived views tm)
                  else raise ERR "ORDER_DP"
                         "not a literal of an order in the context"
                end
      end
  in
    Traverse.REDUCER
      {name = SOME "ORDER_DP",
       addcontext = addcontext,
       apply = apply,
       initial =
         CTXT {theorems = [], contexts = [], sites = ref []}}
  end

val ORDER_REDUCER = make_order_reducer NONE

fun ORDER_REDUCER_BUDGETED budget =
  make_order_reducer (SOME budget)

val ORDER_ss =
  simpLib.named_merge_ss "ORDER"
    [simpLib.SSFRAG
       {name = SOME "ORDER_DP",
        convs = [], rewrs = [], congs = [], filter = NONE,
        ac = [], dprocs = [ORDER_REDUCER]}]

fun ORDER_ss_budgeted budget =
  simpLib.named_merge_ss "ORDER"
    [simpLib.SSFRAG
       {name = SOME "ORDER_DP",
        convs = [], rewrs = [], congs = [], filter = NONE,
        ac = [], dprocs = [ORDER_REDUCER_BUDGETED budget]}]

end
