open HolKernel testutils
open orderLib

fun check (name, predicate) =
  (tprint name;
   if predicate () then OK () else die "failed")

(* None of these goals is a benchmark entry.  Each poses one shape the
   procedure has to read -- a chain longer than a single transitivity
   step, a named order that has to be taken apart, a distinction closed
   by antisymmetry, a negative literal turned round by totality, a
   strict primitive -- and the last two pin what it refuses. *)

fun proves tm = (ORDER_PROVE tm; true) handle Feedback.HOL_ERR _ => false

fun refuses tm = not (proves tm)

val _ =
  check
    ("a chain of weak steps closes on transitivity alone",
     fn () =>
       proves
         ``!R a b c d.
             relation$transitive R ==> R a b ==> R b c ==> R c d ==> R a d``)

(* This finite chain has more terms than the unbudgeted graph cap.  Its
   facts are hypotheses, so a larger budgeted search must still
   reconstruct a theorem with exactly the supplied support. *)
val long_order_type = Type.alpha
val long_order_relation =
  Term.mk_var
    ("long_order_le",
     Type.--> (long_order_type,
       Type.--> (long_order_type, Type.bool)))
val long_order_nodes =
  List.tabulate
    (52, fn index =>
      Term.mk_var
        ("long_order_node_" ^ Int.toString index, long_order_type))
fun long_order_edge left right =
  Term.mk_comb
    (Term.mk_comb (long_order_relation,
       List.nth (long_order_nodes, left)),
     List.nth (long_order_nodes, right))
val long_order_axiom =
  Term.mk_comb
    (Term.prim_mk_const
       {Thy = "relation", Name = "WeakLinearOrder"},
     long_order_relation)
val long_order_facts =
  Thm.ASSUME long_order_axiom ::
  List.tabulate
    (51, fn index =>
      Thm.ASSUME (long_order_edge index (index + 1)))
val long_order_target = long_order_edge 0 51

fun count_primitives f x =
  let
    val meter = Count.mk_meter ()
    val result = f x handle exn => (Count.counting_thms false; raise exn)
    val {prims, ...} = Count.read meter
    val _ = Count.counting_thms false
  in
    (result, prims)
  end

fun unrelated_edges_unproved edge =
  let
    val target = long_order_edge 0 1
    val direct = [Thm.ASSUME long_order_axiom, Thm.ASSUME target]
    val unrelated =
      List.tabulate
        (23, fn i =>
          Thm.ASSUME
            (edge (List.nth (long_order_nodes, 2 * i + 2),
                   List.nth (long_order_nodes, 2 * i + 3))))
    fun count facts =
      count_primitives (fn facts => orderSolve.prove_with facts target) facts
    val (_, bare) = count direct
    val (theorem, loaded) = count (direct @ unrelated)
  in
    Term.aconv (Thm.concl theorem) target andalso
    Lib.list_eq Term.aconv (Thm.hyp theorem) [target] andalso
    (* Allow normalization work for the unused assumptions. *)
    loaded <= bare + 4 * List.length unrelated
  end

val _ =
  check
    ("a direct order proof leaves unrelated equality edges unproved",
     fn () => unrelated_edges_unproved boolSyntax.mk_eq)

val _ =
  check
    ("a weak order proof leaves unrelated strict distinctions unproved",
     fn () =>
       let
         val strict =
           Term.mk_comb
             (Term.prim_mk_const {Thy = "relation", Name = "STRORD"},
              long_order_relation)
       in
         unrelated_edges_unproved
           (fn (x, y) => Term.list_mk_comb (strict, [x, y]))
       end)

val _ =
  check
    ("repeated distinction checks use the first equality in either direction",
     fn () =>
       let
         val transitive =
           Thm.ASSUME
             (Term.mk_comb
                (Term.prim_mk_const {Thy = "relation", Name = "transitive"},
                 long_order_relation))
         fun equation i j =
           boolSyntax.mk_eq
             (List.nth (long_order_nodes, i), List.nth (long_order_nodes, j))
         val early =
           List.tabulate
             (8, fn i => Thm.ASSUME (boolSyntax.mk_neg (equation 0 (i + 2))))
         val later = boolSyntax.mk_neg (equation 0 1)
         val fillers =
           List.tabulate (2, fn i => Thm.ASSUME (equation 10 (i + 11)))
         fun uses_first first second =
           let
             val facts =
               transitive :: early @
               (Thm.ASSUME later :: (fillers @ map Thm.ASSUME [first, second]))
             val theorem = orderSolve.prove_with facts boolSyntax.F
             val support = Thm.hyp theorem
           in
             length support = 2 andalso
             List.exists (Term.aconv first) support andalso
             List.exists (Term.aconv later) support
           end
       in
         uses_first (equation 1 0) (equation 0 1) andalso
         uses_first (equation 0 1) (equation 1 0)
       end)

val _ =
  check
    ("negative order facts share the instantiated totality rules",
     fn () =>
       let
         val [context] = orderData.contexts searchBudget.free_charger
           [Thm.ASSUME long_order_axiom]
         val strict =
           Term.mk_comb
             (Term.prim_mk_const {Thy = "relation", Name = "STRORD"},
              long_order_relation)
         fun fact i =
           let
             val edge =
               if i mod 2 = 0 then long_order_edge i (i + 1)
               else Term.list_mk_comb
                 (strict, [List.nth (long_order_nodes, i),
                           List.nth (long_order_nodes, i + 1)])
           in
             Thm.ASSUME (boolSyntax.mk_neg edge)
           end
         val facts = List.tabulate (30, fact)
         fun count read =
           count_primitives
             (fn read => map (fn fact : orderData.fact => #theorem fact)
               (List.concat (map read facts)))
             read
         val budget = searchBudget.unbounded ()
         val (ordinary, cached) =
           count (orderData.facts_of (searchBudget.charger budget) context)
         fun read_fresh theorem =
           orderData.facts_of searchBudget.free_charger context theorem
         val (reference, uncached) = count read_fresh
         fun same (left, right) =
           Term.aconv (Thm.concl left) (Thm.concl right) andalso
           Lib.list_eq Term.aconv (Thm.hyp left) (Thm.hyp right)
         val {applications, candidates, normalization} =
           searchBudget.usage budget
         val limited =
           searchBudget.create
             {applications = SOME 4, candidates = NONE, normalization = NONE}
         val cut_on_cached_rule =
           (ignore (orderData.facts_of_all (searchBudget.charger limited)
              context facts); false)
           handle searchBudget.LimitReached (searchBudget.Application, usage) =>
             #applications usage = 4 andalso #candidates usage = 3
       in
         length ordinary = length facts andalso
         ListPair.allEq same (ordinary, reference) andalso cached < uncached
         andalso applications = 60 andalso candidates = 30
         andalso normalization = 60 andalso cut_on_cached_rule
       end)

val _ =
  check
    ("the unbudgeted graph cap clips a finite transitivity chain",
     fn () =>
       ((ignore
           (orderSolve.prove_with
             long_order_facts long_order_target);
         false)
        handle Feedback.HOL_ERR _ => true))

fun long_budget limits = searchBudget.create limits

val _ =
  check
    ("a weak goal uses the first path before a later direct edge",
     fn () =>
       let
         val target = long_order_edge 0 2
         val support =
           [long_order_axiom, long_order_edge 0 1, long_order_edge 1 2]
         val facts = map Thm.ASSUME (support @ [target])
         val theorem = orderSolve.prove_with facts target
       in
         Term.aconv (Thm.concl theorem) target andalso
         length (Thm.hyp theorem) = length support andalso
         List.all
           (fn tm => List.exists (Term.aconv tm) (Thm.hyp theorem))
           support
       end)

val _ =
  check
    ("reverse-chain reachability keeps the original first proof path",
     fn () =>
       let
         fun fact left right = Thm.ASSUME (long_order_edge left right)
         val prefix = List.rev (List.tabulate (40, fn i => fact i (i + 1)))
         val earlier = [fact 40 42, fact 42 43]
         val later = [fact 40 41, fact 41 43]
         val axiom = Thm.ASSUME long_order_axiom
         val facts = (axiom :: earlier) @ prefix @ later
         val target = long_order_edge 0 43
         val ordinary = orderSolve.prove_with facts target
         fun same_hypotheses theorem =
           Lib.list_eq Term.aconv (Thm.hyp ordinary) (Thm.hyp theorem)
       in
         Term.aconv (Thm.concl ordinary) target andalso
         List.all
           (fn fact =>
             List.exists (Term.aconv (Thm.concl fact)) (Thm.hyp ordinary))
           later andalso
         (case orderSolve.prove_with_budget
                 (searchBudget.unbounded ()) facts target of
              orderSolve.OrderProved metered => same_hypotheses metered
            | _ => false)
       end)

val _ =
  check
    ("distinct sources in one graph keep their own first proof paths",
     fn () =>
       let
         fun fact left right = Thm.ASSUME (long_order_edge left right)
         fun apart left right =
           Thm.ASSUME
             (boolSyntax.mk_neg
               (boolSyntax.mk_eq (List.nth (long_order_nodes, left),
                            List.nth (long_order_nodes, right))))
         val chain = List.rev (List.tabulate (40, fn i => fact i (i + 1)))
         val distinctions = [apart 0 43, apart 1 43, apart 0 40]
         val facts =
           (Thm.ASSUME long_order_axiom :: chain) @
           (fact 40 0 :: distinctions)
         val target = boolSyntax.F
         val ordinary = orderSolve.prove_with facts target
         fun same_hypotheses theorem =
           Lib.list_eq Term.aconv (Thm.hyp ordinary) (Thm.hyp theorem)
       in
         Term.aconv (Thm.concl ordinary) target andalso
         List.exists (Term.aconv (Thm.concl (List.last distinctions)))
           (Thm.hyp ordinary) andalso
         (case orderSolve.prove_with_budget
                 (searchBudget.unbounded ()) facts target of
              orderSolve.OrderProved metered => same_hypotheses metered
            | _ => false)
       end)

val _ =
  check
    ("a budgeted invocation proves beyond the unbudgeted graph cap",
     fn () =>
       case orderSolve.prove_with_budget
              (long_budget
                {candidates = NONE, applications = NONE,
                 normalization = NONE})
              long_order_facts long_order_target of
           orderSolve.OrderProved theorem =>
             Term.aconv (Thm.concl theorem) long_order_target andalso
             List.length (Thm.hyp theorem) =
               List.length long_order_facts andalso
             List.all
               (fn fact =>
                 List.exists (Term.aconv (Thm.concl fact))
                   (Thm.hyp theorem))
               long_order_facts
         | _ => false)

val _ =
  check
    ("candidate exhaustion is reported with its usage",
     fn () =>
       case orderSolve.prove_with_budget
              (long_budget
                {candidates = SOME 0, applications = NONE,
                 normalization = NONE})
              long_order_facts long_order_target of
           orderSolve.OrderLimitReached
             {kind = searchBudget.Candidate, usage} =>
               #candidates usage = 0
         | _ => false)

val _ =
  check
    ("application exhaustion is distinct from candidate exhaustion",
     fn () =>
       case orderSolve.prove_with_budget
              (long_budget
                {candidates = NONE, applications = SOME 0,
                 normalization = NONE})
              long_order_facts long_order_target of
           orderSolve.OrderLimitReached
             {kind = searchBudget.Application, usage} =>
               #applications usage = 0 andalso #candidates usage > 0
         | _ => false)

val _ =
  check
    ("normalization exhaustion is reported before work starts",
     fn () =>
       case orderSolve.prove_with_budget
              (long_budget
                {candidates = NONE, applications = NONE,
                 normalization = SOME 0})
              long_order_facts long_order_target of
           orderSolve.OrderLimitReached
             {kind = searchBudget.Normalization, usage} =>
               #normalization usage = 0
         | _ => false)

val _ =
  check
    ("a budgeted search distinguishes exhaustion from its limits",
     fn () =>
       case orderSolve.prove_with_budget
              (searchBudget.unbounded ()) [] long_order_target of
           orderSolve.OrderExhausted => true
         | _ => false)

val _ =
  check
    ("context conversion checkpoints a flood of irrelevant theorems",
     fn () =>
       let
         val irrelevant =
           List.tabulate
             (80, fn index =>
               Thm.ASSUME
                 (Term.mk_var
                   ("irrelevant_order_fact_" ^ Int.toString index,
                    Type.bool)))
         val budget =
           long_budget
             {candidates = NONE, applications = NONE,
              normalization = SOME 3}
       in
         case orderSolve.prove_with_budget budget
                (irrelevant @ long_order_facts) long_order_target of
             orderSolve.OrderLimitReached
               {kind = searchBudget.Normalization, usage} =>
                 #normalization usage = 3 andalso
                 #candidates usage < 80
           | _ => false
       end)

val _ =
  check
    ("repeated order calls keep charging their caller's budget",
     fn () =>
       let
         val budget = searchBudget.unbounded ()
         val facts = List.take (long_order_facts, 4)
         val target = long_order_edge 0 3
         val _ = searchBudget.charge budget searchBudget.Candidate
         val first = orderSolve.prove_with_budget budget facts target
         val first_usage = searchBudget.usage budget
         val second = orderSolve.prove_with_budget budget facts target
         val second_usage = searchBudget.usage budget
       in
         (case (first, second) of
              (orderSolve.OrderProved left,
               orderSolve.OrderProved right) =>
                Term.aconv (Thm.concl left) target andalso
                Term.aconv (Thm.concl right) target
            | _ => false) andalso
         #candidates second_usage =
           2 * #candidates first_usage - 1 andalso
         #applications second_usage =
           2 * #applications first_usage andalso
         #normalization second_usage =
           2 * #normalization first_usage
       end)

val _ =
  check
    ("a named order is taken apart for its axioms",
     fn () =>
       proves
         ``!le a b c.
             relation$WeakLinearOrder le ==> le a b ==> le b c ==> le a c``)

val _ =
  check
    ("two chains meeting head to tail are identified by antisymmetry",
     fn () =>
       proves
         ``!le a b c.
             relation$WeakOrder le ==>
             le a b ==> le b c ==> le c a ==> (a = c)``)

val _ =
  check
    ("a refused weak step is read as a strict one under totality",
     fn () =>
       proves
         ``!le a b c.
             relation$WeakLinearOrder le ==>
             ~le a b ==> le a c ==> le c b ==> F``)

val _ =
  check
    ("an equation joins the chain it stands in",
     fn () =>
       proves
         ``!le a b c.
             relation$WeakOrder le ==> le a b ==> (b = c) ==> le a c``)

val _ =
  check
    ("a strict primitive chains as the strict part of its closure",
     fn () =>
       proves
         ``!lt a b c.
             relation$StrongLinearOrder lt ==>
             lt a b ==> lt b c ==> ~(c = a)``)

val _ =
  check
    ("a strict primitive chains in the spelling the goal uses",
     fn () =>
       proves
         ``!lt a b c.
             relation$StrongOrder lt ==> lt a b ==> lt b c ==> lt a c``)

val _ =
  check
    ("a step the chain does not reach is refused",
     fn () =>
       refuses
         ``!R a b c.
             relation$transitive R ==> R a b ==> R b c ==> R c a``)

val _ =
  check
    ("a relation with no order axiom is refused",
     fn () => refuses ``!R a b c. R a b ==> R b c ==> R a c``)

(* The tactic reads the goal's own assumptions, which is how it is
   reached from inside a search: the axioms and the facts arrive there
   and not as arguments. *)
val _ =
  let
    val relation_type =
      Type.--> (Type.alpha, Type.--> (Type.alpha, Type.bool))
    val le = Term.mk_var ("order_le", relation_type)
    val a = Term.mk_var ("order_a", Type.alpha)
    val b = Term.mk_var ("order_b", Type.alpha)
    val c = Term.mk_var ("order_c", Type.alpha)
    fun apply f x y = Term.mk_comb (Term.mk_comb (f, x), y)
    val goal =
      ([Term.mk_comb
          (Term.prim_mk_const {Thy = "relation", Name = "WeakLinearOrder"},
           le),
        apply le a b, apply le b c],
       apply le a c)
  in
    check
      ("ORDER_TAC takes the order and the facts from the assumptions",
       fn () =>
         let
           val (remaining, validation) =
             Tactical.VALID (ORDER_TAC []) goal (Context.snapshot())
         in
           List.null remaining andalso
           Term.aconv (Thm.concl (validation [])) (Lib.snd goal)
         end)
  end

val _ =
  check
    ("ORDER_TAC uses supplied edges with their theorem support",
     fn () =>
       let
         val relation_type =
           Type.--> (Type.alpha, Type.--> (Type.alpha, Type.bool))
         val le = Term.mk_var ("order_fact_le", relation_type)
         val a = Term.mk_var ("order_fact_a", Type.alpha)
         val b = Term.mk_var ("order_fact_b", Type.alpha)
         val c = Term.mk_var ("order_fact_c", Type.alpha)
         fun edge x y = Term.mk_comb (Term.mk_comb (le, x), y)
         val first = edge a b
         val second = edge b c
         val first_support = boolSyntax.mk_disj (first, boolSyntax.F)
         val second_support = boolSyntax.mk_disj (second, boolSyntax.F)
         val order_axiom =
           Term.mk_comb
             (Term.prim_mk_const
                {Thy = "relation", Name = "WeakLinearOrder"}, le)
         val supplied =
           map
             (Rewrite.REWRITE_RULE [boolTheory.OR_CLAUSES] o Thm.ASSUME)
             [first_support, second_support]
         fun closes facts assumptions =
           case Lib.total
                  (fn goal =>
                    Tactical.VALID (ORDER_TAC facts) goal
                      (Context.snapshot()))
                  (assumptions, edge a c) of
               SOME ([], validation) =>
                 (SOME (validation [])
                    handle Feedback.HOL_ERR _ => NONE)
             | _ => NONE
         val supported =
           closes supplied [order_axiom, first_support, second_support]
       in
         not (Option.isSome
           (closes [] [order_axiom, first_support, second_support]))
         andalso
         not (Option.isSome (closes supplied [order_axiom])) andalso
         (case supported of
              SOME theorem =>
                List.exists (Term.aconv first_support) (Thm.hyp theorem)
                andalso
                List.exists (Term.aconv second_support) (Thm.hyp theorem)
            | NONE => false)
       end)

val _ =
  check
    ("ORDER_TAC instantiates a supplied order at the goal carrier",
     fn () =>
       let
         val goal =
           ([``relation$RSUBSET
                (r:num->num->bool) (s:num->num->bool)``,
             ``relation$RSUBSET
                (s:num->num->bool) (t:num->num->bool)``],
            ``relation$RSUBSET
                (r:num->num->bool) (t:num->num->bool)``)
         val other_goal =
           ([``relation$RSUBSET
                (r:bool->bool->bool) (s:bool->bool->bool)``,
             ``relation$RSUBSET
                (s:bool->bool->bool) (t:bool->bool->bool)``],
            ``relation$RSUBSET
                (r:bool->bool->bool) (t:bool->bool->bool)``)
         fun closes tactic target =
           case Lib.total
                  (fn () =>
                    Tactical.VALID tactic target
                      (Context.snapshot ())) () of
               SOME ([], validation) =>
                 (ignore (validation []); true)
             | _ => false
         val axiom = relationTheory.RSUBSET_WeakOrder
         val concrete =
           Thm.INST_TYPE
             (map
               (fn variable =>
                 {redex = variable, residue = Term.type_of ``0:num``})
               (type_vars_in_term (Thm.concl axiom))) axiom
         val schematic_tactic = ORDER_TAC [axiom]
       in
         not (closes (ORDER_TAC []) goal) andalso
         closes (ORDER_TAC [concrete]) goal andalso
         closes schematic_tactic goal andalso
         closes schematic_tactic other_goal
       end)

(* A theorem supplied directly to the simplifier keeps its schematic
   carrier.  ASSUME_TAC turns the same statement into an assumption whose
   support fixes that carrier; the reducer must not reinterpret that
   assumption as a fresh citation. *)
val _ =
  check
    ("ORDER_ss keeps theorem citations distinct from assumptions",
     fn () =>
       let
         val axiom = relationTheory.RSUBSET_WeakOrder
         val concrete =
           Thm.INST_TYPE
             (map
               (fn variable =>
                 {redex = variable, residue = Term.type_of ``0:num``})
               (type_vars_in_term (Thm.concl axiom))) axiom
         val ss = simpLib.++ (boolSimps.bool_ss, ORDER_ss)
         val goal =
           ([``relation$RSUBSET
                (r:num->num->bool) (s:num->num->bool)``,
             ``relation$RSUBSET
                (s:num->num->bool) (t:num->num->bool)``],
            ``relation$RSUBSET
                (r:num->num->bool) (t:num->num->bool)``)
         fun closes theorem =
           case Lib.total
                  (fn () =>
                    Tactical.VALID
                      (Tactical.THEN
                        (Tactic.ASSUME_TAC theorem,
                         simpLib.ASM_SIMP_TAC ss []))
                      goal (Context.snapshot ())) () of
               SOME ([], validation) =>
                 (ignore (validation []); true)
             | _ => false
         fun direct_at goal theorem =
           case Lib.total
                  (fn () =>
                    Tactical.VALID
                      (simpLib.ASM_SIMP_TAC ss [theorem])
                      goal (Context.snapshot ())) () of
               SOME ([], validation) =>
                 (ignore (validation []); true)
             | _ => false
         fun direct theorem = direct_at goal theorem
         val guard = ``order_site_guard:bool``
         val guarded = Drule.ADD_ASSUM guard axiom
       in
         closes concrete andalso
         not (closes axiom) andalso
         direct concrete andalso direct axiom andalso
         not (direct guarded) andalso
         direct_at (guard :: #1 goal, #2 goal) guarded
       end)

val _ =
  check
    ("ORDER_ss uses a schematic order for antisymmetry",
     fn () =>
       let
         val axiom = relationTheory.RSUBSET_WeakOrder
         val concrete =
           Thm.INST_TYPE
             (map
               (fn variable =>
                 {redex = variable, residue = Term.type_of ``0:num``})
               (type_vars_in_term (Thm.concl axiom))) axiom
         val ss = simpLib.++ (boolSimps.bool_ss, ORDER_ss)
         val goal =
           ([``relation$RSUBSET
                (r:num->num->bool) (s:num->num->bool)``,
             ``relation$RSUBSET
                (s:num->num->bool) (r:num->num->bool)``],
            ``(r:num->num->bool) = s``)
         fun closes facts =
           case Lib.total
                  (fn () =>
                    Tactical.VALID
                      (simpLib.ASM_SIMP_TAC ss facts)
                      goal (Context.snapshot ())) () of
               SOME ([], validation) =>
                 (ignore (validation []); true)
             | _ => false
       in
         not (closes []) andalso
         closes [concrete] andalso closes [axiom]
       end)

(* The decision procedure sees an atom the rewriting has left standing,
   which the tactic cannot: it is asked about the goal's subterms with
   the assumptions as its context. *)
val _ =
  check
    ("ORDER_ss decides an atom in a simplifier context",
     fn () =>
       let
         val ss = simpLib.++ (boolSimps.bool_ss, ORDER_ss)
         val goal =
           ``!le a b c.
               relation$WeakLinearOrder le ==>
               le a b /\ le b c ==> le a c``
       in
         List.null
           (Lib.fst (Tactical.VALID
                   (Tactical.THEN
                      (Tactical.REPEAT Tactic.STRIP_TAC,
                       simpLib.ASM_SIMP_TAC ss []))
                   ([], goal) (Context.snapshot())))
       end)

val _ =
  check
    ("budgeted ORDER reducer charges its nested graph search",
     fn () =>
       let
         val goal =
           ``!le a b c.
               relation$WeakLinearOrder le ==>
               le a b /\ le b c ==> le a c``
         val ctxt = Context.snapshot ()
         fun run budget =
           Tactical.VALID
             (Tactical.THEN
                (Tactical.REPEAT Tactic.STRIP_TAC,
                 simpLib.ASM_SIMP_TAC
                   (simpLib.++
                     (boolSimps.bool_ss,
                      ORDER_ss_budgeted budget)) []))
             ([], goal) ctxt
         val funded = searchBudget.unbounded ()
         val (remaining, validation) = run funded
         val _ = validation []
         val used = searchBudget.usage funded
         val zero =
           searchBudget.create
             {candidates = SOME 0, applications = NONE,
              normalization = NONE}
         val cutoff =
           ((ignore (run zero); false)
            handle searchBudget.LimitReached
                     (searchBudget.Candidate, usage) =>
                     #candidates usage = 0
                 | _ => false)
       in
         null remaining andalso #candidates used > 0 andalso cutoff
       end)

val _ =
  check
    ("ORDER_ext_ss lifts context collection and budget cutoffs",
     fn () =>
       let
         val goal =
           ``!le a b c.
               relation$WeakLinearOrder le ==>
               le a b /\ le b c ==> le a c``
         fun run fragment =
           let
             val ss = simpExtLib.++ (simpExtLib.lift_simpset boolSimps.bool_ss, fragment)
             val (remaining, validation) =
               Tactical.VALID
                 (Tactical.THEN
                    (Tactical.REPEAT Tactic.STRIP_TAC,
                     simpExtLib.ASM_SIMP_TAC ss []))
                 ([], goal) (Context.snapshot ())
           in
             if null remaining then (ignore (validation []); true)
             else false
           end
         val funded = searchBudget.unbounded ()
         val zero =
           searchBudget.create
             {candidates = SOME 0, applications = NONE,
              normalization = NONE}
         val ordinary_lift = run ORDER_ext_ss
         val budgeted_lift = run (ORDER_ext_ss_budgeted funded)
         val cutoff =
           ((ignore (run (ORDER_ext_ss_budgeted zero)); false)
            handle searchBudget.LimitReached
                     (searchBudget.Candidate, usage) =>
                     #candidates usage = 0
                 | _ => false)
       in
         ordinary_lift andalso budgeted_lift andalso
         #candidates (searchBudget.usage funded) > 0 andalso cutoff
       end)
