(* Task42: bag counts, guards, declaration identity and local admission. *)
structure SmtReplayBagTests =
struct
  open HolKernel Parse boolLib bossLib bagTheory
  structure H = SmtReplayArithmeticTests
  structure G = SmtReplayGraph
  structure A = SmtReplayArithmetic
  structure ZR = Z3_GraphProofReplay
  val limit = H.limit
  val require = H.require
  val with_graph = H.with_graph
  val import = H.import

  fun exact term hypotheses theorem =
    (H.exact term hypotheses theorem;
     require "bag theorem acquired axiom tags"
       (null (Tag.axioms_of (Thm.tag theorem))))
  fun same_tags expected actual =
    let val left = Tag.dest_tag (Thm.tag expected)
        val right = Tag.dest_tag (Thm.tag actual)
    in require ("bag full tags changed: " ^ String.concatWith "," (#1 left) ^
      " / " ^ String.concatWith "," (#1 right)) (left=right) end
  fun declines action =
    (case action () of NONE => true | SOME _ => false)
    handle Conv.UNCHANGED => true
      | HolSatLib.SAT_cex _ => true
      | Feedback.HOL_ERR detail =>
          if SmtResource.is_resource_gate detail then
            raise Feedback.HOL_ERR detail
          else true
  fun prove admit =
    SmtBagProve.bag_prove_with_admission admit intLib.ARITH_PROVE
  fun shape source named =
    let val (substitution,types) = Term.match_term source named
    in require "bag operator, count, element, guard or Type was hidden"
      (null types andalso List.all
        (fn {residue,...} => Term.is_var residue) substitution)
    end

  (* Native positive first: transport must not enlarge the bag portfolio.
     Use schematic elements, counts and predicates, not ground enumeration. *)
  val schemas =
    [(``BAG_IN (x:'a) b = (1 <= b x)``, ``b:'a -> num``),
     (``BAG_INN (x:'a) n b = (n <= b x)``, ``b:'a -> num``),
     (``BAG_INSERT (x:'a) b y =
          (if y = x then b x + 1 else b y)``, ``BAG_INSERT (x:'a) b``),
     (``BAG_UNION (b:'a -> num) c x = b x + c x``,
       ``BAG_UNION (b:'a -> num) c``),
     (``BAG_DIFF (b:'a -> num) c x = b x - c x``,
       ``BAG_DIFF (b:'a -> num) c``),
     (``BAG_MERGE (b:'a -> num) c x =
          (if b x < c x then c x else b x)``,
       ``BAG_MERGE (b:'a -> num) c``),
     (``BAG_INTER (b:'a -> num) c x =
          (if b x < c x then b x else c x)``,
       ``BAG_INTER (b:'a -> num) c``),
     (``SUB_BAG (b:'a -> num) b = T``, ``b:'a -> num``),
     (``(EMPTY_BAG:'a -> num) x = 0``, ``EMPTY_BAG:'a -> num``),
     (``BAG_CARD (BAG_INSERT (x:'a) EMPTY_BAG) = 1``,
       ``BAG_INSERT (x:'a) EMPTY_BAG``),
     (``BAG_FILTER P (b:'a -> num) x = (if P x then b x else 0)``,
       ``BAG_FILTER P (b:'a -> num)``),
     (``BAG_IMAGE (f:'a -> 'b) EMPTY_BAG = EMPTY_BAG``,
       ``BAG_IMAGE (f:'a -> 'b) EMPTY_BAG``),
     (``ITBAG (f:'a -> 'b -> 'b) EMPTY_BAG a = a``,
       ``ITBAG (f:'a -> 'b -> 'b) EMPTY_BAG a``),
     (``(b:'a -> num) <> EMPTY_BAG ==> BAG_IN (BAG_CHOICE b) b``,
       ``BAG_CHOICE (b:'a -> num)``),
     (``BAG_EVERY P (BAG_INSERT (x:'a) b) = (P x /\ BAG_EVERY P b)``,
       ``BAG_INSERT (x:'a) b``),
     (``SET_OF_BAG (b:'a -> num) x = BAG_IN x b``,
       ``SET_OF_BAG (b:'a -> num)``),
     (``BAG_OF_SET (P:'a -> bool) x = (if P x then 1 else 0)``,
       ``BAG_OF_SET (P:'a -> bool)``)]

  fun schemas_and_sharing () = with_graph (fn graph => fn scope =>
    List.app (fn (original,operand) =>
      let
        val _ = testutils.tprint ("bag schema " ^ term_to_string original)
        val native = SmtBagProve.bag_prove original
        val _ = exact original [] native
        val goal = import graph scope original
        val shared = import graph scope operand
        val calls = ref 0
        val result = A.prove_bounded_variables_admitted graph scope
          {inputs=[goal,goal,shared,shared],template_limit=limit,
           observe=fn _ => (),procedure=fn admit => fn terms =>
             case terms of [left,right,child,again] =>
               (calls := !calls+1;
                require "shared bag roots were copied"
                  (Portable.pointer_eq (left,right) andalso
                   Portable.pointer_eq (child,again));
                shape original left;shape operand child;
                require "source variables reached bag worker"
                  (H.disjoint [original,operand] terms);
                require "bag shared child lost worker identity"
                  (Portable.pointer_eq
                    (HolKernel.find_term (fn tm => tm ~~ child) left,child));
                prove admit left)
             | _ => raise Fail "bag schema arity"}
      in require "bag worker was retried or bypassed" (!calls=1);
         exact original [] (#theorem result);
         same_tags native (#theorem result);testutils.OK () end) schemas)

  val bads =
    [``BAG_INSERT (x:'a) b x = b x``,
     ``BAG_INN (x:'a) (b x + 1) b``,
     ``BAG_UNION (b:'a -> num) b x = b x``,
     ``BAG_DIFF (b:'a -> num) b x = b x + 1``,
     ``BAG_FILTER P (b:'a -> num) x = b x``,
     ``BAG_INSERT (x:'a) b y = b y + 1``,
     ``BAG_OF_SET (P:'a -> bool) x = 1``,
     ``BAG_EVERY P (BAG_INSERT (x:'a) EMPTY_BAG)``]
  fun false_obligations () = with_graph (fn graph => fn scope =>
    List.app (fn goal => require "false named bag obligation accepted"
      (declines (fn () => SOME (A.prove_bounded_variables_admitted graph scope
        {inputs=[import graph scope goal],template_limit=limit,
         observe=fn _ => (),procedure=fn admit => fn [term] =>
           prove admit term | _ => raise Fail "false bag arity"})))) bads)

  (* The guard belongs to the original Int-valued count, not to its Num
     image (which is nonnegative regardless of the original sign). Keep
     the native BAG_INSERT visible to the bag recognizer as well. *)
  fun int_bag_guards () = with_graph (fn graph => fn scope =>
    let
      val positives =
        [``0 <= (counts:'a -> int) x ==>
            (&(BAG_INSERT (x:'a) (\y. Num (counts y)) x):int) =
              counts x + 1``,
         ``0 <= (counts:'a -> int) x ==>
            (BAG_INSERT (x:'a) (\y. Num (counts y)) x =
               Num (counts x) + 1) /\
            ((&(Num (counts x)):int) = counts x)``]
      val negatives =
        [``(&(BAG_INSERT (x:'a) (\y. Num ((counts:'a -> int) y)) x):int) =
              counts x + 1``,
         ``(BAG_INSERT (x:'a) (\y. Num ((counts:'a -> int) y)) x =
               Num (counts x) + 1) /\
            ((&(Num (counts x)):int) = counts x)``,
         ``0 <= (counts:'a -> int) y ==>
            (&(BAG_INSERT (x:'a) (\z. Num (counts z)) x):int) =
              counts x + 1``]
      fun named goal = A.prove_bounded_variables_admitted graph scope
        {inputs=[import graph scope goal],template_limit=limit,
         observe=fn _ => (),procedure=fn admit => fn [term] =>
           (shape goal term;
            require "Int-bag source count or guard reached worker"
              (H.disjoint [goal] [term]);
            prove admit term)
           | _ => raise Fail "Int-bag guard arity"}
      fun positive goal =
        let val _ = testutils.tprint
              ("bag Int guard " ^ term_to_string goal)
            val native = SmtBagProve.bag_prove goal
            val _ = exact goal [] native
            val result = named goal
        in exact goal [] (#theorem result);
           same_tags native (#theorem result);testutils.OK () end
    in List.app positive positives;
       List.app (fn goal =>
         require "Int-bag guard was dropped or moved to another count"
           (declines (fn () => SOME (named goal)))) negatives
    end)

  (* Existing small Z3 map-add shapes: symbolic select and pointwise store.
     These are Int arrays, not arbitrary lambdas classified as native bags. *)
  fun int_array_maps () =
    let
      val select =
        ``(\i:int. (a:int -> int) i + (b:int -> int) i) array_map_x =
            a array_map_x + b array_map_x``
      val store =
        ``(\i:int. ((3:int =+ x) (a:int -> int)) i +
           ((3:int =+ 3) (b:int -> int)) i) =
            (3 =+ x + 3) (\i:int. a i + b i)``
      val _ = with_graph (fn graph => fn scope => List.app (fn goal =>
        let
          val native = SmtBagProve.bag_prove goal
          val result = A.prove_bounded_variables_admitted graph scope
            {inputs=[import graph scope goal],template_limit=limit,
             observe=fn _ => (),procedure=fn admit => fn [term] =>
               (shape goal term;
                require "Int-array source variables reached bag worker"
                  (H.disjoint [goal] [term]);prove admit term)
               | _ => raise Fail "Int-array bag arity"}
        in exact goal [] native;exact goal [] (#theorem result);
           same_tags native (#theorem result) end) [select,store])
    in () end

  val premise = ``(x:'a) = y``
  val contextual_goal = ``BAG_INSERT (x:'a) b = BAG_INSERT y b``
  fun contextual () = with_graph (fn graph => fn scope =>
    let
      val native = SmtBagProve.bag_contextual_prove_with_admission
        (A.new_term_check {limit=limit,observe=fn () => ()})
        [premise] contextual_goal
      val _ = exact contextual_goal [premise] native
      val result = A.prove_bounded_variables_admitted graph scope
        {inputs=map (import graph scope) [contextual_goal,premise],
         template_limit=limit,observe=fn _ => (),
         procedure=fn admit => fn [target,assumption] =>
           let val _ = require "bag context source variables reached worker"
                 (H.disjoint [contextual_goal,premise] [target,assumption])
               val theorem =
                 SmtBagProve.bag_contextual_prove_with_admission
                   admit [assumption] target
           in exact target [assumption] theorem;
              Thm.DISCH assumption theorem end
           | _ => raise Fail "bag context arity"}
      (* This guard is bound: contextual cases must not split it as a
         free assumption before simplification opens the quantifier. *)
      val bound_goal =
        ``!p:bool. (if p then EMPTY_BAG:bool -> num else EMPTY_BAG) =
                    EMPTY_BAG``
      val bound_native = SmtBagProve.bag_contextual_prove_with_admission
        (A.new_term_check {limit=limit,observe=fn () => ()}) [] bound_goal
      val bound_result = A.prove_bounded_variables_admitted graph scope
        {inputs=[import graph scope bound_goal],template_limit=limit,
         observe=fn _ => (),procedure=fn admit => fn [target] =>
           let val theorem =
                 SmtBagProve.bag_contextual_prove_with_admission
                   admit [] target
           in exact target [] theorem;theorem end
           | _ => raise Fail "bound bag context arity"}
    in exact (boolSyntax.mk_imp (premise,contextual_goal)) []
         (#theorem result);same_tags native (#theorem result);
       exact bound_goal [] bound_native;
       exact bound_goal [] (#theorem bound_result);
       same_tags bound_native (#theorem bound_result) end)

  fun cpc_worker name admit term =
    let val located = {term=term,provenance=
          CPC_Proof.UnavailableProvenance "bag identity"}
        val step:CPC_Proof.step =
          {id="@bag",rule=valOf (CPC_Proof.lookup_rule "1.3.4" name),
           premises=[],conclusion=SOME located,args=[located]}
    in #1 (CPC_ProofReplay.graph_bounded_worker_with_admission
      admit [] (step,[])) end

  (* Complete generic CPC assembly checks exact Source Goal/Hyp, argument
     roles, source disjointness and one selected callback in the helper. *)
  fun cpc_cases () =
    let
      fun check goal assumptions name args declared =
        let val native = if name="eq-symm" then
              CPC_ProofReplay.replay_rare_rewrite_for_test name args
            else if null assumptions then SmtBagProve.bag_prove goal
            else SmtBagProve.bag_contextual_prove_with_admission
              (A.new_term_check {limit=limit,observe=fn () => ()})
              assumptions goal
        in H.cpc_arguments_using_admitted limit
          (fn admit => fn input =>
            let val result as (theorem,_) =
                  CPC_ProofReplay.graph_bounded_worker_with_admission
                    admit [] input
            in same_tags native theorem;
               require "CPC bag worker acquired axioms"
                 (null (Tag.axioms_of (Thm.tag theorem)));result end)
          goal assumptions name (map H.Object args) declared end
        handle error => raise Fail ("CPC " ^ term_to_string goal ^ ": " ^
          General.exnMessage error)
      (* The helper records atomic clause boundaries. Nested Boolean source
         syntax is checked through the same named TRUST worker separately,
         not falsely recorded as a single atomic occurrence. *)
      fun atomic goal = not (boolSyntax.is_imp_only goal) andalso
        not (Lib.can (HolKernel.find_term boolSyntax.is_conj) goal)
      val _ = with_graph (fn graph => fn scope => List.app
        (fn (goal,_) =>
          let val result = A.prove_bounded_variables_admitted graph scope
                {inputs=[import graph scope goal],template_limit=limit,
                 observe=fn _ => (),procedure=fn admit => fn [term] =>
                   cpc_worker "trust" admit term
                   | _ => raise Fail "Boolean bag TRUST arity"}
          in exact goal [] (#theorem result) end)
        (List.filter (fn (goal,_) => not (atomic goal)) schemas))
      val _ = List.app (fn (goal,_) => List.app
        (check goal [] "trust" [goal]) [true,false])
        (List.filter (fn (goal,_) => atomic goal) schemas)
      val _ = List.app (check contextual_goal
        [premise,``bag_unused:bool``] "trust" [contextual_goal]) [true,false]
      val left = ``BAG_INSERT (x:'a) b``
      val right = ``c:'a -> num``
      val symmetry = boolSyntax.mk_eq
        (boolSyntax.mk_eq (left,right),boolSyntax.mk_eq (right,left))
      val _ = List.app (check symmetry [] "eq-symm" [left,right])
        [true,false]
    in List.app (fn bad => require "CPC TRUST accepted false bag law"
      (declines (fn () =>
        (H.cpc_arguments_using_admitted limit
          (fn admit => CPC_ProofReplay.graph_bounded_worker_with_admission
            admit []) bad [] "trust" [H.Object bad] true;SOME ()))))
      (List.take (bads,2)) end

  (* Exercise public compact TRUST classification with no numeric operand.
     The bad endpoint prints exactly like the native reflexive bag equation,
     but its right-hand singleton uses a different graph declaration. *)
  fun compact_trust_identity () =
    let
      fun check different = with_graph (fn graph => fn scope =>
        let
          val goal = ``BAG_INSERT (bag_compact_identity:'a) EMPTY_BAG =
                         BAG_INSERT bag_compact_identity EMPTY_BAG``
          val unused = ``bag_compact_unused:bool``
          val sources = SmtReplaySource.new graph scope limit
            {goal=goal,assumptions=[unused]}
          val good = #node (SmtReplaySource.goal_source sources)
          val other = G.variable graph scope G.Generated
            ``bag_compact_identity:'a``
          val insert = G.constant graph scope
            (#1 (boolSyntax.strip_comb
              ``BAG_INSERT (bag_compact_identity:'a) EMPTY_BAG``))
          val empty = import graph scope ``EMPTY_BAG:'a -> num``
          val right = G.application graph scope
            (G.application graph scope (insert,other),empty)
          val equality = G.constant graph scope
            (Term.rator (Term.rator goal))
          val operands = valOf
            (SmtReplayRules.operands graph boolSyntax.equality 2 good)
          val bad = G.application graph scope
            (G.application graph scope (equality,hd operands),right)
          val _ = require "compact bag TRUST needs same-native distinct IDs"
            (good <> bad andalso G.representative graph bad ~~ goal)
          val _ = require "compact bag TRUST acquired a numeric operand"
            (not (A.has_numeric_operand graph scope
              {inputs=[good,bad],observe=fn () => ()}))
          val target = if different then bad else good
          fun located node:SmtLib_GraphFrontend.term =
            {node=node,scope=scope,binder_blocks=[],source_syntax=NONE,
             occurrence=SmtLib_Parser.ConstructionOccurrence
               {value=node,role=SmtLib_Parser.ConstructionAtom,
                token="bag-trust",children=[]}}
          fun registered name = valOf (CPC_Proof.lookup_rule "1.3.4" name)
          val proof:CPC_ProofParser.graph_proof =
            {cvc_version="1.3.4",commands=
              [CPC_ProofParser.GraphAssume ("@denied",located
                 (SmtReplaySource.denied_goal_node sources)),
               CPC_ProofParser.GraphStep {pop=false,step=
                 {id="@bag",rule=registered "trust",premises=[],
                  conclusion=SOME (located target),
                  args=[CPC_ProofParser.GraphTerm (located target)],
                  raw_conclusion=NONE,raw_args=[]}},
               CPC_ProofParser.GraphStep {pop=false,step=
                 {id="@done",rule=registered "resolution",
                  premises=["@bag","@denied"],
                  conclusion=SOME (located
                    (G.constant graph scope boolSyntax.F)),
                  args=[],raw_conclusion=NONE,raw_args=[]}}]}
          fun replay () = CPC_ProofReplay.prove_graph_proof
            {graph=graph,scope=scope,sources=sources,proof=proof}
          val _ = testutils.tprint
            ("bag compact TRUST different-ID=" ^ Bool.toString different)
        in if different then
             (require "compact bag TRUST merged distinct declaration IDs"
                (declines (fn () => SOME (replay ())));testutils.OK ())
           else let val theorem = replay ()
                in exact goal [unused] theorem;
                   same_tags (SmtBagProve.bag_prove goal) theorem;
                   testutils.OK () end
        end)
    in check false;check true end

  (* Equal native spellings are NOT graph declaration identity. In
     particular INSERT has a schematic element and NO numeric result node. *)
  fun graph_handlers () = with_graph (fn graph => fn scope =>
    let
      fun apply tm args = List.foldl (fn (x,f) =>
        G.application graph scope (f,x)) (G.constant graph scope tm) args
      fun head tm = #1 (boolSyntax.strip_comb tm)
      fun eq x y = apply (head (boolSyntax.mk_eq
        (G.representative graph x,G.representative graph y))) [x,y]
      val x = ``bag_identity:'a``
      val left = G.variable graph scope G.RigidSource x
      val right = G.variable graph scope G.Generated x
      val b = ``bag_identity_b:'a -> num``
      val source = G.variable graph scope G.RigidSource b
      val other = G.variable graph scope G.Generated b
      val _ = require "bag identity fixture lost distinct IDs"
        (left <> right andalso source <> other andalso
         G.representative graph left ~~ G.representative graph right andalso
         G.representative graph source ~~ G.representative graph other)
      val empty = import graph scope ``EMPTY_BAG:'a -> num``
      fun insert x b = apply (head ``BAG_INSERT (x:'a) b``) [x,b]
      val y = import graph scope ``bag_identity_y:'a``
      val joined = apply (head ``BAG_UNION (b:'a -> num) c``)
        [empty,source]
      val inserted = insert left empty
      val good_insert = eq inserted inserted
      val bad_insert = eq inserted (insert right empty)
      val _ = require "INSERT identity control acquired numeric operands"
        (not (A.has_numeric_operand graph scope
          {inputs=[good_insert,bad_insert],observe=fn () => ()}))
      val count_x = G.application graph scope (source,left)
      val count_y = G.application graph scope (source,y)
      val successor = apply (head ``(n:num) + 1``)
        [count_x,import graph scope ``1:num``]
      fun branch element = apply (head ``if p then (m:num) else n``)
        [eq y element,successor,count_y]
      val count = G.application graph scope (insert left source,y)
      val cases = [(eq joined source,eq joined other),
                   (good_insert,bad_insert),
                   (eq count (branch left),eq count (branch right))]
      val proof:Z3_GraphProofParser.proof =
        {steps=Redblackmap.mkDict Z3_GraphProofParser.compare_id,
         root=Z3_GraphProofParser.Anonymous 0,vars=[],
         z3_version="4.15.3",close=fn () => ()}
      fun request name target : ZR.local_request =
        {rule=valOf (Z3_Proof.lookup_rule "4.15.3" name),
         metadata=if name="rewrite" then NONE else SOME
           (Z3_Proof.mk_th_lemma_metadata
             (if name="th-lemma-array" then "array" else "arith",NONE,[])),
         target=target,premises=[],arguments=[],law=target}
      fun compatibility request = Option.map
        (fn theorem => {definitions=[],theorem=theorem})
        (Z3_ProofReplay.graph_bounded_local_law graph [] proof request)
      fun recorded request =
        Z3_ProofReplay.graph_bounded_recorded_local_law
          graph scope limit [] proof request
      fun check produce name (good,bad) =
        let val original = G.representative graph good
            val _ = testutils.tprint ("bag graph " ^ name ^ " " ^
              term_to_string original)
            val native = SmtBagProve.bag_prove original
            val _ = require "bad bag law changed native spelling"
              (G.representative graph bad ~~ original andalso good <> bad)
            val _ = case produce (request name good) of
                NONE => raise Fail ("valid Z3 bag law declined: " ^ name)
              | SOME {definitions,theorem} =>
                  (require "Z3 bag law invented definitions" (null definitions);
                   exact original [] theorem;same_tags native theorem)
        in require ("Z3 bag route merged IDs: " ^ name)
          (declines (fn () => produce (request name bad)));testutils.OK () end
      fun cpc target = #theorem (A.prove_bounded_variables_admitted graph scope
        {inputs=[target],template_limit=limit,observe=fn _ => (),
         procedure=fn admit => fn [term] => cpc_worker "trust" admit term
           | _ => raise Fail "bag identity arity"})
      val _ = List.app (fn produce => List.app (fn name =>
        List.app (check produce name) cases)
          ["rewrite","th-lemma-array","th-lemma-arith"])
        [compatibility,recorded]
    in List.app (fn (good,bad) =>
      (exact (G.representative graph good) [] (cpc good);
       require "CPC bag worker merged IDs"
         (declines (fn () => SOME (cpc bad))))) cases end)

  (* Reject a selected rewrite, not merely the entry goal. An ordinary
     HOL_ERR must stay terminal through simp/pointwise/arith and consumers. *)
  fun admission_errors () =
    let
      val goal = #1 (List.nth (schemas,2))
      val fact = Thm.concl bagTheory.BAG_INSERT
      fun check_on goal fact label reject worker =
        let val _ = testutils.tprint ("bag admission " ^ label)
            val stopped = ref false
            val after = ref 0
            val fact_accepted = ref false
            val genuine = A.new_term_check
              {limit=limit,observe=fn () => ()}
            fun admit tm =
              if !stopped then (after := !after+1;genuine tm)
              else if reject tm then
                (stopped := true;raise Feedback.mk_HOL_ERR
                  "Task42Bag" "rewrite" "first error")
              else (if tm ~~ fact then fact_accepted := true else ();
                    genuine tm)
            val result = Exn.capture (fn () => worker admit goal) ()
            val preserved = case result of
                Exn.Exn (Feedback.HOL_ERR detail) =>
                  Feedback.top_structure_of detail = "Task42Bag" andalso
                  Feedback.top_function_of detail = "rewrite" andalso
                  Feedback.message_of detail = "first error"
              | _ => false
            val _ = require (label ^ ": bag admission swallowed or retried" ^
              " (stopped=" ^ Bool.toString (!stopped) ^ ", after=" ^
              Int.toString (!after) ^ ", preserved=" ^
              Bool.toString preserved ^ ")")
              (!stopped andalso !after=0 andalso preserved)
            val _ = require (label ^ ": generic bag law was not accepted")
              (reject fact orelse !fact_accepted)
            (* A failed callback must not poison the next invocation. Use
               the real bounded admission check, not an accepting stub. *)
            val theorem = worker genuine goal
        in exact goal [] theorem;testutils.OK () end
      fun z3 recorded name admit term =
        let val metadata = if name="rewrite" then NONE else SOME
              (Z3_Proof.mk_th_lemma_metadata ("array",NONE,[]))
            val pt = Z3_ProofReplay.graph_local_proofterm
              (valOf (Z3_Proof.lookup_rule "4.15.3" name)) metadata term [] []
            val proof = Z3_Proof.mk_proof
              (Redblackmap.insert (Redblackmap.mkDict Int.compare,0,pt),
               Term.empty_tmset,[],"4.15.3")
        in if recorded then #theorem
          (Z3_ProofReplay.replay_root_with_definition_occurrences_admitted
            admit [] proof)
        else Z3_ProofReplay.replay_root_admitted admit [] proof end
      val check = check_on goal fact
      (* Keep the source-law rejection, and independently reject a root
         abstraction in prospective INSERT instantiation (its RHS), after
         accepting the generic equation. Neither failure may reach a later
         admission callback or poison the next invocation. *)
      val _ = List.app (fn (phase,reject) =>
        (check (phase ^ " native") reject prove;
         check (phase ^ " CPC TRUST") reject (cpc_worker "trust");
         List.app (fn recorded => List.app (fn name =>
           check (phase ^ " Z3 " ^ name) reject (z3 recorded name))
           ["rewrite","th-lemma-array"]) [false,true]))
        [("source rewrite",fn tm => tm ~~ fact),
         ("instantiated rewrite",Term.is_abs)]
      (* HO_PART_MATCH beta-reduces flexible function occurrences after
         INST. Its duplicated argument must be forecast as well, not only
         the smaller pre-beta lambda application. *)
      val beta_goal =
        ``BAG_FILTER (\v:bool. (v,v) = bag_beta_pair) b bag_beta_x =
            (if (bag_beta_x,bag_beta_x) = bag_beta_pair
             then b bag_beta_x else 0)``
      fun beta_result tm =
        let val (left,right) = boolSyntax.dest_eq tm
            val (x,y) = pairSyntax.dest_pair left
        in Term.is_var right andalso Term.is_var x andalso
           Term.type_of x = Type.bool andalso Term.aconv x y end
        handle Feedback.HOL_ERR _ => false
      val beta_fact = Thm.concl bagTheory.BAG_FILTER_DEF
      val beta_check = check_on beta_goal beta_fact
        "higher-order beta rewrite" beta_result
      val _ = beta_check prove
      val _ = beta_check (cpc_worker "trust")
      exception ContextPrimary
      val calls = ref 0
      val result = Exn.capture (fn () =>
        SmtBagProve.bag_contextual_prove_with_admission
          (fn tm => (calls := !calls+1;
            if tm ~~ premise then raise ContextPrimary else ()))
          [premise] contextual_goal) ()
      val _ = require "contextual bag admission swallowed its first error"
        (!calls=2 andalso
         (case result of Exn.Exn ContextPrimary => true | _ => false))
      val recovered = SmtBagProve.bag_contextual_prove_with_admission
        (A.new_term_check {limit=limit,observe=fn () => ()})
        [premise] contextual_goal
    in exact contextual_goal [premise] recovered end

  (* A two-function rule must forecast its selective beta phases in native
     match order. In particular b e -> 0 must not hide the later P e path.
     Arm at the inner predicate result, then reject the WHOLE rebuilt binder
     before conversion. Rejecting only the final conversion would let the
     old silently rolled-back forecast pass this test. *)
  fun prospective_betas () =
    let
      val target =
        ``BAG_FILTER (\v:bool. (v,v) = bag_beta_pair) (\v:bool. 0)
            bag_beta_x =
          (if (bag_beta_x,bag_beta_x) = bag_beta_pair then 0 else 0)``
      val final =
        ``\e:bool. if (e,e) = bag_beta_pair then (0:num) else 0``
      fun predicate tm =
        let val (l,r) = boolSyntax.dest_eq tm
            val (x,y) = pairSyntax.dest_pair l
        in r ~~ ``bag_beta_pair:bool # bool`` andalso
           Term.is_var x andalso x ~~ y end
        handle Feedback.HOL_ERR _ => false
      exception Primary
      exception RolledBack
      fun multi label worker =
        let val _ = testutils.tprint ("bag prospective phases " ^ label)
            val armed = ref false val stopped = ref false val after = ref 0
            val genuine = A.new_term_check
              {limit=limit,observe=fn () => ()}
            fun check tm =
              if !stopped then (after := !after+1;genuine tm)
              else if !armed andalso Term.is_abs tm then
                (stopped := true;
                 if tm ~~ final then raise Primary else raise RolledBack)
              else (genuine tm;if predicate tm then armed := true else ())
            val result = Exn.capture (worker check) target
        in require "later beta phase was rolled back or admitted too late"
             (!armed andalso !stopped andalso !after=0 andalso
              (case result of Exn.Exn Primary => true | _ => false));
           exact target [] (worker genuine target);testutils.OK () end
      val _ = multi "native" prove
      val _ = multi "CPC TRUST" (cpc_worker "trust")
      (* These tuples are prospective pair-map intermediates, absent from
         both the input and native conversion result. A callback-free
         contextual worker returns without ever admitting either one. *)
      val assumption = ``BAG_IN (ctx_x:bool) ctx_b``
      val contextual_target =
        ``(bag_consumer:num # bool -> num)
            (((\v:num. (0:num)) ## (\v:bool. (v,v) = bag_beta_pair))
              (cx,cy)) = bag_consumer (0,(cy,cy)=bag_beta_pair) /\
          BAG_IN (ctx_x:bool) ctx_b``
      val intermediates =
        [``((\v:num. (0:num)) cx,(\v:bool. (v,v) = bag_beta_pair) cy)``,
         ``((\v:num. (0:num)) cx,(cy:bool,cy)=bag_beta_pair)``]
      fun contextual intermediate =
        let val _ = testutils.tprint "bag prospective contextual beta"
            val stopped = ref false val after = ref 0
            val genuine = A.new_term_check
              {limit=limit,observe=fn () => ()}
            fun check tm =
              if !stopped then (after := !after+1;genuine tm)
              else if tm ~~ intermediate then
                (stopped := true;raise Primary)
              else genuine tm
            fun worker admit =
              SmtBagProve.bag_contextual_prove_with_admission
                admit [assumption] contextual_target
            val result = Exn.capture worker check
            val native = worker genuine
        in require "contextual native beta preceded prospective admission"
             (!stopped andalso !after=0 andalso
              (case result of Exn.Exn Primary => true | _ => false));
           exact contextual_target [assumption] native;testutils.OK () end
    in List.app contextual intermediates end

  fun shared_element depth =
    let
      val combine = ``bag_combine:bool -> bool -> bool``
      fun shared 0 = ``bag_leaf:bool``
        | shared n = let val child = shared (n-1)
                     in Term.list_mk_comb (combine,[child,child]) end
    in shared depth end

  (* Context rules are not exported srw rules. Reject an instantiated RHS
     absent from the input AND the final native result, before that rewrite
     can run. Exercise both a scoped Bag conjunction and a bare context
     consequence, plus congruence-local assumptions. *)
  fun prospective_context () =
    let
      val facts = [``!z:bool. (bag_h:bool -> bool) z = bag_g z z``,
                   ``!u v:bool. (bag_g:bool -> bool -> bool) u v``]
      val premise = ``BAG_IN (ctx_x:bool) ctx_b``
      fun target arg bag =
        let val result = Term.mk_comb (``bag_h:bool -> bool``,arg)
        in if bag then boolSyntax.mk_conj (result,premise) else result end
      exception Primary
      fun check bag =
        let val _ = testutils.tprint "bag prospective assumption rewrite"
            val arg = shared_element 15
            val expanded = Term.list_mk_comb
              (``bag_g:bool -> bool -> bool``,[arg,arg])
            val goal = target arg bag
            val context = if bag then facts @ [premise] else facts
            val expanding = if bag then [hd facts,premise] else [hd facts]
            val stopped = ref false val after = ref 0
            val genuine = A.new_term_check
              {limit=200000,observe=fn () => ()}
            fun admit tm =
              if !stopped then (after := !after+1;genuine tm)
              else if tm ~~ expanded then
                (stopped := true;raise Primary)
              else genuine tm
            val _ = require "context expansion fixtures changed"
              (Term.term_size goal < 200000 andalso
               Term.term_size expanded > 200000)
            val result = Exn.capture (fn () =>
              SmtBagProve.bag_contextual_prove_with_admission
                admit expanding goal) ()
            val _ = require ("context RHS was not admitted prospectively: " ^
              Bool.toString (!stopped) ^ "/" ^ Int.toString (!after) ^
              (case result of Exn.Res _ => " returned"
               | Exn.Exn Primary => " primary"
               | Exn.Exn _ => " wrong exception"))
              (!stopped andalso !after=0 andalso
               (case result of Exn.Exn Primary => true | _ => false))
            val cutoff = Exn.capture (fn () =>
              SmtBagProve.bag_contextual_prove_with_admission
                genuine expanding goal) ()
            val _ = require "oversized assumption RHS bypassed admission"
              (case cutoff of Exn.Exn (Feedback.HOL_ERR detail) =>
                Feedback.top_structure_of detail = "SmtReplayArithmetic"
                | _ => false)
            (* The complete context DOES prove the fitting large goal.
               Compose its compact laws rather than refusing a needless
               oversized intermediate. Compare all actual dependencies
               and tags against the original contextual tactic. *)
            val theorem = SmtBagProve.bag_contextual_prove_with_admission
              genuine context goal
            val native = Tactical.TAC_PROOF ((context,goal),
              Tactical.THEN (bossLib.FULL_SIMP_TAC (bossLib.srw_ss()) [],
                intLib.ARITH_TAC))
        in exact goal context theorem;same_tags native theorem;
           require "context composition changed actual Hyp"
             (HOLset.equal (Thm.hypset native,Thm.hypset theorem));
           testutils.OK () end
      val _ = List.app check [false,true]
      fun compatibility depth fixed universal shape =
        let val _ = testutils.tprint "bag contextual source priority/freshness"
            val arg = shared_element depth
            val z = ``z:bool``
            val law = if shape then
                ``!u v w:bool. (bag_g:bool -> bool -> bool)
                    ((bag_combine:bool -> bool -> bool) u v) w``
              else if fixed then boolSyntax.mk_forall (z,
                Term.list_mk_comb (``bag_g:bool -> bool -> bool``,[arg,z]))
              else ``(bag_g:bool -> bool -> bool) z z``
            val context = [hd facts,law] @
              (if universal then [List.nth (facts,1)] else [])
            val goal = target arg false
            val genuine = A.new_term_check
              {limit=200000,observe=fn () => ()}
            val actual = SmtBagProve.bag_contextual_prove_with_admission
              genuine context goal
            val native = Tactical.TAC_PROOF ((context,goal),
              Tactical.THEN (bossLib.FULL_SIMP_TAC (bossLib.srw_ss()) [],
                intLib.ARITH_TAC))
        in exact goal (Thm.hyp native) actual;same_tags native actual;
           testutils.OK () end
      val _ = compatibility 6 false true false
      val _ = compatibility 6 true true false
      val _ = compatibility 15 true true false
      val _ = compatibility 15 true false false
      val _ = compatibility 15 false false true
      fun terminal label reject context goal =
        let val _ = testutils.tprint ("bag contextual terminal " ^ label)
            val stopped = ref false val after = ref 0
            val genuine = A.new_term_check
              {limit=200000,observe=fn () => ()}
            fun admit tm =
              if !stopped then (after := !after+1;genuine tm)
              else if reject tm then
                (stopped := true;raise Feedback.mk_HOL_ERR
                  "Task42Context" label "first admission")
              else genuine tm
            val result = Exn.capture (fn () =>
              SmtBagProve.bag_contextual_prove_with_admission
                admit context goal) ()
        in require "contextual composition/guard error was retried"
             (!stopped andalso !after=0 andalso
              (case result of Exn.Exn (Feedback.HOL_ERR detail) =>
                 Feedback.top_structure_of detail = "Task42Context" andalso
                 Feedback.top_function_of detail = label andalso
                 Feedback.message_of detail = "first admission"
               | _ => false));
           let val actual = SmtBagProve.bag_contextual_prove_with_admission
                 genuine context goal
               val native = Tactical.TAC_PROOF ((context,goal),
                 bossLib.FULL_SIMP_TAC (bossLib.srw_ss()) [])
           in exact goal (Thm.hyp native) actual;same_tags native actual end;
           testutils.OK () end
      fun symbolic tm =
        case boolSyntax.strip_comb tm of (head,[x,y]) =>
          head ~~ ``bag_g:bool -> bool -> bool`` andalso
          Term.is_var x andalso x ~~ y
        | _ => false
      val _ = terminal "composition" symbolic facts
        (target (shared_element 6) false)
      val guard = boolSyntax.mk_eq (shared_element 14,shared_element 14)
      val empty = ``EMPTY_BAG:bool -> num``
      val _ = terminal "guard" (fn tm => tm ~~ guard) []
        (boolSyntax.mk_eq (boolSyntax.mk_cond
          (guard,empty,``bag_other:bool -> num``),empty))
      (* The hypothesis is introduced by implication congruence, not the
         top-level goal context. Its instantiated RHS must use the same
         dispatcher and preserve the first callback error. *)
      val local_rule = hd facts
      val arg = ``bag_local_x:bool``
      val rhs = ``(bag_g:bool -> bool -> bool) bag_local_x bag_local_x``
      val local_goal = boolSyntax.mk_imp
        (local_rule,boolSyntax.mk_eq (target arg false,rhs))
      val seen = ref false
      val local_admit = A.new_term_check {limit=limit,observe=fn () => ()}
      val result = Exn.capture (fn () =>
        SmtBagProve.bag_contextual_prove_with_admission
          (fn tm => if tm ~~ rhs then (seen := true;raise Primary)
            else local_admit tm)
          [] local_goal) ()
    in require "congruence-local assumption escaped admission"
         (!seen andalso
          (case result of Exn.Exn Primary => true | _ => false));
       exact local_goal [] (SmtBagProve.bag_contextual_prove_with_admission
         (A.new_term_check {limit=limit,observe=fn () => ()}) [] local_goal)
    end

  (* Canonical context wrappers are not additional source operands. A
     fitting hypothesis must survive p=T import, whether retained or used.
     Lambda frontiers must expose structure without naming bound values. *)
  fun fitting_context () =
    let
      val memo = ref (Redblackmap.mkDict Int.compare)
      fun balanced leaves = case Redblackmap.peek (!memo,leaves) of
          SOME tm => tm
        | NONE =>
            let val tm = if leaves=1 then ``bag_ctx_leaf:bool`` else
                  Term.list_mk_comb (``bag_ctx_join:bool -> bool -> bool``,
                    [balanced (leaves div 2),
                     balanced (leaves-leaves div 2)])
            in memo := Redblackmap.insert (!memo,leaves,tm);tm end
      val near = balanced 50000
      val tiny = ``BAG_CARD (EMPTY_BAG:bool -> num) = 0``
      fun compare label context target =
        let val _ = testutils.tprint ("bag fitting context " ^ label)
            val native = Tactical.TAC_PROOF ((context,target),
              Tactical.THEN (bossLib.FULL_SIMP_TAC (bossLib.srw_ss()) [],
                intLib.ARITH_TAC))
            val actual = SmtBagProve.bag_contextual_prove_with_admission
              (A.new_term_check {limit=200000,observe=fn () => ()})
              context target
        in exact target (Thm.hyp native) actual;same_tags native actual;
           testutils.OK () end
      val _ = require "canonical context boundary fixture changed"
        (Term.term_size near=199997 andalso
         Term.term_size (boolSyntax.mk_eq (near,boolSyntax.T))=200001)
      val _ = compare "canonical retained" [near] tiny
      val _ = compare "canonical used" [near] near
      (* Component-wise admission must still visit the polymorphic
         equality operator annotation before constructing its conversion. *)
      exception Operator
      val operator_seen = ref false
      val operator_after = ref 0
      val operator_check = A.new_term_check
        {limit=200000,observe=fn () => ()}
      val operator_result = Exn.capture (fn () =>
        SmtBagProve.bag_contextual_prove_with_admission
          (fn tm => if !operator_seen then
              (operator_after := !operator_after+1;operator_check tm)
            else if tm ~~ Term.rator (Term.rator
                (boolSyntax.mk_eq (near,boolSyntax.T))) then
              (operator_seen := true;raise Operator)
            else operator_check tm) [near] tiny) ()
      val _ = require "canonical equation operator bypassed Type admission"
        (!operator_seen andalso !operator_after=0 andalso
         (case operator_result of Exn.Exn Operator => true | _ => false))
      val payload = balanced 32768
      val x = ``bag_ctx_x:bool``
      val k = ``bag_ctx_k:bool -> bool -> bool``
      val abstraction = Term.mk_abs (x,Term.list_mk_comb (k,[x,payload]))
      val h = ``bag_ctx_h:(bool -> bool) -> bool``
      val fact = ``BAG_IN bag_ctx_q (bag_ctx_b:bool -> num)``
      val laws =
        [``!f:bool -> bool. (bag_ctx_h:(bool -> bool) -> bool) f =
             (bag_ctx_g:(bool -> bool) -> (bool -> bool) -> bool) f f``,
         ``!v:bool. (bag_ctx_g:(bool -> bool) -> (bool -> bool) -> bool)
             (\x:bool. (bag_ctx_k:bool -> bool -> bool) x v)
             (\x:bool. (bag_ctx_k:bool -> bool -> bool) x v)``,fact]
      val target = boolSyntax.mk_conj (Term.mk_comb (h,abstraction),fact)
      val _ = require "lambda context fixture changed"
        (Term.term_size target=131084)
      val _ = compare "lambda" laws target
      (* Alpha names do not carry authority. Keep a free prime-name and
         multiple live binders in the abstraction, then require an actual
         structural context law to close the duplicated intermediate. *)
      val nested = Term.mk_abs (x,Term.mk_abs (``bag_ctx_x':bool``,
        Term.list_mk_comb (``bag_ctx_k2:bool -> bool -> bool -> bool``,
          [x,``bag_ctx_x':bool``,payload])))
      val nested_laws =
        [``!f:bool -> bool -> bool.
             (bag_ctx_h2:(bool -> bool -> bool) -> bool) f =
             (bag_ctx_g2:(bool -> bool -> bool) ->
                (bool -> bool -> bool) -> bool) f f``,
         ``!v:bool. (bag_ctx_g2:(bool -> bool -> bool) ->
                (bool -> bool -> bool) -> bool)
             (\a b:bool. (bag_ctx_k2:bool -> bool -> bool -> bool) a b v)
             (\a b:bool. (bag_ctx_k2:bool -> bool -> bool -> bool) a b v)``,
         fact]
      val nested_target = boolSyntax.mk_conj (Term.mk_comb
        (``bag_ctx_h2:(bool -> bool -> bool) -> bool``,nested),fact)
      val _ = compare "nested live binders" nested_laws nested_target
      (* A non-closing context still reaches prospective RHS admission;
         abstraction refinement is not permission to erase a false law. *)
      val stopped = ref false val after = ref 0
      exception Primary
      val expanded = Term.list_mk_comb
        (``bag_ctx_g:(bool -> bool) -> (bool -> bool) -> bool``,
         [abstraction,abstraction])
      val genuine = A.new_term_check {limit=200000,observe=fn () => ()}
      fun admit tm = if !stopped then (after := !after+1;genuine tm)
        else if tm ~~ expanded then (stopped := true;raise Primary)
        else genuine tm
      val result = Exn.capture (fn () =>
        SmtBagProve.bag_contextual_prove_with_admission admit
          [hd laws,fact] target) ()
    in require "lambda miss bypassed admission or retried first error"
         (!stopped andalso !after=0 andalso
          (case result of Exn.Exn Primary => true | _ => false));
       compare "lambda recovery" laws target
    end

  (* Unlike fitting_context's constant payload, these fields depend on
     the enclosing binders. Closing h f via g f f needs two frontiers:
     expose the lambda, then k; never instantiate the duplicated payload. *)
  fun dependent_context () =
    let
      val cap = 200000
      val x = ``bag_dep_x:bool``
      val n = ``bag_dep_n:num``
      val join = ``bag_dep_join:bool -> bool -> bool``
      fun shared leaf 0 = leaf
        | shared leaf depth =
            let val child = shared leaf (depth-1)
            in Term.list_mk_comb (join,[child,child]) end
      val k = ``bag_dep_k:bool -> bool -> bool``
      val h = ``bag_dep_h:(bool -> bool) -> bool``
      val g = ``bag_dep_g:(bool -> bool) -> (bool -> bool) -> bool``
      val fact = ``BAG_IN bag_dep_q (bag_dep_b:bool -> num)``
      val laws =
        [``!f:bool -> bool. (bag_dep_h:(bool -> bool) -> bool) f =
             (bag_dep_g:(bool -> bool) -> (bool -> bool) -> bool) f f``,
         ``!p:bool -> bool.
             (bag_dep_g:(bool -> bool) -> (bool -> bool) -> bool)
               (\x:bool. (bag_dep_k:bool -> bool -> bool) x (p x))
               (\x:bool. (bag_dep_k:bool -> bool -> bool) x (p x))``,
         fact]
      fun abstraction payload =
        Term.mk_abs (x,Term.list_mk_comb (k,[x,payload]))
      fun target payload = boolSyntax.mk_conj
        (Term.mk_comb (h,abstraction payload),fact)
      fun expanded payload =
        let val a = abstraction payload
        in Term.list_mk_comb (g,[a,a]) end
      fun fits goal rhs = require "dependent compact boundary changed"
        (Term.term_size goal < cap andalso Term.term_size rhs > cap)
      fun compare_at maximum label tap context goal =
        let val _ = testutils.tprint ("bag dependent context " ^ label)
            val native = Tactical.TAC_PROOF ((context,goal),
              Tactical.THEN (Tactical.REPEAT Tactic.COND_CASES_TAC,
                Tactical.THEN (bossLib.FULL_SIMP_TAC (bossLib.srw_ss()) [],
                  intLib.ARITH_TAC)))
            val calls = ref (0:IntInf.int)
            val work = ref (0:IntInf.int)
            val genuine = A.new_term_check
              {limit=maximum,observe=fn () => work := !work+1}
            fun admit tm = (calls := !calls+1;tap tm;genuine tm)
            val actual = SmtBagProve.bag_contextual_prove_with_admission
              admit context goal
        in exact goal (Thm.hyp native) native;
           exact goal (Thm.hyp native) actual;same_tags native actual;
           require "dependent closure bypassed paid admission"
             (!calls > 0 andalso !work >= !calls);
           testutils.OK ();(!calls,!work) end
      fun compare label tap context goal =
        compare_at cap label tap context goal
      fun plain label context goal =
        ignore (compare label (fn _ => ()) context goal)
      (* Original review fixture: every leaf is the bound x, not a free
         constant. Depth 13 is supported too, even without a cap crossing. *)
      val _ = List.app (fn depth =>
        let val payload = shared x depth
            val goal = target payload
            val _ = require "dependent review input no longer fits"
              (Term.term_size goal < cap)
            val _ = if depth=15 then fits goal (expanded payload) else ()
        in plain ("review " ^ Int.toString depth) laws goal end) [13,15]
      val _ = with_graph (fn graph => fn scope =>
        let val goal = target (shared x 15)
            val _ = testutils.tprint "bag dependent graph transport"
            val inputs = List.map (fn t =>
              #node (G.import graph scope cap t)) (goal::laws)
            val actual = A.prove_bounded_variables_admitted graph scope
              {inputs=inputs,template_limit=cap,observe=fn _ => (),
               procedure=fn admit => fn terms =>
                 let val th =
                       SmtBagProve.bag_contextual_prove_with_admission
                         admit (tl terms) (hd terms)
                 in List.foldr (fn (h,th) => Thm.DISCH h th)
                      th (tl terms) end}
            val native = Tactical.TAC_PROOF ((laws,goal),
              Tactical.THEN (bossLib.FULL_SIMP_TAC (bossLib.srw_ss()) [],
                intLib.ARITH_TAC))
            val native = List.foldr (fn (h,th) => Thm.DISCH h th)
              native laws
        in exact (boolSyntax.list_mk_imp (laws,goal)) [] (#theorem actual);
           same_tags native (#theorem actual);testutils.OK () end)
      (* A fitting source must not pay for a whole-operand closure redex.
         Exercise both a tiny exact cutoff and the unchanged actual cap. *)
      val balanced_cache = ref (Redblackmap.mkDict Int.compare)
      fun balanced count =
        case Redblackmap.peek (!balanced_cache,count) of SOME t => t
        | NONE =>
            let val t = if count=1 then x else Term.list_mk_comb
                  (join,[balanced (count div 2),
                         balanced (count-count div 2)])
            in balanced_cache := Redblackmap.insert
                 (!balanced_cache,count,t);t end
      val _ = List.app (fn (maximum,leaves,wrap,expected) =>
        let val payload = balanced leaves
            val payload = if wrap then Term.mk_comb
              (``bag_dep_step:bool -> bool``,payload) else payload
            val goal = Term.mk_comb (h,abstraction payload)
            val _ = require "dependent cutoff fixture changed"
              (Term.term_size goal=expected)
        in ignore (compare_at maximum
             ("cap " ^ Int.toString maximum) (fn _ => ()) laws goal)
        end) [(256,63,false,256),(200000,49998,true,199998)]
      (* Separately allocated alpha lambdas must share one field, including
         when the higher-order context requires their repeated identity. *)
      val alpha_a = Term.mk_abs (x,shared x 6)
      val y = ``bag_dep_y:bool``
      val alpha_b = Term.mk_abs (y,shared y 6)
      val alpha_laws =
        [``!u v:bool. (bag_dep_ah:bool -> bool -> bool) u v =
             (bag_dep_ag:bool -> bool -> bool -> bool -> bool) u u v v``,
         ``!f:bool -> bool.
             (bag_dep_ag:bool -> bool -> bool -> bool -> bool)
               ((bag_dep_al:(bool -> bool) -> bool) f)
               (bag_dep_al f) ((bag_dep_ar:(bool -> bool) -> bool) f)
               (bag_dep_ar f)``]
      val alpha_goal = Term.list_mk_comb
        (``bag_dep_ah:bool -> bool -> bool``,
         [Term.mk_comb (``bag_dep_al:(bool -> bool) -> bool``,alpha_a),
          Term.mk_comb (``bag_dep_ar:(bool -> bool) -> bool``,alpha_b)])
      val _ = require "independent alpha fixture changed"
        (Term.term_size alpha_goal=515 andalso
         not (Portable.pointer_eq (alpha_a,alpha_b)))
      val _ = compare_at 1024 "independent alpha fields" (fn _ => ())
        alpha_laws alpha_goal
      val k2 = ``bag_dep_k2:bool -> num -> bool -> bool``
      val h2 = ``bag_dep_h2:(bool -> num -> bool) -> bool``
      val g2 =
        ``bag_dep_g2:(bool -> num -> bool) -> (bool -> num -> bool) -> bool``
      val mixed_laws =
        [``!f:bool -> num -> bool.
             (bag_dep_h2:(bool -> num -> bool) -> bool) f =
             (bag_dep_g2:(bool -> num -> bool) ->
               (bool -> num -> bool) -> bool) f f``,
         ``!p:bool -> num -> bool.
             (bag_dep_g2:(bool -> num -> bool) ->
               (bool -> num -> bool) -> bool)
               (\x:bool. \n:num.
                 (bag_dep_k2:bool -> num -> bool -> bool) x n (p x n))
               (\x:bool. \n:num.
                 (bag_dep_k2:bool -> num -> bool -> bool) x n (p x n))``,
         fact]
      fun mixed (label,leaf) =
        let val payload = shared leaf 14
            val a = Term.list_mk_abs
              ([x,n],Term.list_mk_comb (k2,[x,n,payload]))
            val goal = boolSyntax.mk_conj (Term.mk_comb (h2,a),fact)
            val _ = fits goal (Term.list_mk_comb (g2,[a,a]))
        in plain label mixed_laws goal end
      (* Payload dependencies have arities 2, 1, 1 and 0. Both binders
         remain live in k2 even when a particular payload ignores one. *)
      val _ = List.app mixed
        [("mixed both live",``(bag_dep_r:bool -> num -> bool)
             bag_dep_x bag_dep_n``),
         ("mixed outer only",``(bag_dep_r:bool -> num -> bool)
             bag_dep_x bag_dep_free_num``),
         ("mixed inner only",``(bag_dep_r:bool -> num -> bool)
             bag_dep_free_bool bag_dep_n``),
         ("mixed independent",``(bag_dep_r:bool -> num -> bool)
             bag_dep_free_bool bag_dep_free_num``)]
      (* This redex is introduced by realizing a functional hole. The
         payload itself must be kept verbatim, including SOURCE redexes. *)
      fun prebeta payload = Term.mk_comb (h,Term.mk_abs (x,
        Term.list_mk_comb (k,[x,Term.mk_comb
          (Term.mk_abs (x,payload),x)])))
      val source = shared
        ``(\z:bool. (bag_dep_r1:bool -> bool) z) bag_dep_x`` 14
      val source_pre = prebeta source
      val pre_seen = ref false
      fun source_tap tm =
        if tm ~~ source_pre then pre_seen := true else ()
      val _ = fits (target source) (expanded source)
      val _ = compare "source beta retained" source_tap laws (target source)
      val _ = require "whole-operand administrative beta was constructed"
        (not (!pre_seen))
      (* Reject the first LOCAL introduced beta operand, or its forecast
         result. No whole-operand pre-beta realization is permitted. *)
      val small = shared x 6
      fun terminal label forecast =
        let val _ = testutils.tprint ("bag dependent terminal " ^ label)
            val armed = ref NONE val stopped = ref false val after = ref 0
            val genuine = A.new_term_check {limit=cap,observe=fn () => ()}
            fun stop () = (stopped := true;raise Feedback.mk_HOL_ERR
              "Task42Dependent" label "first admission")
            fun admit tm =
              if !stopped then (after := !after+1;genuine tm)
              else if Option.isSome (!armed) then
                (if forecast andalso tm ~~ valOf (!armed) then stop ()
                 else genuine tm)
              else if Term.is_comb tm andalso
                  Term.is_abs (Term.rator tm) then
                (armed := SOME (Term.beta_conv tm);
                 if forecast then genuine tm else stop ())
              else genuine tm
            val result = Exn.capture (fn () =>
              SmtBagProve.bag_contextual_prove_with_admission
                admit laws (target small)) ()
        in require "dependent admission lost or retried its first error"
             (Option.isSome (!armed) andalso !stopped andalso !after=0 andalso
              (case result of Exn.Exn (Feedback.HOL_ERR detail) =>
                 Feedback.top_structure_of detail = "Task42Dependent" andalso
                 Feedback.top_function_of detail = label andalso
                 Feedback.message_of detail = "first admission"
               | _ => false));
           testutils.OK ();plain (label ^ " recovery") laws (target small)
        end
      val _ = terminal "pre-beta" false
      val _ = terminal "beta forecast" true
      (* Dependent unary suffixes exercise arena construction, not just
         shallow shared trees. These same laws close after two refinements.
         Count checker visits AND callback calls; this is a local paid-Work
         regression, not a claim of universal linear native runtime. *)
      fun suffix 0 = x
        | suffix size = Term.mk_comb
            (``bag_dep_step:bool -> bool``,suffix (size-1))
      fun scaling size = compare ("suffix " ^ Int.toString size)
        (fn _ => ()) laws (target (suffix size))
      val (small_calls,small_work) = scaling 256
      val (large_calls,large_work) = scaling 512
      val _ = print ("BAG_DEPENDENT_WORK calls=" ^
        IntInf.toString small_calls ^ "/" ^ IntInf.toString large_calls ^
        " visits=" ^ IntInf.toString small_work ^ "/" ^
        IntInf.toString large_work ^ "\n")
    in require "dependent suffix exceeded local 2x-growth Work allowance"
         (large_calls <= 3*small_calls andalso large_work <= 3*small_work)
    end

  (* Freshening must not capture an existing free prime-name in a beta
     body. This quantified beta result is neither a whole input nor a
     whole output conversion side: rejecting it tests the forecast itself. *)
  fun prospective_capture () =
    let
      val cases =
        [(``BAG_FILTER (\v:bool. !e:bool. bag_R (e':bool) v e) b bag_x =
             (if (!q:bool. bag_R e' bag_x q) then b bag_x else 0)``,
          ``!q:bool. bag_R (e':bool) (e:bool) q``),
         (``BAG_FILTER
             (\v:bool. !e:bool. bag_R3 (e':bool) (e'':bool) (e''':bool) v e)
             b bag_x =
             (if (!q:bool. bag_R3 e' e'' e''' bag_x q)
              then b bag_x else 0)``,
          ``!q:bool. bag_R3 (e':bool) (e'':bool) (e''':bool) (e:bool) q``),
         (``BAG_FILTER (\v:bool. !e:num. bag_Rn (e':num) v e) b bag_x =
             (if (!q:num. bag_Rn e' bag_x q) then b bag_x else 0)``,
          ``!q:num. bag_Rn (e':num) (e:bool) q``)]
      exception Primary
      fun check (target,expected) (label,worker) =
        let val _ = testutils.tprint ("bag capture-free beta " ^ label)
            val stopped = ref false val after = ref 0
            val genuine = A.new_term_check
              {limit=limit,observe=fn () => ()}
            fun admit tm =
              if !stopped then (after := !after+1;genuine tm)
              else if tm ~~ expected then (stopped := true;raise Primary)
              else genuine tm
            val result = Exn.capture (worker admit) target
        in require "capture-correct beta was not admitted before conversion"
             (!stopped andalso !after=0 andalso
              (case result of Exn.Exn Primary => true | _ => false));
           exact target [] (worker genuine target);testutils.OK () end
    in List.app (fn pair => List.app (check pair)
         [("native",prove),("CPC",cpc_worker "trust")]) cases end

  fun binder_names () = with_graph (fn graph => fn scope =>
    let
      (* A bound Boolean and a free list may share their spelling. Native
         standard dest_abs would need a typed FV set on this clash. The
         recognizer uses the admitted name-only opener instead. *)
      val variable = Term.mk_var ("bag_binder_clash",Type.bool)
      val free = Term.mk_var ("bag_binder_clash",``:num list``)
      val abstraction = Term.mk_abs (variable,
        Term.mk_comb (``LENGTH:num list -> num``,free))
      val goal = boolSyntax.mk_conj
        (boolSyntax.mk_eq (abstraction,abstraction),
         ``BAG_UNION (b:'a -> num) c x = b x + c x``)
      val _ = require "bag recognizer lost its binder-clash family"
        (SmtBagProve.has_bag_encoding goal)
      val native = SmtBagProve.bag_prove goal
      val result = A.prove_bounded_variables_admitted graph scope
        {inputs=[import graph scope goal],template_limit=limit,
         observe=fn _ => (),procedure=fn admit => fn [term] =>
           prove admit term | _ => raise Fail "bag binder arity"}
    in exact goal [] native;exact goal [] (#theorem result);
       same_tags native (#theorem result) end)

  (* Fitting inputs must not pay admission for an unused INSERT branch,
     an expanding reflexive INSERT, or both leaves of COND_CLAUSES as one
     conjunction. Keep the real 200000-node allowance, not an accepting
     admission stub. *)
  fun fitting_intermediates () =
    let
      val cap = 200000
      val element = optionSyntax.mk_some (shared_element 15)
      val bag = ``bag_large_count:bool option -> num``
      val none = ``NONE:bool option``
      val inserted = bagSyntax.mk_insert (element,bag)
      val insert_goal = boolSyntax.mk_eq
        (Term.mk_comb (inserted,none),Term.mk_comb (bag,none))
      val payload = shared_element 14
      val opaque_bag = Term.mk_comb
        (``bag_builder:bool -> (bool -> num)``,payload)
      val reflexive_count = Term.mk_comb
        (bagSyntax.mk_insert (``e:bool``,opaque_bag),``x:bool``)
      val reflexive_goal = boolSyntax.mk_eq
        (reflexive_count,reflexive_count)
      (* shared_element has s(0)=1, s(n+1)=3+2*s(n), hence
         s(14)=4*2^14-3. Builder application adds 2, INSERT e b x adds
         6, and equality adds 3 around two occurrences of that side. *)
      val payload_size = 4 * 16384 - 3
      val count_size = 6 + 2 + payload_size
      val reflexive_size = 3 + 2 * count_size
      val _ = require "opaque reflexive INSERT fixture changed"
        (Term.term_size payload = payload_size andalso
         Term.term_size opaque_bag = 2 + payload_size andalso
         Term.term_size reflexive_count = count_size)
      val singleton = bagSyntax.mk_insert
        (shared_element 14,``EMPTY_BAG:bool -> num``)
      fun conditional guard = boolSyntax.mk_eq
        (boolSyntax.mk_cond (guard,singleton,singleton),singleton)
      val conditional_goal = conditional ``bag_large_guard:bool``
      val bundle = boolSyntax.mk_conj
        (conditional boolSyntax.T,conditional boolSyntax.F)
      val _ = require "large conditional bundle fixture changed"
        (Term.term_size bundle = 393241 andalso
         Term.term_size bundle > cap)
      fun check_using worker label size goal =
        with_graph (fn graph => fn scope =>
        let
          val _ = testutils.tprint ("bag fitting " ^ label)
          val _ = require (label ^ ": fitting bag fixture size changed")
            (Term.term_size goal = size andalso size < cap)
          val native = worker
            (A.new_term_check {limit=cap,observe=fn () => ()}) goal
          val _ = exact goal [] native
          val node = #node (G.import graph scope cap goal)
          val calls = ref 0
          val (result,statistics) =
            SmtReplayRuleObservation.with_statistics (fn () =>
              A.prove_bounded_variables_admitted graph scope
                {inputs=[node,node],template_limit=cap,observe=fn _ => (),
                 procedure=fn admit => fn [left,right] =>
                   (calls := !calls+1;
                    require "fitting bag shared root was copied"
                      (if SmtResource.contains Term.is_abs goal then
                         left ~~ right
                       else Portable.pointer_eq (left,right));
                    require "fitting bag source variables reached worker"
                      (H.disjoint [goal] [left,right]);
                    shape goal left;worker admit left)
                   | _ => raise Fail "fitting bag arity"})
        in require "fitting bag worker was retried or bypassed" (!calls=1);
           require "fitting bag transport was not one INST"
             (#selected_returns statistics = 1);
           exact goal [] (#theorem result);
           same_tags native (#theorem result);testutils.OK () end)
      val check = check_using prove
      (* The old shared 32-visit discovery fuel consumed SOME^31's payload
         root before seeing the query's discriminating NONE. *)
      fun wrap 0 e = e | wrap n e = wrap (n-1) (optionSyntax.mk_some e)
      val nested_element = wrap 31 (shared_element 15)
      val equal_element = optionSyntax.mk_some (shared_element 14)
      val equal_count = Term.mk_comb (bag,equal_element)
      val equal_goal = boolSyntax.mk_eq
        (Term.mk_comb (bagSyntax.mk_insert (equal_element,bag),equal_element),
         numSyntax.mk_plus (equal_count,``1:num``))
      val nested_type = Term.type_of nested_element
      val nested_bag = Term.mk_var ("bag_nested_count",
        Type.mk_type ("fun",[nested_type,numSyntax.num]))
      val nested_none = Term.inst
        [{redex=Type.alpha,residue=optionSyntax.dest_option nested_type}]
        ``NONE:'a option``
      val nested_goal = boolSyntax.mk_eq
        (Term.mk_comb (bagSyntax.mk_insert (nested_element,nested_bag),
           nested_none),Term.mk_comb (nested_bag,nested_none))
      val empty = ``EMPTY_BAG:bool -> num``
      val large_guard = shared_element 15
      val large_guard_goal = boolSyntax.mk_eq
        (boolSyntax.mk_cond (large_guard,empty,empty),empty)
      val binder = ``bag_unused_bound:bool``
      val bound_guard_goal = boolSyntax.mk_eq
        (Term.mk_abs (binder,boolSyntax.mk_cond (large_guard,empty,empty)),
         Term.mk_abs (binder,empty))
      fun known_guard negative =
        let val _ = testutils.tprint "bag fitting contextual known guard"
            val bag = ``bag_other:bool -> num``
            val goal = boolSyntax.mk_eq
              (boolSyntax.mk_cond (large_guard,
                 if negative then bag else empty,
                 if negative then empty else bag),empty)
            val hypothesis = if negative then boolSyntax.mk_neg large_guard
              else large_guard
            val _ = require "known-guard fixture ceased fitting"
              (Term.term_size goal = 131079 andalso
               Term.term_size hypothesis < cap)
            val theorem = SmtBagProve.bag_contextual_prove_with_admission
              (A.new_term_check {limit=cap,observe=fn () => ()})
              [hypothesis] goal
        in exact goal [hypothesis] theorem;testutils.OK () end
    in check "INSERT SOME/NONE" 131083 insert_goal;
       check "nested INSERT SOME/NONE" 131143 nested_goal;
       check "INSERT equal SOME" 196623 equal_goal;
       check_using (fn admit =>
         SmtBagProve.bag_contextual_prove_with_admission admit [])
         "contextual large guard" 131079 large_guard_goal;
       check_using (fn admit =>
         SmtBagProve.bag_contextual_prove_with_admission admit [])
         "contextual large guard under binder" 131081 bound_guard_goal;
       known_guard false;known_guard true;
       check_using (fn admit =>
         SmtBagProve.bag_contextual_prove_with_admission admit [])
         "contextual reflexive guard" 131079
         (boolSyntax.mk_eq (boolSyntax.mk_cond
           (boolSyntax.mk_eq (shared_element 14,shared_element 14),
            empty,``bag_other:bool -> num``),empty));
       List.app (fn (negative,symmetric) =>
         let val _ = testutils.tprint "bag fitting normalized guard"
             val value = if negative then boolSyntax.F else boolSyntax.T
             val hypothesis = boolSyntax.mk_eq
               (if symmetric then (value,large_guard) else (large_guard,value))
             val other = ``bag_other:bool -> num``
             val target = boolSyntax.mk_eq
               (boolSyntax.mk_cond (large_guard,
                 if negative then other else empty,
                 if negative then empty else other),empty)
             val theorem = SmtBagProve.bag_contextual_prove_with_admission
               (A.new_term_check {limit=cap,observe=fn () => ()})
               [hypothesis] target
         in exact target [hypothesis] theorem;testutils.OK () end)
         [(false,false),(false,true),(true,false),(true,true)];
       check "reflexive INSERT opaque bag" reflexive_size reflexive_goal;
       check "conditional shared singleton" 196619 conditional_goal;
       check_using (fn admit =>
         SmtBagProve.bag_contextual_prove_with_admission admit [])
         "contextual conditional" 196619 conditional_goal end

  (* Shallow physically shared operand near the existing 200000-node cap;
     fitting input succeeds, smaller allowance never enters the worker. *)
  fun large_input () = with_graph (fn graph => fn scope =>
    let
      val insert = #1 (boolSyntax.strip_comb ``BAG_INSERT (x:bool) EMPTY_BAG``)
      val singleton = Term.list_mk_comb
        (insert,[shared_element 14,``EMPTY_BAG:bool -> num``])
      val union = #1 (boolSyntax.strip_comb ``BAG_UNION (b:bool -> num) c``)
      val goal = boolSyntax.mk_eq (Term.list_mk_comb
        (union,[``EMPTY_BAG:bool -> num``,singleton]),singleton)
      val cap = 200000
      val size = Term.term_size goal
      val _ = require "large bag fixture size changed"
        (size > 131000 andalso size < cap)
      val node = #node (G.import graph scope cap goal)
      val calls = ref 0
      val worker_returned = ref false
      fun run allowance observe =
        (worker_returned := false;
         A.prove_bounded_variables_admitted graph scope
          {inputs=[node,node],template_limit=allowance,observe=observe,
           procedure=fn admit => fn [left,right] =>
             let
               val _ = calls := !calls+1
               val _ = require "large shared bag root was copied"
                 (Portable.pointer_eq (left,right))
               val _ = require "large source variables reached bag worker"
                 (H.disjoint [goal] [left,right])
               val theorem = prove admit left
             in worker_returned := true;theorem end
             | _ => raise Fail "large bag arity"})
      val refused = (ignore (run (size-1) (fn _ => ()));false)
        handle Feedback.HOL_ERR detail => String.isSubstring
          "exceeds local admission" (Feedback.message_of detail)
      val _ = require "oversized bag input entered worker"
        (refused andalso !calls=0)
      (* Result admission has two unfolded scans before the final native
         INST count. A count scan observes >2 visits per raw node. Three
         paid scans exceed 7*size; two scans plus shallow DAG metadata do
         not. Bulk INST prepayment alone cannot pay the preceding count. *)
      val minimum_ticks = 7 * IntInf.fromInt size
      val ticks = ref (0:IntInf.int)
      val bulk = ref 0
      fun observe amount = if not (!worker_returned) then ()
        else if amount = 1 then ticks := !ticks+1
        else (bulk := !bulk+1;
          require "bag native counting happened before its visit payments"
            (amount = IntInf.fromInt size andalso !ticks >= minimum_ticks))
      val (result,statistics) =
        SmtReplayRuleObservation.with_statistics (fn () => run cap observe)
      val _ = require "bounded bag realization was not one paid INST"
        (#selected_returns statistics = 1 andalso !bulk=1 andalso !calls=1)
      exception CountingBudget
      val _ = ticks := 0
      val _ = bulk := 0
      fun stop_count amount = if not (!worker_returned) then ()
        else if amount = 1 then
          (ticks := !ticks+1;
           if !ticks >= minimum_ticks then raise CountingBudget else ())
        else bulk := !bulk+1
      val (count_stopped,count_statistics) =
        SmtReplayRuleObservation.with_statistics (fn () =>
          Exn.capture (fn () => run cap stop_count) ())
      val _ = require "bag counting observer escaped or reached native INST"
        (!calls=2 andalso !bulk=0 andalso
         #selected_returns count_statistics = 0 andalso
         (case count_stopped of Exn.Exn CountingBudget => true | _ => false))
      exception NativeBudget
      val (stopped,statistics) = SmtReplayRuleObservation.with_statistics
        (fn () => Exn.capture (fn () =>
          A.prove_bounded_variables_admitted graph scope
            {inputs=[node],template_limit=cap,
             observe=fn amount => if amount > 1 then raise NativeBudget else (),
             procedure=fn admit => fn [term] => prove admit term
               | _ => raise Fail "bag native payment arity"}) ())
      val _ = require "native bag substitution escaped prospective payment"
        (#selected_returns statistics = 0 andalso
         (case stopped of Exn.Exn NativeBudget => true | _ => false))
    in require "large bag worker retried" (!calls=2);
       exact goal [] (#theorem result) end)

  fun run () =
    List.app (fn (name,test) => test () handle error =>
      raise Fail (name ^ ": " ^ General.exnMessage error))
      [("bag schemas",schemas_and_sharing),("bag false",false_obligations),
       ("bag Int guards",int_bag_guards),("bag Int arrays",int_array_maps),
       ("bag context",contextual),("bag CPC",cpc_cases),
       ("bag compact TRUST",compact_trust_identity),
       ("bag graph identity",graph_handlers),("bag admission",admission_errors),
       ("bag prospective beta phases",prospective_betas),
       ("bag prospective context",prospective_context),
       ("bag fitting context",fitting_context),
       ("bag dependent context",dependent_context),
       ("bag prospective capture",prospective_capture),
       ("bag binder names",binder_names),
       ("bag fitting intermediates",fitting_intermediates),
       ("bag large",large_input)]
end
