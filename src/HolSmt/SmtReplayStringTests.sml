(* Task41: Unicode String schemas and same-native declaration controls.
   smtstr is a type definition, NOT a datatype with constructors. *)
structure SmtReplayStringTests =
struct
  open HolKernel Parse boolLib bossLib
  open smtstringTheory
  structure H = SmtReplayArithmeticTests
  structure G = SmtReplayGraph
  structure A = SmtReplayArithmetic
  structure I = SmtReplayImport
  structure P = SmtReplayProof
  structure R = SmtReplayRules
  structure Q = CPC_ProofParser
  structure F = SmtLib_GraphFrontend
  structure W = SmtReplayInvocationWork
  structure ZR = Z3_GraphProofReplay
  val limit = H.limit
  val require = H.require
  val with_graph = H.with_graph
  val import = H.import

  fun exact term hypotheses theorem =
    (H.exact term hypotheses theorem;
     require "String theorem acquired axiom tags"
       (null (Tag.axioms_of (Thm.tag theorem))))
  fun same_tags expected actual = require
    ("String full tags changed: " ^
     String.concatWith "," (#1 (Tag.dest_tag (Thm.tag expected))) ^ " -> " ^
     String.concatWith "," (#1 (Tag.dest_tag (Thm.tag actual))))
    (Tag.dest_tag (Thm.tag expected) = Tag.dest_tag (Thm.tag actual))
  fun declines action =
    (case action () of NONE => true | SOME _ => false)
    handle Conv.UNCHANGED => true
      | HolSatLib.SAT_cex _ => true
      | Feedback.HOL_ERR detail =>
          if SmtResource.is_resource_gate detail then
            raise Feedback.HOL_ERR detail
          else true

  val native_string =
    SmtStringProve.string_prove Library.arith_prove_with_cases
  val string_variable = ``task41_string:smtstr``
  val contains_refl =
    ``smtstr_contains (task41_string:smtstr) task41_string``
  val concat_nil =
    ``smtstr_concat (SmtStr []) (task41_string:smtstr) = task41_string``

  (* Ground literals, symbolic concat, membership and regex constructors
     must remain syntax, not become independent Boolean/compound holes.
     First run the ORIGINAL worker: this tests transport, not new solving. *)
  val schemas =
    [(``smtstr_concat (SmtStr [65]) (SmtStr [66]) = SmtStr [65;66]``,
       ``smtstr_concat (SmtStr [65]) (SmtStr [66])``),
     (contains_refl,string_variable),
     (concat_nil,``smtstr_concat (SmtStr []) (task41_string:smtstr)``),
     (``smt_in_re (task41_string:smtstr) (reglan_to_re task41_string)``,
       ``reglan_to_re (task41_string:smtstr)``),
     (``smt_in_re (SmtStr [65;66])
          (reglan_concat (reglan_to_re (SmtStr [65]))
                         (reglan_to_re (SmtStr [66])))``,
       ``reglan_concat (reglan_to_re (SmtStr [65]))
                       (reglan_to_re (SmtStr [66]))``)]

  fun schemas_and_sharing () = with_graph (fn graph => fn scope =>
    let
      fun check (original,operand) =
        let
          val native = native_string original
          val _ = exact original [] native
          val goal = import graph scope original
          val child = import graph scope operand
          val calls = ref 0
          fun shape source named =
            let val (substitution,types) = Term.match_term source named
            in require "String operator, literal or Type was hidden"
              (null types andalso List.all
                (fn {residue,...} => Term.is_var residue) substitution)
            end
          val result = A.prove_admitted graph scope
            {inputs=[goal,goal,child,child],template_limit=limit,
             observe=fn _ => (),procedure=fn admit => fn terms =>
               case terms of [left,right,shared,again] =>
                 (calls := !calls+1;
                  require "shared String roots were rebuilt separately"
                    (Portable.pointer_eq (left,right) andalso
                     Portable.pointer_eq (shared,again));
                  shape original left;shape operand shared;
                  require "source variables reached String worker"
                    (H.disjoint [original,operand] terms);
                  require "String child lost its worker identity"
                    (Portable.pointer_eq
                      (HolKernel.find_term (fn tm => tm ~~ shared) left,
                       shared));
                  List.app admit terms;native_string left)
               | _ => raise Fail "String schema arity"}
          val theorem = #theorem result
        in require "String worker was retried or bypassed" (!calls=1);
           exact original [] theorem;same_tags native theorem end
    in List.app check schemas end)

  val context_goal =
    ``smtstr_len (task41_string:smtstr) = smtstr_len task41_other``
  val context = [``(task41_string:smtstr) = task41_other``]

  fun contextual () = with_graph (fn graph => fn scope =>
    let
      val native = SmtStringProve.string_contextual_prove context context_goal
      val _ = exact context_goal context native
      val result = A.prove_admitted graph scope
        {inputs=map (import graph scope) (context_goal::context),
         template_limit=limit,observe=fn _ => (),
         procedure=fn admit => fn terms => case terms of [goal,premise] =>
           (require "context source variables reached String worker"
              (H.disjoint (context_goal::context) terms);
            List.app admit terms;
            let val theorem =
                  SmtStringProve.string_contextual_prove [premise] goal
                val _ = exact goal [premise] theorem
            in Thm.DISCH premise theorem end)
         | _ => raise Fail "String context arity"}
      val theorem = #theorem result
    in exact (boolSyntax.mk_imp (hd context,context_goal)) [] theorem;
       same_tags native theorem end)

  fun located scope node:F.term =
    {node=node,scope=scope,binder_blocks=[],source_syntax=NONE,
     occurrence=SmtLib_Parser.ConstructionOccurrence
       {value=node,role=SmtLib_Parser.ConstructionAtom,
        token="task41-string",children=[]}}
  fun registered name = valOf (CPC_Proof.lookup_rule "1.3.4" name)

  (* Evaluate symbolic String, not a ground literal. A bad operand with
     the same native spelling must still be rejected. The contains controls
     have NO numeric, list, or regex operand to select naming accidentally.
     concat_nil's [] is its intrinsic empty literal. *)
  datatype identity_case = Contains | ConcatNil | Evaluate
  fun identity_graph kind graph scope =
    let
      val source = G.variable graph scope G.RigidSource string_variable
      val other = G.variable graph scope G.Generated string_variable
      val _ = require "String identity controls need distinct same-native IDs"
        (source <> other andalso
         G.representative graph source ~~ G.representative graph other)
      fun apply operator args = List.foldl
        (fn (x,f) => G.application graph scope (f,x))
        (G.constant graph scope operator) args
      val equality = Term.rator (Term.rator
        (boolSyntax.mk_eq (string_variable,string_variable)))
      fun eq x y = apply equality [x,y]
      val (good,bad,args) = case kind of
          Contains =>
            let val contains = Term.rator (Term.rator contains_refl)
                val truth = G.constant graph scope boolSyntax.T
                val boolean_eq = Term.rator (Term.rator
                  (boolSyntax.mk_eq (contains_refl,boolSyntax.T)))
                fun is_true value = apply boolean_eq [value,truth]
            in (is_true (apply contains [source,source]),
                is_true (apply contains [source,other]),[]) end
        | ConcatNil =>
            let val empty = import graph scope ``SmtStr []``
                val concat = Term.rator (Term.rator
                  ``smtstr_concat (s:smtstr) t``)
                val joined = apply concat [empty,source]
            in (eq joined source,eq joined other,[]) end
        | Evaluate =>
            let val conditional = Term.rator (Term.rator (Term.rator
                  ``if T then task41_string:smtstr else task41_string``))
                val truth = G.constant graph scope boolSyntax.T
                val original = apply conditional [truth,source,source]
            in (eq original source,eq original other,[original]) end
      val _ = require "String bad endpoint changed native spelling"
        (good <> bad andalso
         G.representative graph good ~~ G.representative graph bad)
      val inputs = [good,bad] @ args
      val _ = case kind of ConcatNil => () | _ =>
        (require "String identity control acquired incidental numeric syntax"
           (not (A.has_numeric_operand graph scope
             {inputs=inputs,observe=fn () => ()}));
         require "String identity control acquired incidental Seq syntax"
           (not (SmtReplayStructured.has_sequence_operand graph scope
             {inputs=inputs,observe=fn () => ()})))
    in (good,bad,args) end

  (* Compatibility and recorded producers must BOTH use the graph namespace.
     Native representatives alone cannot distinguish either pair. *)
  fun z3_identity () = with_graph (fn graph => fn scope =>
    let
      val proof:Z3_GraphProofParser.proof =
        {steps=Redblackmap.mkDict Z3_GraphProofParser.compare_id,
         root=Z3_GraphProofParser.Anonymous 0,vars=[],
         z3_version="4.15.3",close=fn () => ()}
      fun request name target:ZR.local_request =
        {rule=valOf (Z3_Proof.lookup_rule "4.15.3" name),
         metadata=if name="th-lemma-seq" then SOME
           (Z3_Proof.mk_th_lemma_metadata ("seq",NONE,[])) else NONE,
         target=target,premises=[],arguments=[],law=target}
      fun compatibility request = Option.map
        (fn theorem => {definitions=[],theorem=theorem})
        (Z3_ProofReplay.graph_bounded_local_law graph [] proof request)
      fun recorded request =
        Z3_ProofReplay.graph_bounded_recorded_local_law
          graph scope limit [] proof request
      fun check kind =
        let
          val (good,bad,_) = identity_graph kind graph scope
          val original = G.representative graph good
          val native = native_string original
          val _ = exact original [] native
          fun pair produce name =
            (case produce (request name good) of
               NONE => raise Fail ("valid String Z3 law declined: " ^ name)
             | SOME {definitions,theorem} =>
                 (require "String Z3 law invented definitions"
                    (null definitions);
                  exact original [] theorem;same_tags native theorem);
             require ("String Z3 merged declaration IDs: " ^ name)
               (declines (fn () => produce (request name bad))))
        in List.app (fn produce => List.app (pair produce)
             ["th-lemma-seq","rewrite"]) [compatibility,recorded] end
    in List.app check [Contains,ConcatNil] end)

  fun native_cpc rule goal args =
    let
      fun object term:CPC_Proof.located_term =
        {term=term,provenance=
          CPC_Proof.UnavailableProvenance "Task41 native control"}
      val step:CPC_Proof.step =
        {id="@native",rule=registered rule,premises=[],
         conclusion=SOME (object goal),args=map object args}
    in #1 (CPC_ProofReplay.graph_bounded_worker [] (step,[])) end

  (* Complete public compact dispatch, including TRUST's deferred boundary.
     Never manufacture a theorem for the callback. The negative certificate
     has the SAME native conclusion and tags, but a different graph ID. *)
  fun cpc_identity () =
    let
      fun check kind rule different = with_graph (fn graph => fn scope =>
        let
          val (good,bad,evaluation_args) = identity_graph kind graph scope
          val goal = G.representative graph good
          val args = case kind of Evaluate => evaluation_args | _ =>
            [if different then bad else good]
          val native = native_cpc rule goal
            (map (G.representative graph) args)
          val _ = exact goal [] native
          val unused = ``task41_unused:bool``
          val sources = SmtReplaySource.new graph scope limit
            {goal=goal,assumptions=[unused]}
          val _ = require "String Source import changed good graph endpoint"
            (#node (SmtReplaySource.goal_source sources) = good)
          val target = if different then bad else good
          fun loc node = located scope node
          val proof:Q.graph_proof =
            {cvc_version="1.3.4",commands=
              [Q.GraphAssume ("@denied",loc
                 (SmtReplaySource.denied_goal_node sources)),
               Q.GraphStep {pop=false,step=
                 {id="@string",rule=registered rule,premises=[],
                  conclusion=SOME (loc target),
                  args=map (Q.GraphTerm o loc) args,
                  raw_conclusion=NONE,raw_args=[]}},
               Q.GraphStep {pop=false,step=
                 {id="@done",rule=registered "resolution",
                  premises=["@string","@denied"],
                  conclusion=SOME (loc (G.constant graph scope boolSyntax.F)),
                  args=[],raw_conclusion=NONE,raw_args=[]}}]}
          fun replay () = CPC_ProofReplay.prove_graph_proof
            {graph=graph,scope=scope,sources=sources,proof=proof}
        in if different then
             require ("compact String merged declaration IDs: " ^ rule)
               (declines (fn () => SOME (replay ())))
           else let val theorem = replay ()
                in exact goal [unused] theorem;same_tags native theorem end
        end)
      fun pair kind rule =
        (testutils.tprint ("Task41 compact String " ^ rule);
         check kind rule false;check kind rule true;testutils.OK ())
    in List.app (fn kind => List.app (pair kind) ["trust","str"])
         [Contains,ConcatNil];
       pair Evaluate "evaluate"
    end

  (* H checks variable-only object schemas, source disjointness, exact
     Goal/Hyp, declared/omitted result roles, and exactly one real worker. *)
  fun cpc_cases () =
    let
      fun check native goal assumptions rule args declared =
        H.cpc_arguments_using_admitted limit
          (fn admit => fn input =>
            let val result as (theorem,_) =
                  CPC_ProofReplay.graph_bounded_worker_with_admission
                    admit [] input
            in same_tags native theorem;
               require "String CPC worker acquired axioms"
                 (null (Tag.axioms_of (Thm.tag theorem)));result end)
          goal assumptions rule (map H.Object args) declared
      fun both goal rule args =
        let val native = native_cpc rule goal args
            val _ = exact goal [] native
        in List.app (check native goal [] rule args) [true,false] end
      val _ = List.app (fn goal => List.app (fn rule =>
        both goal rule [goal]) ["trust","str"]) [contains_refl,concat_nil]
      val rare_goal = boolSyntax.mk_eq (contains_refl,boolSyntax.T)
      val _ = check (native_cpc "str-contains-refl" rare_goal [string_variable])
        rare_goal [] "str-contains-refl" [string_variable] true
      val native = SmtStringProve.string_contextual_prove context context_goal
      val _ = exact context_goal context native
    in List.app (check native context_goal context "str" [context_goal])
         [true,false] end

  fun parsed_z3 () =
    let
      val native = SmtStringProve.string_contextual_prove context context_goal
      val _ = exact context_goal context native
    in Z3_CompactReplayTests.with_proof
      [("s",string_variable),("t",``task41_other:smtstr``)]
      "((proof ((_ th-lemma seq) (asserted (= s t)) \
      \(= (str.len s) (str.len t)))))"
      (fn graph => fn scope => fn proof =>
        let val theorem = Z3_CompactReplayTests.replay graph scope proof
              limit (Z3_CompactReplayTests.fixed graph proof)
        in exact context_goal context theorem;same_tags native theorem end)
    end

  fun parsed_cpc () = with_graph (fn graph => fn scope =>
    let
      val native = SmtStringProve.string_contextual_prove context context_goal
      val _ = exact context_goal context native
      val sources = SmtReplaySource.new graph scope limit
        {goal=context_goal,assumptions=context}
      val work = W.begin graph scope sources
        {limits={input_limit=limit,output_limit=limit,template_limit=limit},
         work_limit=10000000}
      val options = Z3_CompactReplayTests.options graph scope
        [("s",string_variable),("t",``task41_other:smtstr``)]
      val stream = TextIO.openString
        "((assume @p (= s t)) \
        \(assume @denied (not (= (str.len s) (str.len t)))) \
        \(step @law (= (str.len s) (str.len t)) \
        \:rule string_reduction :premises (@p)) \
        \(step @done false :rule resolution :premises (@law @denied)))"
      val result = Exn.capture (fn () =>
        let
          val proof = Q.parse_graph_stream_with_version options
            (SmtLib_Logics.parsedicts_of_logic "ALL") "1.3.4" stream
          val preprocessing = SmtLib_GraphPreprocess.discover_from_sources
            graph scope sources
            {import_limit=limit,revisit=false,check_type=fn _ => (),
             conversion=fn _ => NONE}
        in CPC_GraphProofReplay.prove_admitted_using
          {graph=graph,scope=scope,sources=sources,
           preprocessing=SOME preprocessing,work=SOME work,
           proof=proof,ordinary_limit=limit,template_limit=limit,
           worker=fn admit =>
             CPC_ProofReplay.graph_bounded_worker_with_admission admit [],
           clause_worker=NONE,force_worker=NONE} end) ()
      val _ = TextIO.closeIn stream
      val _ = W.close work
      val theorem = Exn.release result
    in exact context_goal context theorem;same_tags native theorem end)

  (* The original congruence fallback derives operand chains, not just a
     direct premise. Keep it before realization, including exact actual Hyp.
     An unused advertised premise must not leak out of compact assembly. *)
  fun regex_congruence () = with_graph (fn graph => fn scope =>
    let
      val premises =
        [``(s:smtstr) = u``, ``(u:smtstr) = t``,
         ``reglan_equiv r r'``]
      val goals =
        [``smt_in_re s r = smt_in_re t r'``,
         ``reglan_equiv (reglan_star r) (reglan_star r')``,
         ``reglan_equiv (reglan_union r q) (reglan_union r' q)``]
      fun check goal =
        let
          val native = SmtRegLanProve.congruence
            (map Thm.ASSUME premises) goal
          val hypotheses = Thm.hyp native
          val target = import graph scope goal
          val inputs = map (import graph scope) (premises @ [``unused:bool``])
          val block = P.prepare_needed_sources graph
            {scope=scope,roots=target::inputs,sources=inputs,
             template_limit=limit}
          val edge = R.assemble graph block
            {rule="cong",target=target,premises=Lib.enumerate 0 inputs
              |> map (fn (i,node) => (node,P.source block i))}
          val theorem = P.realize block target edge
        in exact goal hypotheses theorem;same_tags native theorem end
      val _ = List.app check goals
      val bad = ``smt_in_re (SmtStr [65]) reglan_none``
      val _ = require "false regex membership proved"
        (declines (fn () => SOME (A.prove_admitted graph scope
          {inputs=[import graph scope bad],template_limit=limit,
           observe=fn _ => (),procedure=fn admit => fn [term] =>
             (admit term;native_string term)
             | _ => raise Fail "false membership arity"})))
      val bad = ``reglan_equiv (f r) (f r')``
      val premise = ``reglan_equiv r r'``
      val target = import graph scope bad
      val input = import graph scope premise
      val block = P.prepare_needed_sources graph
        {scope=scope,roots=[target,input],sources=[input],template_limit=limit}
    in require "opaque regex producer accepted semantic equality"
      (declines (fn () => SOME (R.assemble graph block
        {rule="cong",target=target,premises=[(input,P.source block 0)]})))
    end)

  fun parsed_regex () = with_graph (fn graph => fn scope =>
    let
      val goal = ``smt_in_re s r = smt_in_re t r'``
      val hypotheses = [``(s:smtstr) = u``,``(u:smtstr) = t``,
        ``reglan_equiv r r'``]
      val native = SmtRegLanProve.congruence (map Thm.ASSUME hypotheses) goal
      val _ = exact goal hypotheses native
      val sources = SmtReplaySource.new graph scope limit
        {goal=goal,assumptions=hypotheses}
      val options = Z3_CompactReplayTests.options graph scope
        [("s",``s:smtstr``),("u",``u:smtstr``),("t",``t:smtstr``),
         ("r",``r:reglan``),("r1",``r':reglan``)]
      val stream = TextIO.openString
        "((assume @p (= s u)) (assume @q (= u t)) \
        \(assume @r (= r r1)) \
        \(assume @denied (not (= (str.in_re s r) (str.in_re t r1)))) \
        \(step @law (= (str.in_re s r) (str.in_re t r1)) \
        \:rule cong :premises (@p @q @r) :args ((str.in_re s r))) \
        \(step @done false :rule resolution :premises (@law @denied)))"
      val result = Exn.capture (fn () =>
        let val proof = Q.parse_graph_stream_with_version options
              (SmtLib_Logics.parsedicts_of_logic "ALL") "1.3.4" stream
        in CPC_ProofReplay.prove_graph_proof
          {graph=graph,scope=scope,sources=sources,proof=proof} end) ()
      val _ = TextIO.closeIn stream
      val theorem = Exn.release result
    in exact goal hypotheses theorem;same_tags native theorem end)

  (* Compound relation endpoints have both a name and a constructor spine.
     Chains use the former; schema goals use the latter. Check their bridge
     directly and through the parsed monotonicity route, before realization. *)
  fun compound_regex () =
    let
      val cases =
        [(``reglan_equiv (reglan_star r) (reglan_star t)``,
          [``reglan_equiv (reglan_star r) u``,
           ``reglan_equiv u (reglan_star t)``]),
         (``reglan_equiv (reglan_union r q) (reglan_union t q)``,
          [``reglan_equiv (reglan_union r q) u``,
           ``reglan_equiv u (reglan_union t q)``]),
         (``reglan_equiv (reglan_star (reglan_union r q))
                        (reglan_star (reglan_union t q))``,
          [``reglan_equiv (reglan_union r q) u``,
           ``reglan_equiv u (reglan_union t q)``]),
         (``reglan_equiv (reglan_comp r) (reglan_plus t)``,
          [``reglan_equiv u (reglan_comp r)``,
           ``reglan_equiv (reglan_plus t) u``]),
         (``reglan_equiv (reglan_star r) (reglan_star t)``,
          [``reglan_star r = u``, ``u = reglan_star t``]),
         (``reglan_equiv r t``,
          [``reglan_equiv r (reglan_star a)``, ``(a:reglan) = b``,
           ``reglan_equiv (reglan_star b) t``]),
         (``reglan_equiv r t``,
          [``reglan_equiv r (reglan_star a)``, ``reglan_equiv a b``,
           ``reglan_equiv (reglan_star b) t``]),
         (``reglan_equiv r t``,
          [``reglan_equiv r (reglan_star (reglan_star a))``,
           ``reglan_equiv a b``,
           ``reglan_equiv (reglan_star (reglan_star b)) t``]),
         (``smt_in_re s (reglan_star r) = smt_in_re t (reglan_star r')``,
          [``(s:smtstr) = t``, ``reglan_equiv r r'``]),
         (``reglan_equiv (reglan_power (reglan_star r) n)
                        (reglan_power (reglan_star r') m)``,
          [``reglan_equiv r r'``, ``n:num = m``])]
      fun check (i,(goal,hypotheses)) =
        let
          val label = "Task41 compound " ^ Int.toString i
          val _ = testutils.tprint (label ^ " native")
          val native = SmtRegLanProve.congruence
            (map Thm.ASSUME hypotheses) goal
          val _ = exact goal hypotheses native
          val _ = testutils.OK ()
          fun verify theorem =
            (exact goal hypotheses theorem;same_tags native theorem)
          val _ = testutils.tprint (label ^ " compact")
          val _ = with_graph (fn graph => fn scope =>
            let
              val target = import graph scope goal
              val inputs = map (import graph scope) hypotheses
              val unused = import graph scope ``unused_compound:bool``
              val block = P.prepare_needed_sources graph
                {scope=scope,roots=target::unused::inputs,
                 sources=inputs @ [unused],template_limit=limit}
              val edge = R.assemble graph block
                {rule="cong",target=target,
                 premises=Lib.enumerate 0 (inputs @ [unused])
                   |> map (fn (i,node) => (node,P.source block i))}
            in verify (P.realize block target edge) end)
          val _ = testutils.OK ()
          val _ = testutils.tprint (label ^ " parsed Z3")
          val tokens = List.tabulate (length hypotheses,
            fn i => "p" ^ Int.toString i)
          val bindings = ListPair.zip (tokens,hypotheses) @ [("g",goal)]
          val certificate = "((proof (monotonicity " ^
            String.concatWith " " (map (fn p => "(asserted " ^ p ^ ")")
              tokens) ^ " g)))"
          val _ = Z3_CompactReplayTests.with_proof bindings certificate
            (fn graph => fn scope => fn proof => verify
              (Z3_CompactReplayTests.replay graph scope proof limit
                (Z3_CompactReplayTests.fixed graph proof)))
        in testutils.OK () end
      val _ = List.app check (Lib.enumerate 1 cases)
      val _ = with_graph (fn graph => fn scope =>
        let
          val (goal,hypotheses) = hd cases
          val native = SmtRegLanProve.congruence
            (map Thm.ASSUME hypotheses) goal
          val sources = SmtReplaySource.new graph scope limit
            {goal=goal,assumptions=hypotheses}
          val options = Z3_CompactReplayTests.options graph scope
            [("r",``r:reglan``),("u",``u:reglan``),("t",``t:reglan``)]
          val stream = TextIO.openString
            "((assume @p (= (re.* r) u)) \
            \(assume @q (= u (re.* t))) \
            \(assume @denied (not (= (re.* r) (re.* t)))) \
            \(step @law (= (re.* r) (re.* t)) \
            \:rule cong :premises (@p @q) :args ((re.* r))) \
            \(step @done false :rule resolution :premises (@law @denied)))"
          val result = Exn.capture (fn () =>
            let val proof = Q.parse_graph_stream_with_version options
                  (SmtLib_Logics.parsedicts_of_logic "ALL") "1.3.4" stream
            in CPC_ProofReplay.prove_graph_proof
              {graph=graph,scope=scope,sources=sources,proof=proof} end) ()
          val _ = TextIO.closeIn stream
          val theorem = Exn.release result
        in exact goal hypotheses theorem;same_tags native theorem end)
      val _ = with_graph (fn graph => fn scope =>
        let
          val (goal,hypotheses) = hd cases
          val target = import graph scope goal
          val input = import graph scope (hd hypotheses)
          val block = P.prepare_needed_sources graph
            {scope=scope,roots=[target,input],sources=[input],
             template_limit=limit}
        in require "compound regex accepted a missing chain link"
          (declines (fn () => SOME (R.assemble graph block
            {rule="cong",target=target,
             premises=[(input,P.source block 0)]}))) end)
    in () end

  (* Premise patterns and successful proof priority are observable through
     actual Hyp. Test the same parsed certificate against native replay,
     individual-leaf assembly, and both graph freeze/owned routes. *)
  fun regex_premise_priority () =
    let
      val star = ``reglan_equiv (reglan_star r) (reglan_star t)``
      val children = [``reglan_equiv r u``,``reglan_equiv u t``]
      val endpoints = [``reglan_equiv (reglan_star r) v``,
        ``reglan_equiv v (reglan_star t)``]
      (* Use the native law's actual residual variable, not its spelling.
         This law precedes star congruence and must retain its exact Hyp
         even though matching its conclusion does not bind the middle. *)
      val generic = Drule.SPEC_ALL smtstringTheory.reglan_equiv_trans
      val (antecedents,_) = boolSyntax.strip_imp (Thm.concl generic)
      val (first,_) = boolSyntax.dest_conj (hd antecedents)
      val (_,middle) = SmtRegLanProve.dest_equiv first
      val (lhs,rhs) = SmtRegLanProve.dest_equiv star
      val residual = [SmtRegLanProve.mk_equiv (lhs,middle),
        SmtRegLanProve.mk_equiv (middle,rhs)]
      val typed_namesake = Term.mk_var
        (#1 (Term.dest_var middle),Type.bool)
      fun double 0 term = term
        | double n term = double (n-1) (boolSyntax.mk_conj (term,term))
      val oversized_unused = double 13 ``unused_large:bool``
      fun shared_regex 0 term = term
        | shared_regex n term = shared_regex (n-1)
            (Term.list_mk_comb (``reglan_union``,[term,term]))
      val opaque = shared_regex 11 ``r:reglan``
      val opaque_goal = SmtRegLanProve.mk_equiv (opaque,``t:reglan``)
      val opaque_equality = boolSyntax.mk_eq (opaque,``t:reglan``)
      fun union a b = Term.list_mk_comb (``reglan_union``,[a,b])
      val mixed = SmtRegLanProve.mk_equiv
        (union opaque ``r:reglan``,union opaque ``t:reglan``)
      val patterned = SmtRegLanProve.mk_equiv
        (union opaque ``r:reglan``,union ``t:reglan`` ``s:reglan``)
      val whole_pattern = boolSyntax.mk_conj
        (opaque_goal,``reglan_equiv r s``)
      val large_conjunct = boolSyntax.mk_conj
        (``reglan_equiv r t``,opaque_goal)
      val cases =
        [(star,[``reglan_equiv r t /\ spare``]),
         (star,[``spare /\ (reglan_equiv r t /\ spare2)``]),
         (star,[``reglan_equiv r u /\ reglan_equiv u t``]),
         (star,children @ endpoints),
         (star,endpoints @ children),
         (star,[``reglan_equiv r t``] @ endpoints),
         (``smt_in_re s (reglan_star r) = smt_in_re s (reglan_star t)``,
           children @ endpoints),
         (star,[``(r:reglan) = t /\ spare``]),
         (``reglan_equiv r t``,
           [``reglan_equiv r t``,``(r:reglan) = t``,oversized_unused]),
         (opaque_goal,[opaque_goal,opaque_equality]),
         (opaque_goal,[opaque_equality,opaque_goal]),
         (mixed,[``reglan_equiv r t``,mixed]),
         (mixed,[mixed,``reglan_equiv r t``]),
         (patterned,[whole_pattern,patterned]),
         (patterned,[patterned,whole_pattern]),
         (star,[large_conjunct]),
         (``reglan_equiv r t``,[``reglan_equiv r t``,``(r:reglan) = t``,
           double 13 ``reglan_equiv u v``,
           double 13 ``reglan_equiv u v``]),
         (star,residual @ [``reglan_equiv r t``]),
         (star,``reglan_equiv r t`` :: List.rev residual),
         (star,[boolSyntax.list_mk_conj residual,``reglan_equiv r t``]),
         (star,[typed_namesake,``reglan_equiv r t``] @ endpoints)]
      fun check (i,(goal,premises)) =
        let
          val native = SmtRegLanProve.congruence
            (map Thm.ASSUME premises) goal
          fun verify theorem =
            (exact goal (Thm.hyp native) theorem;same_tags native theorem)
          val tokens = List.tabulate (length premises,
            fn i => "p" ^ Int.toString i)
          val bindings = ListPair.zip (tokens,premises) @ [("g",goal)]
          val certificate = "((proof (monotonicity " ^
            String.concatWith " " (map (fn p => "(asserted " ^ p ^ ")")
              tokens) ^ " g)))"
          val label = "Task41 premise priority " ^ Int.toString i
          val _ = testutils.tprint (label ^ " native Z3")
          val (types,terms) = SmtLib_Logics.parsedicts_of_logic "ALL"
          val terms = List.foldl (fn ((token,term),dict) =>
            Library.extend_dict
              ((token,SmtLib_Theories.K_zero_zero term),dict)) terms bindings
          val stream = TextIO.openString certificate
          val result = Exn.capture (fn () => verify
            (Z3_ProofReplay.replay_root_for_test
              (Z3_ProofParser.parse_stream_with_version (types,terms)
                "4.15.3" stream))) ()
          val _ = TextIO.closeIn stream
          val _ = Exn.release result
          val _ = testutils.OK ()
          val _ = testutils.tprint (label ^ " compact")
          val _ = with_graph (fn graph => fn scope =>
            let
              val target = import graph scope goal
              val inputs = map (import graph scope) premises
              val block = P.prepare_needed_sources graph
                {scope=scope,roots=target::inputs,sources=inputs,
                 template_limit=limit}
              val edge = R.assemble graph block
                {rule="cong",target=target,premises=Lib.enumerate 0 inputs
                  |> map (fn (i,node) => (node,P.source block i))}
            in verify (P.realize block target edge) end)
          val _ = testutils.OK ()
          fun parsed owned =
            (testutils.tprint (label ^ (if owned then " owned Z3"
               else " graph Z3"));
             Z3_CompactReplayTests.with_proof bindings certificate
               (fn graph => fn scope => fn proof => verify
                 (if owned then Z3_CompactReplayTests.owned_replay
                    graph scope proof goal premises
                    (Z3_CompactReplayTests.fixed graph proof)
                  else Z3_CompactReplayTests.replay graph scope proof limit
                    (Z3_CompactReplayTests.fixed graph proof)));
             testutils.OK ())
        in List.app parsed [false,true] end
      fun declaration kind = with_graph (fn graph => fn scope =>
        let
          val target = import graph scope star
          val child = import graph scope ``reglan_equiv r t``
          val left = import graph scope lhs
          val right = import graph scope rhs
          val other = G.variable graph scope kind middle
          fun relation a b = G.application graph scope
            (G.application graph scope
              (G.constant graph scope SmtRegLanProve.equiv_tm,a),b)
          val inputs = [relation left other,relation other right,child]
          val block = P.prepare_needed_sources graph
            {scope=scope,roots=target::inputs,sources=inputs,
             template_limit=limit}
          val edge = R.assemble graph block
            {rule="cong",target=target,premises=Lib.enumerate 0 inputs
              |> map (fn (i,node) => (node,P.source block i))}
          val native = SmtRegLanProve.congruence
            [Thm.ASSUME ``reglan_equiv r t``] star
          val theorem = P.realize block target edge
        in exact star (Thm.hyp native) theorem;
           same_tags native theorem end)
    in List.app check (Lib.enumerate 1 cases);
       List.app (fn (label,kind) =>
         (testutils.tprint ("Task41 residual declaration " ^ label);
          declaration kind;testutils.OK ()))
         [("generated",G.Generated),("solver",G.SolverFlexible),
          ("bound",G.Bound)]
    end

  (* Binder operands cannot be expanded through constructor equations.
     Exercise the existing bounded variable-only law boundary BEFORE freeze,
     through both proof formats, rather than treating a predicate as a name. *)
  fun regex_binders () =
    let
      val goal = ``reglan_equiv r t``
      fun check premise =
        let
          val native = SmtRegLanProve.congruence [Thm.ASSUME premise] goal
          fun verify theorem =
            (exact goal [premise] theorem;same_tags native theorem)
          val unused = ``unused_binder:bool``
          val bindings = [("g",goal),("p",premise),("r",``r:reglan``),
            ("unused",unused)]
          val _ = List.app (fn owned =>
            (testutils.tprint (if owned then "Task41 binder owned Z3"
               else "Task41 binder graph Z3");
             Z3_CompactReplayTests.with_proof bindings
              "((proof (monotonicity (asserted p) (asserted unused) g)))"
              (fn graph => fn scope => fn proof => verify
                (if owned then Z3_CompactReplayTests.owned_replay
                   graph scope proof goal [premise,unused]
                   (Z3_CompactReplayTests.fixed graph proof)
                 else Z3_CompactReplayTests.replay graph scope proof limit
                   (Z3_CompactReplayTests.fixed graph proof)));
             testutils.OK ())) [false,true]
          val _ = testutils.tprint "Task41 binder parsed CPC"
          val _ = with_graph (fn graph => fn scope =>
            let
              val sources = SmtReplaySource.new graph scope limit
                {goal=goal,assumptions=[premise]}
              val options = Z3_CompactReplayTests.options graph scope bindings
              val stream = TextIO.openString
                "((assume @p p) (assume @denied (not g)) \
                \(step @law g :rule cong :premises (@p) :args (r)) \
                \(step @done false :rule resolution \
                \:premises (@law @denied)))"
              val result = Exn.capture (fn () =>
                let val proof = Q.parse_graph_stream_with_version options
                      (SmtLib_Logics.parsedicts_of_logic "ALL") "1.3.4" stream
                in CPC_ProofReplay.prove_graph_proof
                  {graph=graph,scope=scope,sources=sources,proof=proof} end) ()
              val _ = TextIO.closeIn stream
            in verify (Exn.release result) end)
        in testutils.OK () end
      val _ = List.app check
        [``!x y:reglan. reglan_equiv x y``,
         ``!x y:reglan. reglan_equiv x y /\ spare``]
    in require "false quantified regex premise accepted"
      (declines (fn () => Z3_CompactReplayTests.with_proof
        [("g",goal),("p",``!x:reglan. reglan_equiv x x``)]
        "((proof (monotonicity (asserted p) g)))"
        (fn graph => fn scope => fn proof => SOME
          (Z3_CompactReplayTests.replay graph scope proof limit
            (Z3_CompactReplayTests.fixed graph proof))))) end

  (* Unknown inclusive inventory must be checked/observed BEFORE native
     count-only binder opening, not retrospectively by prove_admitted. *)
  fun binder_admission () =
    let
      val term = ``!x:bool. !y:bool. x /\ y``
      val inclusive = valOf (I.bounded_binder_size 100 term)
      val checks = ref 0
      val visits = ref 0
      fun count cap = I.bounded_binder_size_with_type_check_observed
        {limit=cap,observe=fn () => visits := !visits+1,
         check_type=fn _ => checks := !checks+1} term
      val _ = require "inclusive binder cutoff changed"
        (count (inclusive-1) = NONE andalso
         count inclusive = SOME inclusive andalso
         count (inclusive+1) = SOME inclusive andalso !checks >= 6)
      val short_visits = !visits
      val _ = ignore (count 1)
      val _ = require "rejected inclusive visits were not observed"
        (!visits > short_visits)
      fun shared 0 = Type.bool
        | shared n = let val ty = shared (n-1)
                     in Type.mk_type ("fun",[ty,ty]) end
      val hidden = shared 21
      val u = Term.mk_var ("task41_u",Type.bool)
      val v = Term.mk_var ("task41_v",Type.bool)
      val z = Term.mk_var ("task41_z",hidden)
      val inner = Term.mk_abs (v,z)
      val f = Term.mk_var ("task41_f",Type.mk_type ("fun",[hidden,Type.bool]))
      val body = Term.mk_comb (f,Term.mk_comb (inner,u))
      val buried = boolSyntax.mk_forall (u,body)
      exception BeforeInner
      val opened_types = ref ([] : Type.hol_type list)
      val _ = require "nested binder was opened without prospective Type check"
        ((ignore (I.bounded_binder_size_with_type_check_observed
          {limit=100,observe=fn () => (),check_type=fn ty =>
            (opened_types := ty :: !opened_types;
             if length (!opened_types)=2 then raise BeforeInner else ())}
          buried);false)
         handle BeforeInner =>
           length (!opened_types)=2 andalso
           #1 (Type.dest_type (#2 (Type.dom_rng (hd (!opened_types))))) =
             "fun")
      val _ = with_graph (fn graph => fn scope =>
        let
          val target = import graph scope ``reglan_equiv r t``
          val premise = import graph scope buried
          val law = R.implication graph scope [premise] target
          val _ = require "binder test unexpectedly has known inventory"
            (G.unfolded_nodes graph G.BinderInclusiveNodes 200000 law = NONE)
          val proof : Z3_GraphProofParser.proof =
            {steps=Redblackmap.mkDict Z3_GraphProofParser.compare_id,
             root=Z3_GraphProofParser.Anonymous 0,vars=[],
             z3_version="4.15.3",close=fn () => ()}
          val request : ZR.local_request =
            {rule=valOf (Z3_Proof.lookup_rule "4.15.3" "monotonicity"),
             metadata=NONE,target=target,premises=[premise],arguments=[],
             law=law}
          fun invoke observe = Z3_ProofReplay.graph_bounded_local_law_using
            observe graph [] proof request
          val _ = require "hidden binder Type escaped original admission"
            ((ignore (invoke (fn _ => ()));false)
             handle Feedback.HOL_ERR detail =>
               Feedback.message_of detail =
                 Feedback.message_of
                   ((SmtResource.check_dag_size_with_limit "BitVector"
                      "word-graph-primitive-type-tree"
                      SmtResource.max_bv_replay_term_nodes
                      (SmtResource.max_bv_replay_term_nodes+1);
                     raise Fail "Type overflow admitted")
                    handle Feedback.HOL_ERR expected => expected))
          fun callback_failure error =
            let val calls = ref 0
                fun observe _ =
                  (calls := !calls+1;if !calls=1000 then raise error else ())
                val actual = Exn.capture (fn () => invoke observe) ()
            in require "prospective callback was swallowed or retried"
              (!calls=1000 andalso
               case actual of Exn.Exn exn =>
                 Feedback.exn_to_string exn = Feedback.exn_to_string error
               | _ => false) end
        in List.app callback_failure
          [Fail "Task41 prospective callback",
           Feedback.mk_HOL_ERR "Task41" "prospective" "callback"] end)
    in () end

  (* Preserve native TRUST's earlier FP/private-marker deferral. String
     naming must not close/reject ASSUME target before the existing force
     boundary. Use the real worker and a checked force proof, once each. *)
  fun deferred_priority () =
    let
      (* Allocate a genuine private marker of the original String type. *)
      val stream = TextIO.openString
        "((define @m () (@fp.INF String)) (assume @p (= @m @m)))"
      val parsed = Exn.capture (fn () => Q.parse_stream_with_version
        (SmtLib_Logics.parsedicts_of_logic "ALL") "1.3.4" stream) ()
      val _ = TextIO.closeIn stream
      (* A saved term alone does not retain proof-local allocation metadata.
         Restore the owning proof scope at each real callback boundary. *)
      val marker_proof = Exn.release parsed
      fun with_marker action input =
        Q.with_cpc_fp_private_proof marker_proof action input
      val marker = case Q.cpc_fp_private_unbound_markers () of
          [(marker,"@fp.INF")] => marker
        | _ => raise Fail "missing String private marker fixture"
      val _ = require "String marker lacks parser identity"
        (Q.is_cpc_fp_private_marker marker)
      val private_goal = boolSyntax.mk_eq (marker,marker)
      val atom = ``binary_ieee$float_is_nan (f:('a,'b) binary_ieee$float)``
      val tautologies = List.tabulate (90,fn i =>
        let val p = Term.mk_var ("task41_pad_" ^ Int.toString i,Type.bool)
        in boolSyntax.mk_eq (p,p) end)
      val mixed_goal = boolSyntax.list_mk_conj
        (boolSyntax.mk_eq (string_variable,string_variable) ::
         boolSyntax.mk_imp (atom,atom) :: tautologies)
      fun check (private,goal) = with_graph (fn graph => fn scope =>
        let
          val sources = SmtReplaySource.new graph scope limit
            {goal=goal,assumptions=[]}
          val target = #node (SmtReplaySource.goal_source sources)
          val _ = require "deferred fixture accidentally became arithmetic/Seq"
            (not (A.has_numeric_operand graph scope
              {inputs=[target],observe=fn () => ()}) andalso
             not (SmtReplayStructured.has_sequence_operand graph scope
              {inputs=[target],observe=fn () => ()}))
          fun loc node = located scope node
          val proof:Q.graph_proof =
            {cvc_version="1.3.4",commands=
              [Q.GraphAssume ("@denied",loc
                 (SmtReplaySource.denied_goal_node sources)),
               Q.GraphStep {pop=false,step=
                 {id="@trust",rule=registered "trust",premises=[],
                  conclusion=SOME (loc target),
                  args=[Q.GraphTerm (loc target)],
                  raw_conclusion=NONE,raw_args=[]}},
               Q.GraphStep {pop=false,step=
                 {id="@done",rule=registered "resolution",
                  premises=["@trust","@denied"],
                  conclusion=SOME (loc (G.constant graph scope boolSyntax.F)),
                  args=[],raw_conclusion=NONE,raw_args=[]}}]}
          val calls = ref 0
          val forced = ref 0
          val private_targets = ref 0
          val deferred = ref 0
          fun worker input = with_marker (fn input =>
            let
              val _ = calls := !calls+1
              val (step:CPC_Proof.step,_) = input
              val term = #term (valOf (#conclusion step))
              val _ = if List.exists Q.is_cpc_fp_private_marker
                  (Term.free_vars term) then
                    private_targets := !private_targets+1 else ()
              val result as (theorem,_) =
                CPC_ProofReplay.graph_bounded_worker [] input
              val _ = if List.exists (Term.aconv term) (Thm.hyp theorem)
                then deferred := !deferred+1 else ()
            in result end) input
          fun force input = with_marker (fn (step:CPC_Proof.step,_) =>
            let val _ = forced := !forced+1
                val _ = require "String force lost its private allocation"
                  (not private orelse Q.is_cpc_fp_private_marker marker)
                val result = valOf (#conclusion step)
                val theorem = simpLib.SIMP_PROVE boolSimps.bool_ss []
                  (#term result)
            in (theorem,result) end) input
          val outcome = Exn.capture (with_marker (fn () =>
            CPC_GraphProofReplay.check_contradiction_observing
              {graph=graph,scope=scope,sources=sources,proof=proof,
               ordinary_limit=limit,template_limit=limit,worker=worker,
               force_worker=SOME force,observer=fn _ => ()})) ()
          val _ = require
            ("String changed earlier TRUST deferral/force order: private=" ^
             Bool.toString private ^ " calls=" ^ Int.toString (!calls) ^
             " private_targets=" ^ Int.toString (!private_targets) ^
             " deferred=" ^ Int.toString (!deferred) ^
             " forced=" ^ Int.toString (!forced) ^ " got=" ^
             (case outcome of Exn.Exn error => Feedback.exn_to_string error
              | _ => "success"))
            (!calls=1 andalso !forced=1 andalso !deferred=1 andalso
             !private_targets=(if private then 1 else 0))
          val theorem = Exn.release outcome
        in exact boolSyntax.F [boolSyntax.mk_neg goal] theorem end)
    in require "mixed TRUST fixture no longer selects large native deferral"
         (SmtResource.dag_nodes_up_to 257 mixed_goal > 256);
       List.app check [(true,private_goal),(false,mixed_goal)]
    end

  fun run () = List.app (fn (name,action) =>
    (testutils.tprint ("Task41 String " ^ name);
     action ();testutils.OK ()))
    [("schemas/sharing",schemas_and_sharing),("context",contextual),
     ("Z3 identity",z3_identity),("CPC identity",cpc_identity),
     ("CPC roles",cpc_cases),("parsed Z3",parsed_z3),
     ("parsed CPC",parsed_cpc),("regex fallback/negatives",regex_congruence),
     ("parsed regex fallback",parsed_regex),
     ("compound regex bridges",compound_regex),
     ("regex premise priority",regex_premise_priority),
     ("regex binder laws",regex_binders),
     ("prospective binder admission",binder_admission),
     ("deferred priority",deferred_priority)]
end
