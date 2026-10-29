(* Task41: Unicode String schemas and same-native declaration controls.
   smtstr is a type definition, NOT a datatype with constructors. *)
structure SmtReplayStringTests =
struct
  open HolKernel Parse boolLib bossLib
  open smtstringTheory
  structure H = SmtReplayArithmeticTests
  structure G = SmtReplayGraph
  structure A = SmtReplayArithmetic
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

  (* Preserve native TRUST's earlier FP/private-marker deferral. String
     naming must not close/reject ASSUME target before the existing force
     boundary. Use the real worker and a checked force proof, once each. *)
  fun deferred_priority () =
    let
      val marker = Term.mk_var ("@fp.task41_string",``:smtstr``)
      val private_goal = boolSyntax.mk_eq (marker,marker)
      val atom = ``binary_ieee$float_is_nan (f:('a,'b) binary_ieee$float)``
      val tautologies = List.tabulate (90,fn i =>
        let val p = Term.mk_var ("task41_pad_" ^ Int.toString i,Type.bool)
        in boolSyntax.mk_eq (p,p) end)
      val mixed_goal = boolSyntax.list_mk_conj
        (boolSyntax.mk_eq (string_variable,string_variable) ::
         boolSyntax.mk_imp (atom,atom) :: tautologies)
      fun check goal = with_graph (fn graph => fn scope =>
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
          fun worker input =
            (calls := !calls+1;
             CPC_ProofReplay.graph_bounded_worker [] input)
          fun force (step:CPC_Proof.step,_) =
            let val _ = forced := !forced+1
                val result = valOf (#conclusion step)
                val theorem = simpLib.SIMP_PROVE boolSimps.bool_ss []
                  (#term result)
            in (theorem,result) end
          val theorem = CPC_GraphProofReplay.check_contradiction_observing
            {graph=graph,scope=scope,sources=sources,proof=proof,
             ordinary_limit=limit,template_limit=limit,worker=worker,
             force_worker=SOME force,observer=fn _ => ()}
          val _ = require "String changed earlier TRUST deferral/force order"
            (!calls=1 andalso !forced=1)
        in exact boolSyntax.F [boolSyntax.mk_neg goal] theorem end)
    in require "mixed TRUST fixture no longer selects large native deferral"
         (SmtResource.dag_nodes_up_to 257 mixed_goal > 256);
       List.app check [private_goal,mixed_goal]
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
     ("deferred priority",deferred_priority)]
end
