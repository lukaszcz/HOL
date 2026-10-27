(* Missing-invariant controls for compact arithmetic, not another prover. *)
structure SmtReplayArithmeticTests =
struct
  open HolKernel Parse boolLib bossLib
  structure G = SmtReplayGraph
  structure A = SmtReplayArithmetic
  structure R = SmtReplayRules
  structure Q = CPC_ProofParser
  structure F = SmtLib_GraphFrontend
  structure W = SmtReplayInvocationWork
  val limit = 4096
  fun require message yes = if yes then () else raise Fail message
  fun exact term hypotheses theorem =
    (require ("arithmetic endpoint changed: " ^ term_to_string
       (Thm.concl theorem) ^ " expected " ^ term_to_string term)
       (Thm.concl theorem ~~ term);
     require ("arithmetic hypotheses changed: " ^ String.concatWith ","
       (List.map term_to_string (Thm.hyp theorem))) (HOLset.equal
       (Thm.hypset theorem,HOLset.addList (Term.empty_tmset,hypotheses)));
     Library.check_oracle_tags "SmtReplayArithmeticTests" "exact" theorem)
  fun refuses action =
    (action ();false) handle Feedback.HOL_ERR _ => true
      | HolSatLib.SAT_cex _ => true
  fun with_graph action =
    let val graph = G.new () val scope = G.root_scope graph
        val outcome = Exn.capture (fn () => action graph scope) ()
        val cleanup = Exn.capture (fn () => G.close_scope graph scope) ()
    in case outcome of Exn.Exn primary => raise primary
      | Exn.Res result => (Exn.release cleanup;result) end
  fun import graph scope term = #node (G.import graph scope limit term)
  fun disjoint originals terms =
    let val vars = Term.FVL terms Term.empty_tmset
    in List.all (fn variable => not (HOLset.member (vars,variable)))
         (HOLset.listItems (Term.FVL originals Term.empty_tmset)) end

  (* Every original operator, numeral and shared child must survive. No
     whitelist of linear heads, fixed prefix depth or renamed native source
     operand is allowed to stand in for a checked operator relationship. *)
  fun operators () = with_graph (fn graph => fn scope =>
    let
      val expressions =
        [``(x:num) + y * 2 - 1``, ``MAX (x:num) (MIN y 2)``,
         ``(x:num) DIV y``, ``(x:num) MOD y``, ``(x:num) ** n``,
         ``(x:int) + y * 2 - 1``, ``ABS (x:int)``,
         ``int_max (x:int) (int_min y 2)``,
         ``(x:int) / y``, ``(x:int) % y``,
         ``int_quot (x:int) y``, ``int_rem (x:int) y``,
         ``ediv (x:int) y``, ``emod (x:int) y``,
         ``HolSmt$smt_ediv_total (x:int) y``,
         ``HolSmt$smt_emod_total (x:int) y``,
         ``(x:int) ** n``, ``&(x:num):int``, ``Num (x:int)``,
         ``(x:real) + y * 2 - 1``, ``abs (x:real)``,
         ``max (x:real) (min y 2)``, ``(x:real) / y``,
         ``HolSmt$smt_rdiv (x:real) y``, ``(x:real) pow n``,
         ``real_of_int (x:int)``, ``&(x:num):real``,
         ``if p then x:int else y``, ``(x:int) < y``,
         ``(x:int) <= y``, ``(x:real) > y``, ``(x:real) >= y``,
         ``LENGTH (xs:'a word list)``]
      fun check original =
        let val node = import graph scope original
            fun procedure [left,right] =
                  (require "source variables reached arithmetic"
                     (disjoint [original] [left,right]);
                   require "shared graph operand got distinct holes"
                     (Portable.pointer_eq (left,right));
                   let val (substitution,type_substitution) =
                         Term.match_term original left
                   in require "arithmetic operator or literal was hidden"
                     (null type_substitution andalso List.all
                       (fn {residue,...} => Term.is_var residue) substitution)
                   end;
                   Thm.REFL left)
              | procedure _ = raise Fail "wrong input arity"
            val result = A.prove graph scope
              {inputs=[node,node],template_limit=limit,
               observe=fn _ => (),procedure=procedure}
        in exact (boolSyntax.mk_eq (original,original)) []
             (#theorem result) end
    in List.app check expressions end)

  fun negatives () = with_graph (fn graph => fn scope =>
    let
      val original = ``(x:int) = 1``
      val node = import graph scope original
      fun run procedure = ignore (A.prove graph scope
        {inputs=[node],template_limit=limit,observe=fn _ => (),
         procedure=procedure})
      val _ = require "false rigid source assignment accepted"
        (refuses (fn () => run (fn [term] =>
          Z3_ProofReplay.arith_prove_for_test term
          | _ => raise Fail "arity")))
      val _ = require "extra arithmetic Hyp accepted"
        (refuses (fn () => run (fn [term] => Thm.ASSUME term
          | _ => raise Fail "arity")))
      val _ = require "unowned arithmetic worker variable accepted"
        (refuses (fn () => run (fn _ => Thm.REFL ``foreign:int``)))
      val bound = ``\u:int. u + x``
      val binder = import graph scope bound
      val result = A.prove graph scope
        {inputs=[binder],template_limit=limit,observe=fn _ => (),
         procedure=fn [term] =>
           (require "bounded binder syntax was hidden"
              (Term.is_abs term andalso disjoint [bound] [term]);Thm.REFL term)
           | _ => raise Fail "arity"}
      val _ = exact (boolSyntax.mk_eq (bound,bound)) [] (#theorem result)
      val beta = ``(\u:int. u + 1) x = x + 1``
      val result = A.prove graph scope
        {inputs=[import graph scope beta],template_limit=limit,
         observe=fn _ => (),procedure=fn [term] =>
           Library.arith_prove_with_cases term
           | _ => raise Fail "arity"}
      val _ = exact beta [] (#theorem result)
      val x = ``x:int``
      val xnode = import graph scope x
      val collision = Term.mk_var
        ("__smt_arith_" ^ StringCvt.padLeft #"0" 16
           (Int.fmt StringCvt.HEX (G.node_id xnode)),intSyntax.int_ty)
      val beta = boolSyntax.mk_eq
        (Term.mk_comb (Term.mk_abs (collision,
           intSyntax.mk_plus (collision,x)),``0:int``),x)
      val result = A.prove graph scope
        {inputs=[import graph scope beta],template_limit=limit,
         observe=fn _ => (),procedure=fn [term] =>
           Library.arith_prove_with_cases term
           | _ => raise Fail "arity"}
      val _ = exact beta [] (#theorem result)
      val calls = ref 0
      fun counted _ = (calls := !calls+1;boolTheory.TRUTH)
      val _ = require "over-limit arithmetic ran its procedure"
        (refuses (fn () => ignore (A.prove graph scope
          {inputs=[node],template_limit=1,observe=fn _ => (),
           procedure=counted})) andalso !calls=0)
      val other = G.new () val root = G.root_scope other
      val foreign = import other root original
      val _ = require "foreign cached arithmetic root accepted"
        (refuses (fn () => ignore (A.prove graph scope
          {inputs=[node,foreign],template_limit=limit,observe=fn _ => (),
           procedure=counted})) andalso !calls=0)
      val _ = G.close_scope other root
      val sentinel = "arithmetic observer sentinel"
      val raised = ((ignore (A.prove graph scope
        {inputs=[node],template_limit=limit,
         observe=fn _ => raise Fail sentinel,procedure=counted});false)
        handle Fail message => message=sentinel)
    in require "arithmetic observer error was retried or replaced"
         (raised andalso !calls=0) end)

  fun classification () = with_graph (fn graph => fn scope =>
    let
      fun numeric node = A.has_numeric_operand graph scope
        {inputs=[node],observe=fn () => ()}
      val hidden = #node (G.admit_binder graph scope limit
        ``\u:bool. (x:int) + 0 = x``)
      val plain = #node (G.admit_binder graph scope limit ``\u:bool. u``)
      val unknown = #node (G.retain_source graph scope
        ``\u:bool. (x:int) + 1 = x``)
    in require "arithmetic hidden behind Boolean binders was missed"
         (numeric hidden andalso not (numeric plain) andalso numeric unknown)
    end)

  fun annotation_frontier () = with_graph (fn graph => fn scope =>
    let
      fun shared 0 = Type.bool
        | shared n = let val ty = shared (n-1)
                     in Type.mk_type ("fun",[ty,ty]) end
      fun length () =
        let val ty = Type.mk_type ("list",[shared 25])
            val variable = Term.mk_var ("x",ty)
            val operator = Term.mk_thy_const
              {Thy="list",Name="LENGTH",
               Ty=Type.mk_type ("fun",[ty,numSyntax.num])}
        in Term.mk_comb (operator,variable) end
      (* Small raw syntax and outer Type, but two equal, separately allocated
         exponential annotations. A native dest_abs clash would build a typed
         free_vars set before rejecting their annotations. *)
      val term = Term.mk_abs (Term.mk_var ("x",Type.bool),
        numSyntax.mk_plus (length (),length ()))
      val node = #node (G.retain_source graph scope term)
      val called = ref false
      val _ = require "unadmitted binder annotations reached arithmetic"
        (refuses (fn () => ignore (A.prove graph scope
          {inputs=[node],template_limit=limit,observe=fn _ => (),
           procedure=fn _ => (called := true;boolTheory.TRUTH)})) andalso
         not (!called))
    in () end)

  fun identities () = with_graph (fn graph => fn scope =>
    let
      val x = ``x:int``
      val rigid = G.variable graph scope G.RigidSource x
      val generated = G.variable graph scope G.Generated x
      fun binary constant left right = G.application graph scope
        (G.application graph scope
          (G.constant graph scope constant,left),right)
      val plus = Term.rator (Term.rator ``(x:int) + y``)
      val equality = Term.rator (Term.rator ``(x:int) = y``)
      val goal = binary equality (binary plus rigid generated)
        (binary plus generated rigid)
      fun two_names terms = require "graph identities collapsed in worker"
        (HOLset.numItems (Term.FVL terms Term.empty_tmset)=2)
      fun dependencies expected node =
        case G.free_variable_nodes graph node of
          SOME actual => require "arithmetic variable kind/scope changed"
            (length actual=length expected andalso
             List.all (fn node => List.exists (fn other => node=other) actual)
               expected)
        | NONE => raise Fail "arithmetic dependencies became unknown"
      val result = A.prove graph scope
        {inputs=[goal],template_limit=limit,observe=fn _ => (),
         procedure=fn terms => (two_names terms;
           Library.arith_prove_with_cases (hd terms))}
      val _ = dependencies [rigid,generated] (#node result)
      val binder = import graph scope ``\u:int. u + x``
      fun check frame direct reversed =
        let
          val inputs = if reversed then [direct,binder] else [binder,direct]
          val result = A.prove graph frame
            {inputs=inputs,template_limit=limit,observe=fn _ => (),
             procedure=fn terms =>
               let val _ = two_names terms
                   val direct = List.nth (terms,if reversed then 0 else 1)
                   val original = List.nth (terms,if reversed then 1 else 0)
                   val fresh = Term.mk_abs (``v:int``,
                     intSyntax.mk_plus (direct,direct))
               in Thm.CONJ (Thm.REFL original) (Thm.REFL fresh) end}
          val _ = dependencies [rigid,direct] (#node result)
          val conjuncts = valOf (R.operands graph boolSyntax.conjunction 2
            (#node result))
          val equation = List.nth (conjuncts,1)
          val abstraction = hd (valOf (R.operands graph boolSyntax.equality 2
            equation))
          val _ = G.binder_closure_data graph frame
            (G.binder_closure graph frame abstraction)
        in () end
      val _ = check scope generated false
      val _ = check scope generated true
      val child = G.new_scope graph scope []
      val scoped = G.variable graph child G.Generated x
      val _ = check child scoped false
      val _ = check child scoped true
      val _ = G.close_scope graph child
    in () end)

  fun binder_identities () = with_graph (fn graph => fn scope =>
    let
      val x = ``x:int``
      val rigid = G.variable graph scope G.RigidSource x
      val generated = G.variable graph scope G.Generated x
      val child = G.new_scope graph scope []
      val variable = G.fresh_bound_variable graph child ``u:int``
      val plus = G.constant graph scope
        (Term.rator (Term.rator ``(x:int) + y``))
      val body = G.application graph child
        (G.application graph child (plus,rigid),generated)
      val binder = G.recorded_abstraction graph scope limit
        {binder=variable,body=body,body_frame=child}
      val result = A.prove graph scope
        {inputs=[binder],template_limit=limit,observe=fn _ => (),
         procedure=fn [term] =>
           (require "distinct identities INSIDE binder were merged"
              (HOLset.numItems (Term.FVL [term] Term.empty_tmset)=2);
            Thm.REFL term)
           | _ => raise Fail "arity"}
      val _ = case G.free_variable_nodes graph (#node result) of
          SOME nodes => require "binder result changed declaration identities"
            (length nodes=2 andalso List.exists (fn n => n=rigid) nodes andalso
             List.exists (fn n => n=generated) nodes)
        | NONE => raise Fail "binder result has unknown dependencies"
      (* Legacy bounded literal binders remain supported without a closure
         record. No new constructor permission is inferred from NONE. *)
      val body = G.application graph child
        (G.application graph child (plus,variable),
         import graph scope ``1:int``)
      val legacy = G.abstraction graph scope limit (variable,body)
      val application = G.application graph scope (legacy,rigid)
      val rhs = G.application graph scope
        (G.application graph scope (plus,rigid),import graph scope ``1:int``)
      val equality = G.constant graph scope
        (Term.rator (Term.rator ``(x:int) = y``))
      val goal = G.application graph scope
        (G.application graph scope (equality,application),rhs)
      val result = A.prove graph scope
        {inputs=[goal],template_limit=limit,observe=fn _ => (),
         procedure=fn [term] => Library.arith_prove_with_cases term
           | _ => raise Fail "arity"}
    in exact ``(\u:int. u + 1) x = x + 1`` [] (#theorem result) end)

  fun cpc goal assumptions rule_name arguments declared =
    with_graph (fn graph => fn scope =>
    let
      val sources = SmtReplaySource.new graph scope limit
        {goal=goal,assumptions=assumptions}
      val work = W.begin graph scope sources
        {limits={input_limit=limit,output_limit=limit,template_limit=limit},
         work_limit=10000000}
      fun located node:F.term =
        {node=node,scope=scope,binder_blocks=[],source_syntax=NONE,
         occurrence=SmtLib_Parser.ConstructionOccurrence
           {value=node,role=SmtLib_Parser.ConstructionAtom,
            token="arithmetic",children=[]}}
      val target = #node (SmtReplaySource.goal_source sources)
      val premise_nodes = SmtReplaySource.assumption_nodes sources
      val premise_ids = List.tabulate (length assumptions,fn i =>
        "@p" ^ Int.toString i)
      fun registered name = valOf (CPC_Proof.lookup_rule "1.3.4" name)
      val proof:Q.graph_proof =
        {cvc_version="1.3.4",commands=
          ListPair.mapEq (fn (id,node) => Q.GraphAssume (id,located node))
            (premise_ids,premise_nodes) @
          [Q.GraphAssume ("@denied",located
             (SmtReplaySource.denied_goal_node sources)),
           Q.GraphStep {pop=false,step=
             {id="@arith",rule=registered rule_name,premises=premise_ids,
              conclusion=if declared then SOME (located target) else NONE,
              args=List.map (Q.GraphTerm o located o import graph scope)
                arguments,raw_conclusion=NONE,raw_args=[]}},
           Q.GraphStep {pop=false,step=
             {id="@done",rule=registered "resolution",
              premises=["@arith","@denied"],
              conclusion=SOME (located (G.constant graph scope boolSyntax.F)),
              args=[],raw_conclusion=NONE,raw_args=[]}}]}
      val calls = ref 0
      fun worker (step:CPC_Proof.step,inputs) =
        (calls := !calls+1;
         require "CPC source operands reached generic worker"
           (disjoint (goal::assumptions @ arguments)
             ((case #conclusion step of NONE => []
               | SOME value => [#term value]) @
              List.map #term (inputs @ #args step)));
         CPC_ProofReplay.graph_bounded_worker [] (step,inputs))
      val result = Exn.capture (fn () =>
        let val preprocessing = SmtLib_GraphPreprocess.discover_from_sources
              graph scope sources
              {import_limit=limit,revisit=false,check_type=fn _ => (),
               conversion=fn _ => NONE}
        in CPC_GraphProofReplay.prove_preprocessed_with_work_using work
          {graph=graph,scope=scope,sources=sources,
           preprocessing=preprocessing,proof=proof,ordinary_limit=limit,
           template_limit=limit,worker=worker,force_worker=NONE} end) ()
      val _ = W.close work
      val theorem = Exn.release result
      val _ = require "arithmetic worker was retried or bypassed" (!calls=1)
      val _ = require "CPC arithmetic lost its original Goal object"
        (Portable.pointer_eq (Thm.concl theorem,goal))
    in exact goal (if null assumptions then [] else List.take (assumptions,2))
         theorem end)

  fun cpc_cases () =
    (cpc ``(x:int) < z`` [``(x:int) < y``,``(y:int) < z``]
       "arith" [] true;
     cpc ``(2i > 0i /\ (x:int) < y) ==> 2i*x < 2i*y`` []
       "arith_mult_pos" [``2i``,``(x:int) < y``] true;
     cpc ``(x:int) + 0 = x`` [] "arith_poly_norm"
       [``(x:int) + 0 = x``] false;
     cpc ``(\u:int. u + 1) x = x + 1`` [] "arith" [] true)

  fun parsed_clause () = with_graph (fn graph => fn scope =>
    let
      val assumptions = [``(x:int) <= y``,``(y:int) < x``]
      val sources = SmtReplaySource.new graph scope limit
        {goal=boolSyntax.F,assumptions=assumptions}
      val work = W.begin graph scope sources
        {limits={input_limit=limit,output_limit=limit,template_limit=limit},
         work_limit=10000000}
      val options = Z3_CompactReplayTests.options graph scope
        [("x",``x:int``),("y",``y:int``)]
      val stream = TextIO.openString
        "((assume @p0 (<= x y)) (assume @p1 (< y x)) \
        \(step @law (or (not (<= x y)) (not (< y x))) :rule arith) \
        \(step @part (not (< y x)) :rule resolution \
        \:premises (@law @p0)) \
        \(step @done false :rule resolution :premises (@part @p1)))"
      val proof = Q.parse_graph_stream_with_version options
        (SmtLib_Logics.parsedicts_of_logic "ALL") "1.3.4" stream
      val preprocessing = SmtLib_GraphPreprocess.discover_from_sources
        graph scope sources
        {import_limit=limit,revisit=false,check_type=fn _ => (),
         conversion=fn _ => NONE}
      val theorem =
        CPC_GraphProofReplay.prove_preprocessed_with_clauses_and_work_using
        work {graph=graph,scope=scope,sources=sources,
          preprocessing=preprocessing,proof=proof,ordinary_limit=limit,
          template_limit=limit,worker=CPC_ProofReplay.graph_bounded_worker [],
          clause_worker=
            CPC_ProofReplay.graph_bounded_worker_with_clause work [],
          force_worker=NONE}
      val _ = TextIO.closeIn stream val _ = W.close work
    in exact boolSyntax.F assumptions theorem end)

  fun z3_cases () =
    let
      fun check expected text = Z3_CompactReplayTests.with_proof
        [("x",``x:int``),("y",``y:int``)] text
        (fn graph => fn scope => fn proof =>
          exact expected [] (Z3_CompactReplayTests.replay graph scope proof
            limit (Z3_CompactReplayTests.fixed graph proof)))
    in check ``(x:int) + 2 = 2 + x``
       "((proof ((_ th-lemma arith farkas 1) (= (+ x 2) (+ 2 x)))))";
       check ``(y:int) = 0 \/ ediv 0 y = 0``
       "((proof ((_ th-lemma arith farkas 1) \
       \(or (= y 0) (= (div 0 y) 0)))))";
       Z3_CompactReplayTests.with_proof
         [("x",``x:int``),("y",``y:int``),("z",``z:int``)]
         "((proof ((_ th-lemma arith farkas 1) \
         \(asserted (< x y)) (asserted (< x y)) (asserted (< y z)) \
         \(< x z))))"
         (fn graph => fn scope => fn proof =>
           let val child = G.new_scope graph scope []
               val theorem = Z3_CompactReplayTests.replay graph child proof
                 limit (Z3_CompactReplayTests.fixed graph proof)
               val _ = G.close_scope graph child
           in exact ``(x:int) < z`` [``(x:int) < y``,``(y:int) < z``]
                theorem end);
       Z3_CompactReplayTests.with_proof [("x",``x:int``),("y",``y:int``)]
         "((proof ((_ th-lemma arith farkas 1) (asserted (< x y)) \
         \(= 1 1))))"
         (fn graph => fn scope => fn proof =>
           exact ``(1:int) = 1`` [``(x:int) < y``]
             (Z3_CompactReplayTests.replay graph scope
             proof limit (Z3_CompactReplayTests.fixed graph proof)))
    end

  fun run () =
    (operators ();negatives ();classification ();annotation_frontier ();
     identities ();
     binder_identities ();
     cpc_cases ();parsed_clause ();
     (* The fixed selected Z3 worker is exercised by its parsed fixture. *)
     z3_cases ())
end
