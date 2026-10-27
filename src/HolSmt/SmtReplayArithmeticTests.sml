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
  structure ZR = Z3_GraphProofReplay
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

  (* A tiny arithmetic term may have annotations larger than its local
     template allowance, while still below the original Type allowance. *)
  fun annotation_allowance () = with_graph (fn graph => fn scope =>
    let
      fun shared 0 = Type.bool
        | shared n = let val ty = shared (n-1)
                     in Type.mk_type ("fun",[ty,ty]) end
      val ty = Type.mk_type ("list",[shared 17])
      val length_head = Term.mk_thy_const
        {Thy="list",Name="LENGTH",
         Ty=Type.mk_type ("fun",[ty,numSyntax.num])}
      fun operand i = intSyntax.mk_injected (Term.mk_comb
        (length_head,Term.mk_var ("xs" ^ Int.toString i,ty)))
      val original = List.foldl (fn (term,total) =>
        intSyntax.mk_plus (total,term)) (operand 0)
          (List.tabulate (37,fn i => operand (i+1)))
      val node = import graph scope original
      val admission = SmtWordGraph.new_type_admission ()
      val _ = List.app (fn child => SmtWordGraph.admit_primitive_type
        admission (G.type_of graph child)) (G.block_reachable graph [node])
      val calls = ref 0
      val paid = ref (0:IntInf.int)
      fun observe amount =
        (paid := !paid+amount;
         require "repeated shared annotations exhausted original Work"
           (!paid <= 10000000))
      val result = A.prove graph scope
        {inputs=[node,node],template_limit=limit,observe=observe,
         procedure=fn [left,right] =>
           (calls := !calls+1;
            require "large annotations changed shared arithmetic operands"
              (Portable.pointer_eq (left,right));
            require "large-annotation source variable reached worker"
              (disjoint [original] [left,right]);
            Thm.REFL left)
           | _ => raise Fail "arity"}
      val _ = require "large-annotation worker was retried or bypassed"
        (!calls=1)
    in exact (boolSyntax.mk_eq (original,original)) [] (#theorem result) end)

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
      val expected =
        ((SmtResource.check_dag_size_with_limit "BitVector"
            "word-graph-primitive-type-tree"
            SmtResource.max_bv_replay_term_nodes
            (SmtResource.max_bv_replay_term_nodes+1);
          raise Fail "original Type gate unexpectedly admitted overflow")
         handle Feedback.HOL_ERR detail => detail)
      val refused =
        ((ignore (A.prove graph scope
           {inputs=[node],template_limit=limit,observe=fn _ => (),
            procedure=fn _ => (called := true;boolTheory.TRUTH)});false)
         handle Feedback.HOL_ERR actual =>
           Feedback.top_structure_of actual =
             Feedback.top_structure_of expected andalso
           Feedback.top_function_of actual =
             Feedback.top_function_of expected andalso
           Feedback.message_of actual = Feedback.message_of expected)
      val _ = require "binder Type gate changed diagnostic or ran worker"
        (refused andalso not (!called))
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
      fun check expected input =
        let
          val calls = ref 0
          val result = A.prove graph scope
            {inputs=[input],template_limit=limit,observe=fn _ => (),
             procedure=fn [term] =>
               (calls := !calls+1;
                require "distinct identities INSIDE binder were merged"
                  (HOLset.numItems (Term.FVL [term] Term.empty_tmset)=
                   length expected);
                Thm.REFL term)
               | _ => raise Fail "arity"}
          val _ = require "binder worker was retried or bypassed" (!calls=1)
          val _ = case G.free_variable_nodes graph (#node result) of
              SOME nodes => require "binder changed declaration IDs/kinds"
                (length nodes=length expected andalso List.all
                   (fn n => List.exists (fn other => n=other) nodes) expected)
            | NONE => raise Fail "binder result has unknown dependencies"
          val original = G.representative graph input
        in exact (boolSyntax.mk_eq (original,original)) []
             (#theorem result) end
      val legacy = G.abstraction graph scope limit (variable,body)
      val _ = require "legacy binder unexpectedly has a closure record"
        (not (Option.isSome
          (G.recorded_binder_closure graph scope legacy)))
      val _ = List.app (check [rigid,generated]) [binder,legacy]
      (* Generated-only control: no rigid declaration or lexical binding
         with this native spelling has been allocated before adaptation. *)
      val generated_only = G.variable graph scope G.Generated
        ``only_generated:int``
      val body = G.application graph child
        (G.application graph child (plus,variable),generated_only)
      val binder = G.recorded_abstraction graph scope limit
        {binder=variable,body=body,body_frame=child}
      val legacy = G.abstraction graph scope limit (variable,body)
      val _ = List.app (check [generated_only]) [binder,legacy]
      (* Legacy beta remains supported without a closure record. No new
         constructor permission is inferred from NONE. *)
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

  datatype cpc_argument = Object of term | Objects of term list
  fun cpc_arguments_using local_limit selected_worker
      goal assumptions rule_name arguments declared =
    with_graph (fn graph => fn scope =>
    let
      val limit = local_limit
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
      fun argument (Object term) =
            Q.GraphTerm (located (import graph scope term))
        | argument (Objects terms) = Q.GraphList
            (List.map (Q.GraphTerm o located o import graph scope) terms)
      val originals = List.concat (List.map (fn Object term => [term]
        | Objects terms => terms) arguments)
      val target = #node (SmtReplaySource.goal_source sources)
      val premise_nodes = SmtReplaySource.assumption_nodes sources
      val premise_ids = List.tabulate (length assumptions,fn i =>
        "@p" ^ Int.toString i)
      fun registered name = valOf (CPC_Proof.lookup_rule "1.3.4" name)
      val structured = Q.graph_structured_rule_arguments
        (registered rule_name)
      val expected_arguments = if structured then arguments else
        List.concat (List.map (fn Object term => [Object term]
          | Objects terms => List.map Object terms) arguments)
      val proof:Q.graph_proof =
        {cvc_version="1.3.4",commands=
          ListPair.mapEq (fn (id,node) => Q.GraphAssume (id,located node))
            (premise_ids,premise_nodes) @
          [Q.GraphAssume ("@denied",located
             (SmtReplaySource.denied_goal_node sources)),
           Q.GraphStep {pop=false,step=
             {id="@arith",rule=registered rule_name,premises=premise_ids,
              conclusion=if declared then SOME (located target) else NONE,
              args=List.map argument arguments,
              raw_conclusion=NONE,raw_args=[]}},
           Q.GraphStep {pop=false,step=
             {id="@done",rule=registered "resolution",
              premises=["@arith","@denied"],
              conclusion=SOME (located (G.constant graph scope boolSyntax.F)),
              args=[],raw_conclusion=NONE,raw_args=[]}}]}
      val calls = ref 0
      fun worker (step:CPC_Proof.step,inputs) =
        (calls := !calls+1;
         require "CPC changed omitted/declared result role"
           (Option.isSome (#conclusion step) = declared);
         require "CPC changed argument role count"
           (length (#args step) = length expected_arguments);
         ListPair.appEq (fn (expected,actual:CPC_Proof.located_term) =>
           case expected of Object original =>
               let val (substitution,types) =
                     Term.match_term original (#term actual)
               in require "CPC hid an object argument's operator or Type"
                 (null types andalso List.all
                   (fn {residue,...} => Term.is_var residue) substitution)
               end
           | Objects terms =>
               let val (elements,ty) = listSyntax.dest_list (#term actual)
               in require "CPC changed structured list arity"
                    (length elements = length terms);
                  require "CPC changed structured metadata provenance"
                    (case #provenance actual of
                       CPC_Proof.UnavailableProvenance _ => true | _ => false);
                  require "CPC changed structured list Type"
                    (ty = (case terms of
                       [] => Type.mk_vartype "'cpc_list"
                     | first::_ => Term.type_of first))
               end) (expected_arguments,#args step);
         require "CPC source operands reached generic worker"
           (disjoint (goal::assumptions @ originals)
             ((case #conclusion step of NONE => []
               | SOME value => [#term value]) @
              List.map #term (inputs @ #args step)));
         selected_worker (step,inputs))
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
    in exact goal assumptions theorem end)

  val cpc_arguments = cpc_arguments_using limit
    (CPC_ProofReplay.graph_bounded_worker [])

  fun cpc goal assumptions rule_name arguments declared =
    cpc_arguments goal assumptions rule_name (List.map Object arguments)
      declared

  fun cpc_cases () =
    (cpc ``(x:int) < z`` [``(x:int) < y``,``(y:int) < z``]
       "arith" [] true;
     cpc ``(2i > 0i /\ (x:int) < y) ==> 2i*x < 2i*y`` []
       "arith_mult_pos" [``2i``,``(x:int) < y``] true;
     cpc ``(x:int) + 0 = x`` [] "arith_poly_norm"
       [``(x:int) + 0 = x``] false;
     cpc ``(\u:int. u + 1) x = x + 1`` [] "arith" [] true;
     (* The middle +0 forces the bounded fallback, not exact/alias trans. *)
     cpc ``(a:int) = b`` [``(a:int) = x + 0``,``(x:int) = b``]
       "trans" [] true;
     cpc ``(x:int) < z``
       [``(x:int) < y``,``(x:int) < y``,``(y:int) < z``]
       "arith" [] true;
     require "duplicate CPC premises invented a missing inequality"
       (refuses (fn () => cpc ``(x:int) < z``
         [``(x:int) < y``,``(x:int) < y``] "arith" [] true));
     (* Ordinary packets flatten, including empty and heterogeneous ones. *)
     cpc_arguments ``(x:int) + 0 = x`` [] "arith_poly_norm"
       [Objects [],Objects [``(x:int) + 0 = x``],Objects []] false;
     cpc_arguments ``(2i > 0i /\ (x:int) < y) ==> 2i*x < 2i*y`` []
       "arith_mult_pos" [Objects [``2i``,``(x:int) < y``]] true;
     List.app (fn rule =>
       cpc_arguments
         ``smt_emod_total (smt_emod_total (r:int) 2) 2 =
           smt_emod_total r 2`` [``~((2:int) = 0)``] rule
         [Object ``2:int``,Objects [],Object ``r:int``,Objects []] false)
       ["arith-mod-over-mod","arith-mod-over-mod-mult"])

  (* These selected workers isolate boundary roles, not arithmetic solving.
     The ordinary worker above separately exercises native packet consumers. *)
  fun cpc_truth (_:CPC_Proof.step,_:CPC_Proof.located_term list) =
    (boolTheory.TRUTH,
     {term=boolSyntax.T,provenance=CPC_Proof.AtomicProvenance})

  fun cpc_packet_boundaries () =
    let
      (* Numeric syntax occurs ONLY in the packet. The generic classifier
         must select arithmetic naming even though the endpoint is Boolean.
         A list-typed object is an operand, not another packet to flatten. *)
      val _ = cpc_arguments_using limit cpc_truth boolSyntax.T [] "evaluate"
        [Objects [``packet_p:bool``,``packet_xs:int list``,``packet_x:int``]]
        true
      val elements = List.tabulate (31,fn _ => ``packet_x:int``)
      fun structured cap worker =
        cpc_arguments_using cap worker boolSyntax.T [] "arith-mod-over-mod"
          [Objects elements] true
      (* NIL costs one node and each variable CONS costs four: exactly 125.
         Ordinary packets must NOT pay for a synthetic native list. *)
      val _ = structured 125 cpc_truth
      val _ = require "structured aggregate exceeded its raw-node cap"
        (refuses (fn () => structured 124
          (fn _ => raise Fail "over-limit structured list reached worker")))
      val _ = cpc_arguments_using 124 cpc_truth boolSyntax.T [] "arith"
        [Objects elements] true
      fun extra_hyp (step:CPC_Proof.step,inputs) =
        let val (theorem,result) = cpc_truth (step,inputs)
        in (Drule.ADD_ASSUM (#term (hd (#args step))) theorem,result) end
      val _ = require "CPC retained an undischarged worker Hyp"
        (refuses (fn () => cpc_arguments_using limit extra_hyp
          boolSyntax.T [] "arith" [Object ``packet_p:bool``] true))
      fun doubled 0 = ``packet_x:int``
        | doubled n = let val term = doubled (n-1)
                      in intSyntax.mk_plus (term,term) end
      val large = doubled 5
      val _ = require "CPC arithmetic lost its ordinary unfolded term cap"
        (refuses (fn () => cpc_arguments_using 124
          (fn _ => raise Fail "over-limit ordinary term reached worker")
          (boolSyntax.mk_eq (large,large)) [] "arith" [] true))
    in () end

  fun cpc_annotations () =
    let
      fun shared 0 = Type.bool
        | shared n = let val ty = shared (n-1)
                     in Type.mk_type ("fun",[ty,ty]) end
      fun goal depth =
        let val ty = listSyntax.mk_list_type (shared depth)
            val xs = Term.mk_var ("cpc_large_xs",ty)
            val operator = Term.mk_thy_const
              {Thy="list",Name="LENGTH",
               Ty=Type.mk_type ("fun",[ty,numSyntax.num])}
            val term = intSyntax.mk_injected (Term.mk_comb (operator,xs))
        in boolSyntax.mk_eq (term,term) end
      (* Its raw term fits 4096, but an annotation has over 8192 nodes. *)
      val _ = cpc (goal 12) [] "arith" [] true
      val expected =
        ((SmtResource.check_dag_size_with_limit "BitVector"
            "word-graph-primitive-type-tree"
            SmtResource.max_bv_replay_term_nodes
            (SmtResource.max_bv_replay_term_nodes+1);
          raise Fail "original CPC Type gate admitted overflow")
         handle Feedback.HOL_ERR detail => detail)
      val refused =
        ((cpc_arguments_using limit
            (fn _ => raise Fail "over-limit CPC Type reached worker")
            (goal 20) [] "arith" [] true;false)
         handle Feedback.HOL_ERR actual =>
           Feedback.top_structure_of actual =
             Feedback.top_structure_of expected andalso
           Feedback.top_function_of actual =
             Feedback.top_function_of expected andalso
           Feedback.message_of actual = Feedback.message_of expected)
    in require "CPC Type quota changed its original primitive diagnostic"
         refused end

  (* Native mod_context folds ts @ [emod r c] @ ss LEFT, with + or *.
     Its simplifier is not a general modular-ring prover. Taking r already
     reduced makes arbitrary nonempty contexts native-valid for both rules,
     rather than asking the adapter to extend the native proof fragment. *)
  fun structured_cases () =
    let
      val reduced = ``smt_emod_total (r:int) 2``
      val prefix = [``a:int``,``b:int``]
      val suffix = [``d:int``,``e:int``]
      fun arguments leading trailing =
        [Object ``2:int``,Objects leading,Object reduced,Objects trailing]
      val cases =
        [("arith-mod-over-mod",
          ``smt_emod_total
              (((((a:int) + b) +
                 smt_emod_total (smt_emod_total r 2) 2) + d) + e) 2 =
            smt_emod_total
              ((((a + b) + smt_emod_total r 2) + d) + e) 2``),
         ("arith-mod-over-mod-mult",
          ``smt_emod_total
              (((((a:int) * b) *
                 smt_emod_total (smt_emod_total r 2) 2) * d) * e) 2 =
            smt_emod_total
              ((((a * b) * smt_emod_total r 2) * d) * e) 2``)]
      fun check (rule,goal) =
        let
          val native = CPC_ProofReplay.replay_rare_rewrite_for_test rule
            [``2:int``,listSyntax.mk_list (prefix,intSyntax.int_ty),
             reduced,listSyntax.mk_list (suffix,intSyntax.int_ty)]
          val _ = exact goal [``~((2:int) = 0)``] native
          val _ = List.app (fn declared =>
            cpc_arguments goal [``~((2:int) = 0)``] rule
              (arguments prefix suffix) declared) [false,true]
          val _ = require "false structured arithmetic result accepted"
            (refuses (fn () => cpc_arguments ``(0:int) = 1``
              [``~((2:int) = 0)``] rule
              (arguments prefix suffix) true))
        in List.app (fn args =>
          require "wrong-typed structured arithmetic list accepted"
            (refuses (fn () => cpc_arguments goal
              [``~((2:int) = 0)``] rule args false)))
          [arguments [boolSyntax.T] suffix,
           arguments prefix [boolSyntax.F]] end
    in List.app check cases end

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

  (* B3: a Boolean false target has numeric PREMISES. Count the classifier
     AND the unfolded preflight separately: only a further observed debit
     demonstrates that the arithmetic adapter, not just dispatch, was paid. *)
  fun z3_false_target () =
    let
      val x = ``arithmetic_false_x:int``
      val assumptions =
        [``(arithmetic_false_x:int) = 0``,
         ``(arithmetic_false_x:int) = 1``]
      val metadata = Z3_Proof.mk_th_lemma_metadata
        ("basic",SOME "eq-propagate",["0"])
      val initial = Z3_Proof.update_proof_vars
        (Z3_Proof.empty_proof "4.15.3")
        (HOLset.add (Term.empty_tmset,x))
      val ordinary = Z3_Proof.update_proof_steps initial
        (Redblackmap.insert (Z3_Proof.proof_steps initial,0,
          Z3_Proof.TH_LEMMA_BASIC (metadata,
            List.map (Z3_Proof.THEOREM o Thm.ASSUME) assumptions,
            boolSyntax.F)))
      val _ = exact boolSyntax.F assumptions
        (Z3_ProofReplay.replay_root_for_test ordinary)
    in Z3_CompactReplayTests.with_proof [("x",x)]
      "((proof ((_ th-lemma basic eq-propagate 0) \
      \(asserted (= x 0)) (asserted (= x 1)) false)))"
      (fn graph => fn scope => fn proof =>
        let
          val sources = SmtReplaySource.new graph scope limit
            {goal=boolSyntax.F,assumptions=assumptions}
          val work = W.begin graph scope sources
            {limits={input_limit=limit,output_limit=limit,
               template_limit=limit},work_limit=10000000}
          val calls = ref 0
          val debits = ref (0:IntInf.int)
          val dispatch = ref (0:IntInf.int)
          fun dispatch_tick () = dispatch := !dispatch+1
          fun observe amount =
            (debits := !debits+amount;W.spend_guard_policy work amount)
          fun local_law (request:ZR.local_request) =
            let
              val _ = calls := !calls+1
              val _ = require "B3 lost its Boolean false target"
                (#target request = G.constant graph scope boolSyntax.F)
              val _ = require "B3 lost its numeric premises"
                (length (#premises request)=2 andalso
                 A.has_numeric_operand graph
                   (G.node_scope graph (#law request))
                   {inputs= #target request :: #premises request,
                    observe=dispatch_tick})
              val _ = List.app (fn node =>
                ignore (G.unfolded_nodes_observed dispatch_tick graph
                  G.BinderInclusiveNodes SmtResource.max_bitblast_term_nodes
                  node))
                (#law request :: List.map #node (#arguments request))
            in Z3_ProofReplay.graph_bounded_local_law_using observe
              graph [] proof request end
          val outcome = Exn.capture (fn () =>
            let
              val preprocessing =
                SmtLib_GraphPreprocess.discover_from_sources
                  graph scope sources
                  {import_limit=limit,revisit=false,check_type=fn _ => (),
                   conversion=fn _ => NONE}
            in
              ZR.check_proof_with_preprocessed_sources_with_work_using
                  work graph scope
                  {sources=sources,preprocessing=preprocessing,proof=proof,
                   template_limit=limit,local_law=local_law,
                   nnf=Z3_ProofReplay.graph_bounded_nnf graph}
            end) ()
          val _ = W.close work
          val theorem = Exn.release outcome
          val _ = exact boolSyntax.F assumptions theorem
          val _ = SmtReplaySource.check_goal sources theorem
          val _ = require "B3 bounded law was retried or bypassed" (!calls=1)
        in require "B3 numeric premises bypassed paid arithmetic adaptation"
             (!debits > !dispatch) end)
    end

  (* The compatibility producer has no recorded-definition ports. Neither a
     Source assignment nor a same-native distinct declaration is a law. *)
  fun z3_rigidity () = with_graph (fn graph => fn scope =>
    let
      val native = Term.mk_var ("arithmetic_rigid",``:int``)
      val rigid = G.variable graph scope G.RigidSource native
      val other = G.variable graph scope G.Generated native
      val zero = import graph scope ``0:int``
      val eq = G.constant graph scope
        (Term.rator (Term.rator ``(a:int) = b``))
      fun equation right = G.application graph scope
        (G.application graph scope (eq,rigid),right)
      val proof : Z3_GraphProofParser.proof =
        {steps=Redblackmap.mkDict Z3_GraphProofParser.compare_id,
         root=Z3_GraphProofParser.Anonymous 0,vars=[],
         z3_version="4.15.3",close=fn () => ()}
      val rule = valOf (Z3_Proof.lookup_rule "4.15.3" "rewrite")
      fun check target =
        let val law = SmtReplayRules.implication graph scope [] target
        in require "non-recorded arithmetic accepted a rigid assignment"
          (refuses (fn () => ignore
            (Z3_ProofReplay.graph_bounded_local_law graph [] proof
              {rule=rule,metadata=NONE,target=target,premises=[],
               arguments=[],law=law}))) end
    in check (equation zero);check (equation other) end)

  (* Generic rule names must not restore native-name equality or grant
     definition authority to arithmetic holes. Pair generic rejections with
     valid requests through BOTH local producers, so unsupported dispatch or
     resource refusal cannot masquerade as an identity check. *)
  fun z3_generic_identities () = with_graph (fn graph => fn root =>
    let
      val scope = G.new_scope graph root []
      val native = ``arithmetic_generic:int``
      val rigid = G.variable graph root G.RigidSource native
      val other = G.variable graph root G.Generated native
      val flexible = G.variable graph root G.SolverFlexible native
      val unused = G.variable graph scope G.SolverFlexible native
      val _ = require "generic controls need distinct same-native IDs"
        (rigid <> other andalso rigid <> flexible andalso
         flexible <> unused andalso List.all (fn node =>
           G.representative graph node ~~ native)
             [rigid,other,flexible,unused])
      fun app operator operand = G.application graph scope (operator,operand)
      fun binary constant left right =
        app (app (G.constant graph scope constant) left) right
      val int_eq = Term.rator (Term.rator ``(a:int) = b``)
      val bool_eq = Term.rator (Term.rator ``(p:bool) = q``)
      val eq = binary int_eq
      val iff = binary bool_eq
      val disj = binary boolSyntax.disjunction
      fun neg node = app (G.constant graph scope boolSyntax.negation) node
      val zero = import graph scope ``0:int``
      val atom = eq rigid zero
      val different_atom = eq other zero
      fun located node:F.term =
        {node=node,scope=scope,binder_blocks=[],source_syntax=NONE,
         occurrence=SmtLib_Parser.ConstructionOccurrence
           {value=node,role=SmtLib_Parser.ConstructionAtom,
            token="generic-arithmetic",children=[]}}
      fun proof variables : Z3_GraphProofParser.proof =
        {steps=Redblackmap.mkDict Z3_GraphProofParser.compare_id,
         root=Z3_GraphProofParser.Anonymous 0,vars=variables,
         z3_version="4.15.3",close=fn () => ()}
      fun request name target premises arguments : ZR.local_request =
        {rule=valOf (Z3_Proof.lookup_rule "4.15.3"
           (String.translate (fn #"_" => "-" | c => String.str c) name)),
         metadata=NONE,
         target=target,premises=premises,arguments=List.map located arguments,
         law=R.implication graph scope premises target}
      fun compatibility variables request = Option.map
        (fn theorem => {definitions=[],theorem=theorem})
        (Z3_ProofReplay.graph_bounded_local_law graph []
          (proof variables) request)
      fun recorded variables request =
        Z3_ProofReplay.graph_bounded_recorded_local_law graph scope limit []
          (proof variables) request
      fun declines action =
        (case action () of NONE => true | SOME _ => false)
        handle Conv.UNCHANGED => true
          | HolSatLib.SAT_cex _ => true
          | Feedback.HOL_ERR detail =>
              if SmtResource.is_resource_gate detail then
                raise Feedback.HOL_ERR detail
              else true
      fun positive label produce (request:ZR.local_request) =
        (case produce request of
          NONE => raise Fail (label ^ " declined valid generic arithmetic")
        | SOME {definitions,theorem} =>
            (require (label ^ " invented generic definitions")
               (null definitions);
             exact (G.representative graph (#law request)) [] theorem))
        handle error => raise Fail (label ^ " positive " ^
          #replay_handler (#rule request) ^ ": " ^
          General.exnMessage error)
      fun paired label produce name good bad premises arguments =
        (positive label produce (request name good premises arguments);
         require (label ^ " accepted mismatched graph IDs for " ^ name)
           (declines (fn () => produce
             (request name bad premises arguments))))
      val binder_scope = G.new_scope graph scope []
      val bound = G.fresh_bound_variable graph binder_scope ``u:bool``
      val abstraction = G.recorded_abstraction graph scope limit
        {binder=bound,body=atom,body_frame=binder_scope}
      val quantified = app
        (G.constant graph scope ``$! : (bool -> bool) -> bool``) abstraction
      (* The predicate stays uninterpreted: mismatched instantiation must
         not become valid just because an arithmetic universal is false. *)
      val predicate = import graph scope
        ``arithmetic_predicate:int -> int -> bool``
      val instance_scope = G.new_scope graph scope []
      val instance_bound =
        G.fresh_bound_variable graph instance_scope ``u:int``
      val universal_body = G.application graph instance_scope
        (G.application graph instance_scope (predicate,instance_bound),rigid)
      val universal = app
        (G.constant graph scope ``$! : (int -> bool) -> bool``)
        (G.recorded_abstraction graph scope limit
          {binder=instance_bound,body=universal_body,
           body_frame=instance_scope})
      val instance = app (app predicate other) rigid
      val instantiation = disj (neg universal) instance
      fun check (label,produce) =
        (paired label produce "commutativity"
           (iff (eq rigid other) (eq other rigid))
           (iff (eq rigid other) (eq rigid rigid)) [] [];
         paired label produce "apply_def"
           (eq zero rigid) (eq zero other) [atom] [];
         paired label produce "def_axiom"
           (disj (neg atom) atom) (disj (neg atom) different_atom) [] [];
         paired label produce "elim_unused"
           (iff quantified atom) (iff quantified different_atom) [] [];
         positive label produce
           (request "quant_inst" instantiation [] [other]);
         positive label produce (request "quant_inst"
           (disj (neg universal) (app (app predicate rigid) rigid))
           [] [rigid]);
         (* quant-inst's documented Metis repair can prove a different
            valid instance regardless of its argument. Use a mismatched
            FREE parameter, not just another valid bound substitution. *)
         require (label ^ " merged quant-inst target/argument graph names")
           (declines (fn () => produce (request "quant_inst"
             (disj (neg universal) (app (app predicate other) other))
             [] [other])));
         require (label ^ " merged quant-inst bound and free argument IDs")
           (declines (fn () => produce (request "quant_inst"
             (disj (neg universal) (app (app predicate rigid) other))
             [] [rigid]))))
      val _ = List.app check
        [("compatibility",compatibility []),("recorded",recorded [])]
      (* Only the actual visible SolverFlexible declaration may authorize
         state_define. An unused same-native declaration must not replace it
         in either list order; a listed rigid node is still rigid. *)
      fun introduction node = request "intro_def" (eq node zero) [] []
      fun rejects_definition message variables node =
        require message (declines (fn () =>
          recorded variables (introduction node)))
      val _ = rejects_definition
        "rigid intro-def borrowed same-native flexible authority"
        [flexible,unused] rigid
      val _ = rejects_definition "listing rigid vars granted authority"
        [rigid] rigid
      val _ = rejects_definition "listing generated vars granted authority"
        [other] other
      val _ = rejects_definition "unlisted flexible target gained authority"
        [unused] flexible
      fun defines variables node =
        let val request = introduction node
            val target = #target request
        in case recorded variables request of
          NONE => raise Fail "actual flexible intro-def was refused"
        | SOME {definitions,theorem} =>
            (require "intro-def recorded another declaration's graph ID"
               (definitions = [target]);
             require "intro-def lost its actual flexible endpoint"
               (case R.operands graph boolSyntax.equality 2
                   (hd definitions) of
                  SOME [left,right] => left=node andalso right=zero
                | _ => false);
             exact (G.representative graph
               (R.implication graph scope [target] target)) [] theorem)
        end
      val _ = defines [flexible] flexible
      val _ = List.app (fn variables =>
        (defines variables flexible;defines variables unused))
        [[flexible,unused],[unused,flexible]]
      val _ = G.close_scope graph instance_scope
      val _ = G.close_scope graph binder_scope
      val _ = G.close_scope graph scope
    in () end)

  fun run () =
    (operators ();negatives ();classification ();
     annotation_allowance ();annotation_frontier ();
     identities ();
     binder_identities ();
     cpc_cases ();cpc_packet_boundaries ();cpc_annotations ();
     structured_cases ();parsed_clause ();
     (* The fixed selected Z3 worker is exercised by its parsed fixture. *)
     z3_cases ();z3_false_target ();z3_rigidity ();
     z3_generic_identities ())
end
