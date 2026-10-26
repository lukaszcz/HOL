(* Focused Z3 parser regressions. Complements selftest groups 386 and 433.
   No parser packet is treated as an inference certificate. Only SMALL
   semantic projections below are reconstructed, then kernel-compared. *)
val _ = load "Z3_GraphValueProofParser"
structure Z3_GraphParserTests =
struct
  open HolKernel Parse boolLib bossLib
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure V = SmtLib_GraphSourcePortfolio
  structure GP = SmtLib_GraphPreprocess
  structure T = SmtLib_GraphTranslation
  structure F = SmtLib_GraphFrontend
  structure PV = SmtLib_GraphParserValue
  structure MD = SmtLib_GraphDeclarationMetadata
  structure RP = SmtReplayResourcePolicy
  structure Z = Z3_GraphProofParser
  structure ZV = Z3_GraphValueProofParser
  structure VP = SmtLib_GraphValueProof
  structure Packet = SmtLib_GraphProof
  val cap = RP.AtMost 1000000000
  val maximum = 512
  val compound = ``task34_p /\ task34_q``
  val source_terms = [("task34_compound",compound)]
  val version = "4.15.3"
  type env = {graph:G.graph,scope:G.scope,sources:S.sources,
    work:W.portfolio,query:GP.graph_query,metadata:MD.metadata}
  datatype route = Finite | Policy | Value
  val routes = [Finite,Policy,Value]
  fun route_name Finite = "finite"
    | route_name Policy = "policy"
    | route_name Value = "Value"
  fun require message yes = if yes then () else raise Fail message
  val failures = ref ([]:string list)
  fun test label action =
    (testutils.tprint ("Task34 " ^ label);
     ((action ();testutils.OK ()) handle primary =>
       (failures := label :: !failures;
        print ("FAILED: " ^ General.exnMessage primary ^ "\n"))))
  fun finally action close =
    let val outcome = Exn.capture action ()
        val cleanup = Exn.capture close ()
    in case outcome of Exn.Exn primary => raise primary
      | Exn.Res value => (Exn.release cleanup;value) end
  fun input text =
    let val next = ref 0 in fn () =>
      if !next = String.size text then NONE else
        let val char = String.sub (text,!next)
        in next := !next+1;SOME char end end
  fun wrap body = "((proof " ^ body ^ "))"
  fun owned action =
    let
      val graph = G.new () val scope = G.root_scope graph
      val sources = S.new graph scope 10000
        {assumptions=[compound],goal=compound}
      val work = W.begin_with_policy graph scope sources
        {limits={input_limit=cap,output_limit=cap,template_limit=cap},
         work_limit=cap}
      fun run () =
        let
          val {assumptions,denied} = V.originals_with_policy work
          val validation = V.validate_portfolio_with_policy work
            {assumptions=assumptions,goal= #node (S.goal_source sources),
             denied=denied}
          val query = GP.prepare_query_with_policy work
            (GP.from_portfolio_with_policy work validation)
          fun open_view caller node = ignore
            (G.record_opened_view_with_policy graph caller
              (RP.AtMost 10000) node)
          val metadata = T.with_outbound_query_analysis_with_policy work
            query open_view (fn context =>
              SmtLib.outbound_with_backend_context
                {sequence_emission=false,set_backend=SmtLib.Z3Set,
                 bag_backend=SmtLib.Z3ArrayBag,
                 has_set_terms=false,has_bag_terms=false}
                (fn backend =>
                  let
                    val operations =
                      SmtLib_GraphCarrierOperations.make_with_datatypes
                        context {sequence_emission=false}
                        {term_to_string=fn _ =>
                          raise Fail "unexpected Task34 formatter"}
                    val emission = SmtLib_GraphDispatcher.emit context
                      {operations=operations,regime=SmtLib.FirstOrder,
                       apply_operator=SmtLib.ApplyUnderscore,
                       prefix="task34_emitted_",roots=[(0,#goal context)]}
                  in MD.freeze context
                    {graph=graph,scope=scope,regime=SmtLib.FirstOrder,
                     backend=backend,operations=operations,emission=emission}
                  end))
        in action ({graph=graph,scope=scope,sources=sources,
          work=work,query=query,metadata=metadata}:env) end
    in finally run (fn () => (W.close work;G.close_scope graph scope)) end
  fun finite_options (e:env) : F.options =
    {graph= #graph e,scope= #scope e,logic="ALL",sources=source_terms,
     sorts=Redblackmap.mkDict String.compare,binder_lists=[],
     import_limit=10000,literal_limit=10000,binder_limit=10000,
     recipe_limits={template_limit=10000,index_limit=10000,
       operand_limit=10000,token_limit=10000},
     special=fn _ => fn _ => NONE,
     ascribed=fn _ => fn _ => fn _ => NONE}
  (* These options are genuinely carrier-polymorphic, as in group386. *)
  fun policy_options (e:env) : 'a F.constructed_policy_options =
    {graph= #graph e,scope= #scope e,logic="ALL",sources=source_terms,
     sorts=Redblackmap.mkDict String.compare,binder_lists=[],
     import_limit=cap,literal_limit=cap,binder_limit=cap,
     recipe_limits={template_limit=cap,index_limit=cap,
       operand_limit=cap,token_limit=cap},
     special=fn _ => fn _ => NONE,
     ascribed=fn _ => fn _ => fn _ => NONE}
  fun native_packet route (e:env) text = case route of
      Finite =>
        let val stream = TextIO.openString text
        in finally (fn () => Z.create_packet (finite_options e)
          version stream) (fn () => TextIO.closeIn stream) end
    | Policy => Z.create_packet_with_policy_from_input
        (policy_options e) version (input text)
    | Value => raise Fail "Value is not a native packet"
  fun value_packet (e:env) text =
    ZV.create_packet_with_policy_from_input (#work e) (#query e)
      (policy_options e) (#metadata e) version (input text)
  fun bounded term = require "Task34 raw projection exceeds bound512"
    (Option.isSome (SmtReplayImport.bounded_raw_size maximum term))
  fun native_raw (e:env) node =
    let val term = G.representative (#graph e) node
    in bounded term;term end
  (* proof_view also covers retained compound Source leaves. No opaque
     fallback, aconv-only success or unbounded Value expansion is allowed. *)
  fun value_raw context value =
    let
      val remaining = ref maximum
      fun walk environment node =
        let val _ = require "Task34 Value projection exceeds bound512"
              (!remaining>0)
            val _ = remaining := !remaining-1
            val key = PV.proof_key context node
        in case List.find (fn (saved,_) => saved=key) environment of
            SOME (_,term) => term
          | NONE => case PV.proof_view context node of
              PV.ProofVariable (_,atom) => atom
            | PV.ProofConstant atom => atom
            | PV.ProofApplication (f,x) =>
                Term.mk_comb (walk environment f,walk environment x)
            | PV.ProofAbstraction {binder,body,...} =>
                let val variable = Term.genvar
                      (PV.proof_type_of context binder)
                in Term.mk_abs (variable,walk
                  ((PV.proof_key context binder,variable)::environment)
                  body) end
            | PV.ProofOpaque => raise Fail "opaque Task34 projection"
        end
      val result = walk [] (PV.proof_term context value)
    in bounded result;result end
  fun normalize term = Conv.QCONV
    (DEPTH_CONV BETA_CONV THENC
     simpLib.SIMP_CONV pureSimps.pure_ss [boolTheory.LET_THM] THENC
     DEPTH_CONV BETA_CONV) term
  val bridges = ref 0
  fun bridge left right =
    let
      val _ = bounded left val _ = bounded right
      val lhs = normalize left val rhs = normalize right
      val _ = bounded (boolSyntax.rhs (Thm.concl lhs))
      val _ = bounded (boolSyntax.rhs (Thm.concl rhs))
      val middle = Thm.ALPHA (boolSyntax.rhs (Thm.concl lhs))
        (boolSyntax.rhs (Thm.concl rhs))
      val theorem = Thm.TRANS lhs (Thm.TRANS middle (Thm.SYM rhs))
      val _ = Library.check_oracle_tags "Z3_GraphParserTests"
        "bounded semantic bridge" theorem
      val _ = require "bridge changed endpoints, Hyp or axiom tags"
        (null (Thm.hyp theorem) andalso
         null (Tag.axioms_of (Thm.tag theorem)) andalso
         Term.aconv (Thm.concl theorem) (boolSyntax.mk_eq (left,right)))
    in bridges := !bridges+1 end
  datatype observation = Rule of string * Term.term * observation list
    | Indexed of Term.term list * Term.term
    | Lemma of Z3_Proof.th_lemma_metadata * Term.term * observation list
    | Bind of Type.hol_type list * observation
  fun close variables body = List.foldr Term.mk_abs body variables
  fun rule name term premises = Rule (name,term,premises)
  fun asserted term = rule "asserted" term []
  fun compare (Rule (name,left,ls),Rule (other,right,rs)) =
        (require "proof rule name/arity changed"
           (name=other andalso length ls=length rs);
         bridge left right;ListPair.appEq compare (ls,rs))
    | compare (Indexed (args,left),Indexed (other,right)) =
        (require "indexed argument count changed" (length args=length other);
         ListPair.appEq (fn (a,b) => bridge a b) (args,other);
         bridge left right)
    | compare (Lemma (metadata,left,ls),Lemma (other,right,rs)) =
        (require "theory label metadata/arity changed"
           (metadata=other andalso length ls=length rs);
         bridge left right;ListPair.appEq compare (ls,rs))
    | compare (Bind (types,left),Bind (other,right)) =
        (require "proof-bind variable types changed"
           (ListPair.allEq (fn (a,b) => Type.compare (a,b)=EQUAL)
             (types,other));compare (left,right))
    | compare _ = raise Fail "proof rule/bind structure changed"
  fun legacy text =
    let
      val (types,terms) = SmtLib_Logics.parsedicts_of_logic "ALL"
      val terms = List.foldl (fn ((token,term),dict) =>
        Library.extend_dict
          ((token,SmtLib_Theories.K_zero_zero term),dict)) terms source_terms
      val stream = TextIO.openString text
    in finally (fn () => Z3_ProofParser.parse_stream_with_version
      (types,terms) version stream) (fn () => TextIO.closeIn stream) end
  fun legacy_observation proof =
    let
      val remaining = ref 128
      fun walk variables pt =
        let val _ = require "Task34 legacy proof exceeds128" (!remaining>0)
            val _ = remaining := !remaining-1
            fun result name term pts = Rule
              (name,close variables term,List.map (walk variables) pts)
        in case pt of
            Z3_Proof.ID id => walk variables
              (Redblackmap.find (Z3_Proof.proof_steps proof,id))
          | Z3_Proof.PROOF_BIND (bound,body) =>
              Bind (List.map Term.type_of bound,
                walk (variables @ bound) body)
          | Z3_Proof.QUANT_INST (args,term) =>
              Indexed (List.map (close variables) args,close variables term)
          | Z3_Proof.TH_LEMMA_ARITH (metadata,pts,term) =>
              Lemma (metadata,close variables term,
                List.map (walk variables) pts)
          | Z3_Proof.ASSERTED term => result "asserted" term []
          | Z3_Proof.REFL term => result "refl" term []
          | Z3_Proof.REWRITE term => result "rewrite" term []
          | Z3_Proof.MP (a,b,term) => result "mp" term [a,b]
          | Z3_Proof.NNF_POS (pts,term) => result "nnf-pos" term pts
          | Z3_Proof.QUANT_INTRO (pt,term) => result "quant-intro" term [pt]
          | Z3_Proof.UNIT_RESOLUTION (pts,term) =>
              result "unit-resolution" term pts
          | _ => raise Fail "unexpected Task34 legacy constructor"
        end
    in walk [] (Redblackmap.find (Z3_Proof.proof_steps proof,0)) end
  fun graph_observation raw (proof:'a Z.constructed_proof) =
    let
      val remaining = ref 128
      fun walk variables id =
        let val _ = require "Task34 graph proof exceeds128" (!remaining>0)
            val _ = remaining := !remaining-1
        in case Redblackmap.find (#steps proof,id) of
            Z.Alias next => walk variables next
          | Z.Bind {binding=F.ScopedSession {variables=bound,...},body,...} =>
              let val bound = List.map raw bound
                  val types = List.map Term.type_of bound
                  (* Native eager let reduction joins these lambda blocks.
                     Retain graph inventories/IDs; canonicalize only this
                     bounded semantic observation, closing over ALL blocks. *)
                  val observed = walk (variables @ bound) body
              in case observed of Bind (inner,pt) => Bind (types @ inner,pt)
                | _ => Bind (types,observed) end
          | Z.Rule {rule,conclusion,premises,arguments,metadata,...} =>
              if #name rule="quant-inst" then
                (require "quant-inst has premises" (null premises);
                 Indexed (List.map (fn argument =>
                   close variables (raw (#node argument))) arguments,
                   close variables (raw (#node conclusion))))
              else
                let val _ = require "unexpected indexed arguments"
                      (null arguments)
                    val term = close variables (raw (#node conclusion))
                    val pts = List.map (walk variables) premises
                in case metadata of SOME labels =>
                    (require "theory label changed rule"
                       (#name rule="th-lemma-arith");
                     Lemma (labels,term,pts))
                  | NONE => Rule (#name rule,term,pts) end
        end
    in walk [] (#root proof) end
  fun expired (e:env) saved = List.app (fn (scope,observe) =>
    let val closed = (G.validate_scope (#graph e) scope;false)
          handle Feedback.HOL_ERR _ => true
        val stale = (observe ();false) handle Feedback.HOL_ERR _ => true
    in require "proof scope or session survived packet.close" (closed andalso
      stale) end) saved
  fun bindings (proof:'a Z.constructed_proof) =
    Redblackmap.foldl (fn (_,step,rest) => case step of
      Z.Bind {binding=F.ScopedSession {session,scope,...},...} =>
        (scope,fn () => ignore ((#sort_dictionary session) ()))::rest
      | _ => rest) [] (#steps proof)
  (* Check exact real IDs before projection. NONE selects every variable;
     SOME positions permits intentionally shadowed or unused binders.
     Positions are zero-based in each Bind's flattened inventory. This
     selects only this inventory's body free IDs: nested Bind conclusions
     can also mention outer variables. graph_observation/compare still
     checks ALL binder types/counts and closes unused outer variables too. *)
  fun check_bound_usage selected free (proof:''a Z.constructed_proof) =
    let
      fun conclusion id = case Redblackmap.find (#steps proof,id) of
          Z.Rule {conclusion,...} => #node conclusion
        | Z.Alias next => conclusion next
        | Z.Bind {body,...} => conclusion body
      fun check (_,Z.Bind {binding=F.ScopedSession {variables,...},
            body,...},()) =
            let
              val actual = List.filter (fn v =>
                List.exists (fn bound => bound=v) variables)
                (free (conclusion body))
              val expected = case selected of NONE => variables
                | SOME positions => List.map
                    (fn i => List.nth (variables,i)) positions
              fun distinct [] = true
                | distinct (v::vs) = not (List.exists (fn a => a=v) vs)
                    andalso distinct vs
              val _ = require "Bind reused a Bound identity"
                (distinct variables)
            in require "Bind body changed the exact selected Bound free IDs"
              (length actual=length expected andalso
               List.all (fn v => List.exists (fn a => a=v) actual) expected)
            end
        | check (_,_,()) = ()
    in Redblackmap.foldl check () (#steps proof) end
  fun with_native_using selected route text action = owned (fn e =>
    let val held = native_packet route e text
        val proof = Packet.proof held
        val saved = bindings proof
        val result = finally (fn () =>
          (check_bound_usage selected (fn node => case
               G.free_variable_nodes (#graph e) node of SOME vars => vars
             | NONE => raise Fail "unknown native binder dependencies") proof;
           action e proof)) (fn () => Packet.close held)
        val _ = expired e saved
    in result end)
  fun with_value_using selected text action = owned (fn e =>
    let val held = value_packet e text
        val saved = ref []
        val result = finally (fn () => W.with_step (#work e) (fn () =>
          let val current = VP.contents_with_policy_for
                (#work e) (#query e) held
              val _ = saved := bindings (#proof current)
              val _ = check_bound_usage selected
                (PV.free_variables (#context current)) (#proof current)
          in action e (#context current) (#proof current) end))
          (fn () => VP.close held)
        (* Context callbacks require a live action, so test their guard in
           the same Work. This is deliberately last: failure retires Work. *)
        val closed = List.all (fn (scope,_) =>
          (G.validate_scope (#graph e) scope;false)
            handle Feedback.HOL_ERR _ => true) (!saved)
        val stale = case !saved of [] => true | (_,observe)::_ =>
          ((W.with_step (#work e) observe;false)
            handle Feedback.HOL_ERR _ => true)
    in require "Value scope/session survived close" (closed andalso stale);
       result end)
  fun with_native route = with_native_using NONE route
  fun with_value text = with_value_using NONE text
  fun compare_routes selected label text expected old =
    let
      fun checked observed =
        (compare (expected,observed);
         case old of NONE => () | SOME previous => compare (previous,observed))
      fun run route = test (label ^ " / " ^ route_name route) (fn () =>
        case route of Value => with_value_using selected text
            (fn _ => fn context => fn proof =>
              checked (graph_observation (value_raw context) proof))
        | _ => with_native_using selected route text
            (fn e => fn proof =>
              checked (graph_observation (native_raw e) proof)))
    in List.app run routes end
  fun positive_using selected label body expected =
    let
      val text = wrap body
      val old = Exn.capture (fn () => legacy_observation (legacy text)) ()
      (* A legacy failure is recorded, never counted as old-parser success.
         Graph checks still run against the independent expected terms. *)
      val _ = test (label ^ " / legacy vs expected")
        (fn () => compare (Exn.release old,expected))
      val previous = case old of Exn.Res value => SOME value
        | Exn.Exn _ => NONE
    in compare_routes selected label text expected previous end
  fun positive label = positive_using NONE label
  (* reduce_z3_lets cannot beta-reduce the ordinary parser's multi-binding
     LET encoding. These graph-only fixtures make no legacy-success claim;
     every route must kernel-bridge to the independent HOL terms below. *)
  fun simultaneous label body expected =
    compare_routes NONE
      (label ^ " / legacy unsupported: simultaneous LET")
      (wrap body) expected NONE
  fun negative_matching accepts label body = List.app (fn route =>
    test (label ^ " / " ^ route_name route) (fn () => owned (fn e =>
      let
        val diagnostic = (case route of
            Value => (VP.close (value_packet e (wrap body));NONE)
          | _ => (Packet.close (native_packet route e (wrap body));NONE))
          handle Feedback.HOL_ERR detail => SOME (Feedback.message_of detail)
        val _ = G.validate_scope (#graph e) (#scope e)
      in case diagnostic of
          NONE => raise Fail "malformed lexical input published a proof packet"
        | SOME message => require ("wrong first error: " ^ message)
            (accepts message)
      end))) routes
  fun negative label = negative_matching (fn _ => true) label
  fun first_error label body required forbidden =
    negative_matching (fn message =>
      List.all (fn text => String.isSubstring text message) required andalso
      List.all (fn text => not (String.isSubstring text message)) forbidden)
      label body
  (* Identity/occurrence checks from group433 supplement semantic bridges.
     Closing variables before ALPHA must not mask reused Bound identities. *)
  fun alias_rule (proof:'a Z.constructed_proof) id =
    case Redblackmap.find (#steps proof,id) of Z.Rule info => info
      | Z.Alias next => alias_rule proof next
      | _ => raise Fail "alias control expected Rule"
  fun alias_bind (proof:'a Z.constructed_proof) id =
    case Redblackmap.find (#steps proof,id) of
      Z.Bind {binding,body,lambda_blocks=[1]} => (binding,body)
    | Z.Alias next => alias_bind proof next
    | _ => raise Fail "alias control expected one-variable Bind"
  fun atom expected
      (SmtLib_Parser.ConstructionOccurrence {value,role,children,...}) =
    value=expected andalso null children andalso
    (case role of SmtLib_Parser.ConstructionAtom => true | _ => false)
  fun check_shadow mode bound (proof:''a Z.constructed_proof) =
    let
      val (binding,body) = alias_bind proof (#root proof)
      val F.ScopedSession {variables,...} = binding
      val variable = case variables of [v] => v
        | _ => raise Fail "shadow control lost variable"
      val _ = F.scoped_session_origin binding
      val _ = require "alias replaced Bound variable" (bound variable)
      fun exact (term:''a F.constructed_term) =
        #node term=variable andalso atom variable (#occurrence term)
      val info = alias_rule proof body
      val _ = require "shadow retained alias occurrence"
        (exact (#conclusion info))
    in if mode="nested" then
        let val (inner,outer) = case #premises info of [a,b] => (a,b)
              | _ => raise Fail "nested shadow lost premises"
            val (F.ScopedSession {variables=inner_vars,...},inside) =
              alias_bind proof inner
            val fresh = case inner_vars of [v] => v
              | _ => raise Fail "nested shadow lost inner variable"
            val term = #conclusion (alias_rule proof inside)
        in require "nested shadow reused Bound identity or lost outer"
          (fresh<>variable andalso bound fresh andalso #node term=fresh
           andalso atom fresh (#occurrence term)
           andalso exact (#conclusion (alias_rule proof outer))) end
      else if mode="retained" then
        let val (prior,later) = case #premises info of [a,b] => (a,b)
              | _ => raise Fail "retained shadow lost premises"
            val earlier = #conclusion (alias_rule proof prior)
            val after = #conclusion (alias_rule proof later)
            fun disjunction (term:''a F.constructed_term) = case
                #occurrence term of
                SmtLib_Parser.ConstructionOccurrence
                  {value,role=SmtLib_Parser.ConstructionApplication,
                   token="or",children=[left,right]} =>
                    value= #node term andalso List.all
                      (fn SmtLib_Parser.ConstructionOccurrence {role,...} =>
                        case role of SmtLib_Parser.ConstructionAtom => true
                          | _ => false) [left,right]
              | _ => false
        in require "nonshadowed OR/proof aliases lost syntax"
          (prior<>later andalso #node earlier= #node after andalso
           disjunction earlier andalso disjunction after) end
      else () end
  fun shadow label body mode = List.app (fn route =>
    test (label ^ " / " ^ route_name route) (fn () => case route of
      Value => with_value (wrap body) (fn _ => fn context => fn proof =>
        check_shadow mode (fn value => case PV.view context value of
          PV.Variable (G.Bound,_) => true | _ => false) proof)
    | _ => with_native route (wrap body) (fn e => fn proof =>
        check_shadow mode (fn node => case G.view (#graph e) node of
          G.Variable (G.Bound,_) => true | _ => false) proof))) routes
  (* Unlike parser-only positives, every inference here is valid. Replay
     the original packet, not an observation rebuilt as a synthetic proof.
     Value projection remains semantic-only; no projection is replayed. *)
  fun replay_positive label body goal =
    let
      val text = wrap body
      fun checked theorem =
        (Library.check_oracle_tags "Z3_GraphParserTests" label theorem;
         require "replay changed exact Goal/Hyp or axiom tags"
           (Term.aconv (Thm.concl theorem) goal andalso
            null (Thm.hyp theorem) andalso
            null (Tag.axioms_of (Thm.tag theorem))))
    in test (label ^ " / checked replay") (fn () =>
      let
        val old = Z3_ProofReplay.replay_root_for_test (legacy text)
        val _ = checked old
        fun replay route = with_native route text (fn e => fn proof =>
          let
            val theorem = Z3_GraphProofReplay.replay (#graph e) (#scope e)
              {proof=proof,template_limit=maximum,
               local_law=fn _ => raise Fail "refl needed a local fallback"}
            val _ = checked theorem
          in bridge (Thm.concl old) (Thm.concl theorem) end)
      in List.app replay [Finite,Policy] end) end
  fun run () =
    let
      val _ = bridges := 0
      val _ = failures := []
      val _ = replay_positive "valid refl with term let"
        "(let ((a (or true false))) (refl (= a a)))"
        ``(T \/ F) = (T \/ F)``
      val _ = replay_positive "valid local @x proof let and symm"
        "(symm (let ((@x1 (refl (= true true)))) @x1) (= true true))"
        ``T = T``
      val _ = replay_positive "valid quoted local @x term let"
        "(symm (let ((|@x7| true)) (refl (= @x7 @x7))) (= true true))"
        ``T = T``
      val tt = asserted boolSyntax.T val ff = asserted boolSyntax.F
      fun ur terms result = rule "unit-resolution" result terms
      val _ = positive "plain proof grammar" "(asserted true)" tt
      val _ = positive "term alias keeps OR semantics"
        "(let ((a (or true false))) (asserted a))"
        (asserted ``T \/ F``)
      val _ = positive "separate local @x proof IDs"
        "(unit-resolution (let ((@x1 (asserted true))) @x1)\
        \ (let ((@x1 (asserted false))) @x1) false)" (ur [tt,ff] boolSyntax.F)
      val _ = positive "quoted local @x proof IDs are lexical"
        "(unit-resolution (let ((|@x2| (asserted true))) |@x2|)\
        \ (let ((@x2 (asserted false))) @x2) false)" (ur [tt,ff] boolSyntax.F)
      val _ = positive "nested local @x proof IDs restore outer alias"
        "(unit-resolution (let ((@x1 (asserted true)))\
        \ (unit-resolution (let ((@x1 (asserted false))) @x1) @x1 true))\
        \ (asserted false) false)"
        (ur [ur [ff,tt] boolSyntax.T,ff] boolSyntax.F)
      val _ = List.app (fn name => positive "local @x term alias"
        ("(unit-resolution (let ((" ^ name ^ " true)) (asserted " ^
          name ^ ")) (asserted false) false)") (ur [tt,ff] boolSyntax.F))
        ["@x7","|@x7|"]
      val _ = simultaneous "simultaneous RHS sees incoming Bool before Int"
        "(let ((x true))\
        \ (asserted (let ((x 7) (copy x)) copy)))" tt
      val _ = simultaneous "simultaneous RHS sees incoming Int before Bool"
        "(let ((x 7))\
        \ (asserted (let ((x false) (copy x)) (= copy 7))))"
        (asserted ``(7:int) = 7``)
      val _ = simultaneous "local proof RHS sees incoming term before shadow"
        "(unit-resolution (let ((x true))\
        \ (let ((x (asserted false)) (copy (asserted x))) copy))\
        \ (asserted false) false)" (ur [tt,ff] boolSyntax.F)
      val _ = positive "compound Source leaf through alias and not"
        "(let ((a task34_compound)) (asserted (not a)))"
        (asserted (boolSyntax.mk_neg compound))
      val _ = simultaneous "compound Source leaf through simultaneous aliases"
        "(let ((x task34_compound))\
        \ (asserted (let ((x false) (copy x)) copy)))" (asserted compound)
      val _ = positive "compound proof alias survives quoted Source shadow"
        "(unit-resolution (let ((p (asserted (not task34_compound))))\
        \ (let ((|task34_compound| (asserted false))) p))\
        \ (asserted false) false)"
        (ur [asserted (boolSyntax.mk_neg compound),ff] boolSyntax.F)
      val _ = positive "compound term alias survives quoted Source shadow"
        "(let ((a task34_compound))\
        \ (unit-resolution (let ((|task34_compound| (asserted false)))\
        \ (asserted (not a))) (asserted false) false))"
        (ur [asserted (boolSyntax.mk_neg compound),ff] boolSyntax.F)
      val _ = positive "ordinary term let re-shadows a proof blocker"
        "(unit-resolution (let ((p (asserted false)))\
        \ (asserted (not (let ((|p| true)) p))))\
        \ (asserted false) false)"
        (ur [asserted ``~T``,ff] boolSyntax.F)
      val _ = positive "ordinary term binder re-shadows a proof blocker"
        "(unit-resolution (let ((|p| (asserted false)))\
        \ (asserted (not (forall ((p Bool)) p))))\
        \ (asserted false) false)"
        (ur [asserted ``~(!p:bool. p)``,ff] boolSyntax.F)
      val _ = positive "local proof not leaves builtin application available"
        "(unit-resolution (let ((not (asserted true)))\
        \ (asserted (not false))) (asserted false) false)"
        (ur [asserted ``~F``,ff] boolSyntax.F)
      val _ = positive "proof catch-all does not hide concrete true"
        "(unit-resolution (let ((_ (asserted false))) (asserted true))\
        \ (asserted false) false)" (ur [tt,ff] boolSyntax.F)
      val _ = positive "quoted proof catch-all does not hide concrete false"
        "(unit-resolution (let ((|_| (asserted true))) (asserted false))\
        \ (asserted true) false)" (ur [ff,tt] boolSyntax.F)
      val _ = positive "annotation labels sharing a proof name are metadata"
        "(unit-resolution (let ((p (asserted false)))\
        \ (asserted (! true :qid p :named p)))\
        \ (asserted false) false)" (ur [tt,ff] boolSyntax.F)
      val empty_seq = ``[]:int list``
      val _ = positive "ascribed sort names do not resolve proof aliases"
        "(unit-resolution (let ((Int (asserted false)))\
        \ (let ((Seq (asserted false)))\
        \ (asserted (= (as seq.empty (Seq Int))\
        \ (as seq.empty (Seq Int)))))) (asserted false) false)"
        (ur [asserted (boolSyntax.mk_eq (empty_seq,empty_seq)),ff]
          boolSyntax.F)
      (* Pinned verbatim term-lambda fixture from Unittest. Ordinary term
         lambdas must not become Bind nodes or open speculative scopes. *)
      val increment = ``\x:int. x + 1``
      val _ = positive "pinned verbatim term-lambda equality"
        "(let ((?x28 (lambda ((x Int))\
        \ (! (+ x 1) :qid k!4)))) (asserted (= ?x28 ?x28)))"
        (asserted (boolSyntax.mk_eq (increment,increment)))
      val nested_term = ``\outer:int. \x:bool. x``
      val _ = positive "nested term lambdas shadow a proof alias"
        "(unit-resolution (let ((x (asserted false)))\
        \ (asserted (= (lambda ((x Int)) (lambda ((|x| Bool)) x))\
        \ (lambda ((x Int)) (lambda ((x Bool)) x)))))\
        \ (asserted false) false)"
        (ur [asserted (boolSyntax.mk_eq (nested_term,nested_term)),ff]
          boolSyntax.F)
      (* Use actual term arguments for quant-inst, not proof-typed terms.
         The last index re-shadows an incoming proof alias within the index. *)
      val _ = simultaneous "atomic and compound term indices keep their types"
        "(unit-resolution (let ((p (asserted false)) (n 7))\
        \ ((_ quant-inst n true (+ 1 2) (let ((p 9)) p)) false))\
        \ (asserted false) false)"
        (ur [Indexed ([``7:int``,boolSyntax.T,``(1:int) + 2``,``9:int``],
          boolSyntax.F),ff] boolSyntax.F)
      val divides = intSyntax.mk_divides (``3:int``,``6:int``)
      val _ = positive "local proof catch-all leaves numeric divisible index"
        "(unit-resolution (let ((n 6))\
        \ (let ((_ (asserted true))) (asserted ((_ divisible 3) n))))\
        \ (asserted false) false)"
        (ur [asserted divides,ff] boolSyntax.F)
      val _ = positive "frontend atomic index resolves a local term alias"
        "(let ((n 3)) (asserted ((_ divisible n) 6)))"
        (asserted divides)
      val _ = positive "frontend compound index re-shadows a proof alias"
        "(unit-resolution (let ((p (asserted false)))\
        \ (asserted ((_ divisible (let ((|p| 3)) p)) 6)))\
        \ (asserted false) false)"
        (ur [asserted divides,ff] boolSyntax.F)
      (* th-lemma labels are not term arguments. The legacy parser captures
         the local binder's spelling before let substitution; compare that
         exact metadata too. This is parser classification, not replay. *)
      val _ = positive "proof alias in an atomic theory label is not a term"
        "(unit-resolution (let ((p (asserted true)))\
        \ ((_ th-lemma arith farkas p) false)) (asserted false) false)"
        (ur [Lemma ({theory="arith",subkind=SOME "farkas",indices=["p"]},
          boolSyntax.F,[]),ff] boolSyntax.F)
      (* Exact Unittest.z3_proof_parser_structures_proof_bind_success input.
         Expected closed bodies are independent of both parser outputs. *)
      val bound_body = ``\x:int. (x = x) = (x = x)``
      val expected = rule "mp" boolSyntax.F
        [rule "nnf-pos" boolSyntax.F
          [Bind ([``:int``],rule "refl" bound_body [])],
         rule "quant-intro" boolSyntax.F
          [Bind ([``:int``],rule "rewrite" bound_body [])]]
      val _ = positive "pinned aliased proof lambdas"
        "(let ((?x67 (lambda ((x Int))\
        \ (refl (~ (= x x) (= x x))))))\
        \ (let ((?x80 (lambda ((x Int))\
        \ (rewrite (= (= x x) (= x x))))))\
        \ (mp (nnf-pos (proof-bind ?x67) false)\
        \ (quant-intro (proof-bind ?x80) false) false)))" expected
      (* These deliberately invalid inferences test parser classification
         and bounded semantics only, never checked inference replay. *)
      val _ = positive_using (SOME [])
        "indexed theory lemma body classifies proof lambda"
        "(quant-intro (proof-bind (lambda ((x Int))\
        \ ((_ th-lemma arith) true))) false)"
        (rule "quant-intro" boolSyntax.F
          [Bind ([``:int``],
            Lemma ({theory="arith",subkind=NONE,indices=[]},
              ``\x:int. T``,[]))])
      val _ = positive "lambda let lambda composes proof bindings"
        "(quant-intro (proof-bind (lambda ((x Int))\
        \ (let ((a true)) (lambda ((y Int)) (asserted (= x y)))))) false)"
        (rule "quant-intro" boolSyntax.F
          [Bind ([``:int``,``:int``],asserted ``\x:int. \y:int. x = y``)])
      val _ = positive_using (SOME [1])
        "consecutive proof lambdas hide repeated Int name"
        "(quant-intro (proof-bind (lambda ((x Int))\
        \ (lambda ((|x| Int)) (asserted (= x x))))) false)"
        (rule "quant-intro" boolSyntax.F
          [Bind ([``:int``,``:int``],asserted ``\outer:int. \x:int. x = x``)])
      val _ = positive_using (SOME [1])
        "consecutive proof lambdas hide Int behind Bool"
        "(quant-intro (proof-bind (lambda ((|x| Int))\
        \ (lambda ((x Bool)) (asserted x)))) false)"
        (rule "quant-intro" boolSyntax.F
          [Bind ([``:int``,``:bool``],asserted nested_term)])
      val _ = positive_using (SOME [2])
        "three consecutive proof lambdas restore only innermost name"
        "(quant-intro (proof-bind (lambda ((x Int)) (lambda ((x Bool))\
        \ (lambda ((|x| Int)) (asserted (= x x)))))) false)"
        (rule "quant-intro" boolSyntax.F
          [Bind ([``:int``,``:bool``,``:int``],
            asserted ``\outer:int. \middle:bool. \x:int. x = x``)])
      val names = [("x","x","x"),("|x|","x","|x|"),
        ("x","|x|","x"),("|alias name|","|alias name|","|alias name|")]
      fun binder_shadow rhs (alias,binder,reference) = shadow
        "binder shadows term/proof aliases incl quotes"
        ("(let ((" ^ alias ^ " " ^ rhs ^ "))\
         \ (proof-bind (lambda ((" ^ binder ^ " Bool))\
         \ (asserted " ^ reference ^ "))))") "atom"
      val _ = List.app (fn rhs => List.app (binder_shadow rhs) names)
        ["(or true false)","(asserted true)"]
      val _ = List.app (fn rhs => shadow
        "simultaneous LET sees incoming binder"
        ("(let ((x " ^ rhs ^ ")) (proof-bind (lambda ((x Bool))\
         \ (let ((x false) (copy x)) (asserted copy)))))") "simultaneous")
        ["(or true false)","(asserted true)"]
      val _ = shadow "nested binders keep fresh IDs"
        "(let ((x (or true false))) (proof-bind (lambda ((x Bool))\
        \ (unit-resolution\
        \ (proof-bind (lambda ((x Bool)) (asserted x)))\
        \ (asserted x) x))))" "nested"
      val _ = shadow "nonshadowed aliases preserve OR occurrences"
        "(let ((a (or true false))) (let ((p (asserted a)))\
        \ (proof-bind (lambda ((x Bool))\
        \ (unit-resolution p (asserted a) x)))))" "retained"
      (* Put shadowing inside a premise: outer-let uniqueness must NOT be
         the reason for rejecting a proof alias used inside a term. *)
      val _ = List.app (fn (outer,inner,reference) => negative
        "proof shadow inside not is not the previous term"
        ("(unit-resolution (let ((" ^ outer ^ " true))\
         \ (let ((" ^ inner ^ " (asserted false)))\
         \ (asserted (not " ^ reference ^ "))))\
         \ (asserted true) false)")) names
      val _ = negative "local proof not is still not an atomic term"
        "(unit-resolution (let ((not (asserted true))) (asserted not))\
        \ (asserted false) false)"
      val bad_name = "string literal used as a let binding name"
      val _ = first_error "earlier unknown RHS precedes later bad let name"
        "(unit-resolution (let ((a missing) (\"bad\" true))\
        \ (asserted true)) (asserted false) false)"
        ["missing"] ["string literal"]
      val _ = first_error "bad let name precedes its unknown RHS"
        "(unit-resolution (let ((\"bad\" missing) (a true))\
        \ (asserted true)) (asserted false) false)"
        [bad_name] ["missing"]
      val _ = List.app (fn rhs => negative "string let names reject"
        ("(unit-resolution (let ((\"bad\" " ^ rhs ^ "))\
         \ (asserted true)) (asserted false) false)"))
        ["true","(asserted true)"]
      val _ = negative "duplicate simultaneous names reject incl quotes"
        "(unit-resolution (let ((x true) (|x| false)) (asserted x))\
        \ (asserted false) false)"
      val _ = negative "same proof-lambda block duplicates decoded names"
        "(proof-bind (lambda ((x Int) (|x| Bool)) (asserted true)))"
      val _ = negative "outer named proof is still not a term definition"
        "(let ((@x1 true)) (asserted @x1))"
      val _ = require "positive suite constructed no checked bridges"
        (!bridges>=60)
      val _ = print ("TASK34_KERNEL_BRIDGES " ^
        Int.toString (!bridges) ^ "\n")
      val _ = require ("Task34 failures: " ^
        String.concatWith ", " (List.rev (!failures))) (null (!failures))
    in () end
end
