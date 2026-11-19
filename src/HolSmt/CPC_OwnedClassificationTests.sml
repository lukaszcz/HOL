(* Work and refusals of the owned Value receiver's rule classification.

   The receiver classifies every step (pop, resolution, CNF, alignment,
   simple Boolean/equality, truth family, bounded) while it plans and
   while it replays, paying through its packet/contract guard. One case
   per route class runs through both paths on a live packet, a stale
   packet and a tight-budget packet. The checks are relations inside one
   run: exact vs one-short budgets, a stale packet vs a live one. No
   charge is pinned (they depend on the heap); the before/after
   identity of charges and outcomes is shown out of tree through
   [observe], which prints full lines. *)
structure CPC_OwnedClassificationTests =
struct
  open HolKernel boolLib
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure V = SmtLib_GraphSourcePortfolio
  structure GP = SmtLib_GraphPreprocess
  structure T = SmtLib_GraphTranslation
  structure MD = SmtLib_GraphDeclarationMetadata
  structure F = SmtLib_GraphFrontend
  structure PV = SmtLib_GraphParserValue
  structure VP = SmtLib_GraphValueProof
  structure C = CPC_ProofParser
  structure CV = CPC_GraphValueProofParser
  structure NC = SmtReplayNativeContract
  structure RP = SmtReplayResourcePolicy
  structure Receiver = CPC_OwnedValueNamedReplay

  fun require message yes = if yes then () else raise Fail message

  val cap = RP.AtMost 1000000000
  val native:NC.limits =
    {semantic_limits={input_limit=1000000,output_limit=1000000,
       template_limit=1000000},import_limit=1000000,
     type_work_limit=100000000}

  val p = mk_var("cpc_cls_p",bool)
  val q = mk_var("cpc_cls_q",bool)
  val r = mk_var("cpc_cls_r",bool)
  val f = mk_var("cpc_cls_f",bool --> bool)
  val bindings = [("p",p),("q",q),("r",r),("f",f)]
  val goal = mk_conj(mk_var("cpc_cls_goal",bool),mk_var("cpc_cls_goal",bool))
  val neg = mk_neg val disj = mk_disj val imp = mk_imp
  val eq = mk_eq val app = mk_comb

  type env = {graph:G.graph,scope:G.scope,sources:S.sources,
    work:W.portfolio,query:GP.graph_query,
    metadata:MD.metadata,contract:NC.contract}

  (* [budget] bounds the whole portfolio, setup included. *)
  fun fixture budget assumptions action =
    let
      val limit = case budget of NONE => cap | SOME n => RP.AtMost n
      val graph = G.new () val scope = G.root_scope graph
      val sources = S.new graph scope 10000
        {assumptions=assumptions,goal=goal}
      val work = W.begin_with_policy graph scope sources
        {limits={input_limit=cap,output_limit=cap,template_limit=cap},
         work_limit=limit}
      fun run () =
        let
          val contract = NC.capture work native
          val {assumptions,denied} = V.originals_with_policy work
          val validation = V.validate_portfolio_with_policy work
            {assumptions=assumptions,
             goal= #node (S.goal_source sources),denied=denied}
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
               has_set_terms=false,has_bag_terms=false} (fn backend =>
              let
                val operations =
                  SmtLib_GraphCarrierOperations.make_with_datatypes context
                    {sequence_emission=false}
                    {term_to_string=fn _ => raise Fail "unexpected formatter"}
                val emission = SmtLib_GraphDispatcher.emit context
                  {operations=operations,regime=SmtLib.FirstOrder,
                   apply_operator=SmtLib.ApplyUnderscore,prefix="cpc_cls_",
                   roots=ListPair.zip
                     (List.tabulate (length (#assumptions context)+2,Lib.I),
                      #goal context :: #assumptions context @
                        [#denied context])}
              in MD.freeze context
                {graph=graph,scope=scope,regime=SmtLib.FirstOrder,
                 backend=backend,operations=operations,emission=emission}
              end))
        in action ({graph=graph,scope=scope,sources=sources,work=work,
          query=query,metadata=metadata,contract=contract}:env) end
      val outcome = Exn.capture run ()
      val cleanup = Exn.capture (fn () =>
        (W.close work;G.close_scope graph scope)) ()
    in case outcome of Exn.Exn primary => raise primary
      | Exn.Res result => (Exn.release cleanup;result) end

  fun options (e:env):F.value_options =
    {graph= #graph e,scope= #scope e,logic="ALL",sources=bindings,
     sorts=Redblackmap.mkDict String.compare,binder_lists=[],
     import_limit=cap,literal_limit=cap,binder_limit=RP.AtMost 1,
     recipe_limits={template_limit=cap,index_limit=cap,
       operand_limit=cap,token_limit=cap},
     special=fn _ => fn _ => NONE,ascribed=fn _ => fn _ => fn _ => NONE}
  fun input text =
    let val index = ref 0 in fn () =>
      if !index = String.size text then NONE else
        let val result = String.sub (text,!index)
        in index := !index+1;SOME result end end
  fun packet (e:env) text =
    CV.create_packet_with_policy_from_input (#work e) (#query e)
      (options e) (#metadata e) "1.3.4" (input text)

  (* The query's assertions: the packet's own ASSUME value where it has
     one, else a copy of the query node (e.g. the denied goal). *)
  fun assertions (e:env) (data:CV.proof VP.contents) =
    let
      val current = GP.query_nodes_with_policy_for (#work e) (#query e)
      val asserted = List.mapPartial (fn C.GraphAssume (_,term) =>
          SOME (#node term) | _ => NONE) (#commands (#proof data))
      val context = #context data
      fun copy node =
        case G.view (#graph e) node of
          G.Variable _ => PV.graph_leaf context (#scope e) node
        | G.Constant _ => PV.graph_leaf context (#scope e) node
        | G.Application (left,right) =>
            PV.application context (#scope e) (copy left,copy right)
        | _ => raise Fail "fixture Source needs a binder programme"
      fun actual node =
        case List.find (fn value =>
            case PV.corresponds_to_graph_with_policy context
                (#graph e) (#scope e) {value=value,node=node} of
              PV.Corresponding => true | _ => false) asserted of
          SOME value => value
        | NONE => copy node
    in W.with_step (#work e) (fn () =>
      List.map actual (#assumptions current @ [#denied current])) end

  datatype path = Plan | Replay
  type observation =
    {before:IntInf.int,charged:IntInf.int,outcome:string,steps:int,
     trace:string list}

  (* One path of one case. [before] is the Work charged ahead of the
     path (packet, setup and, for Replay, planning); [charged] is what
     the path itself charged. [trace] lists the type-check callbacks
     and each completed step's theorem, in order. With [stale] the
     packet is closed right ahead of the path. A [budget] bounds the
     whole portfolio. *)
  fun observe {assumptions,text} path budget stale : observation =
    let
      val total = ref 0 : IntInf.int ref
      val mark = ref 0 : IntInf.int ref
      val outcome = ref "refused: before the path" and steps = ref 0
      val trace = ref ([]:string list)
      fun run (e:env) =
        let
          fun charged () = #charged (W.audit_policy (#work e))
          val _ = total := charged ()
          val held = packet e text
          val data = W.with_step (#work e) (fn () =>
            VP.contents_with_policy_for (#work e) (#query e) held)
          val values = assertions e data
          fun plan () = Receiver.prepare_with_policy (#work e) (#query e)
            held {assertions=values,native_contract= #contract e,
                  check_type=fn ty =>
                    trace := ("type " ^ type_to_string ty) :: !trace}
          fun refused detail = "refused: " ^ Feedback.message_of detail
          fun replay invocation =
            let
              val _ = mark := charged ()
              fun next ids =
                case Receiver.replay_next_with_policy (#work e) invocation of
                  NONE => List.rev ids
                | SOME {id,...} => (steps := !steps+1;next (id::ids))
              fun receipt id =
                let val {block,edge,...} =
                      Receiver.step_with_policy_for (#work e) invocation id
                    val theorem = W.with_step (#work e) (fn () =>
                      SmtReplayOwnedValueProof.compact_theorem_for
                        (#work e) block edge)
                in trace := ("step " ^ id ^ " " ^
                     term_to_string (concl theorem) ^ " / " ^
                     Int.toString (length (hyp theorem))) :: !trace end
            in
              (if stale then VP.close held else ();
               List.app receipt (next []);outcome := "replayed")
              handle Feedback.HOL_ERR detail => outcome := refused detail
            end
          val _ = if stale andalso path = Plan then VP.close held else ()
          val _ = mark := charged ()
          val prepared = Exn.capture plan ()
          val invocation = case prepared of
              Exn.Res (Receiver.Prepared invocation) =>
                (if path = Plan then outcome := "prepared" else ();
                 SOME invocation)
            | Exn.Res (Receiver.Needs rows) =>
                (outcome := "needs " ^ Int.toString (length rows);NONE)
            | Exn.Exn (Feedback.HOL_ERR detail) =>
                (outcome := refused detail;NONE)
            | Exn.Exn other => raise other
          val _ = if path = Plan then total := charged () else
            (case invocation of
               SOME invocation => (replay invocation;total := charged ())
             | NONE => total := charged ())
          val _ = case invocation of
              SOME invocation => (Receiver.close invocation
                handle Feedback.HOL_ERR _ => ())
            | NONE => (VP.close held handle Feedback.HOL_ERR _ => ())
        in () end
      val setup = Exn.capture (fn () => fixture budget assumptions run) ()
      val _ = case setup of Exn.Exn (Feedback.HOL_ERR detail) =>
          outcome := "refused: " ^ Feedback.message_of detail
        | Exn.Exn other => raise other
        | Exn.Res () => ()
    in {before= !mark,charged= !total - !mark,outcome= !outcome,
        steps= !steps,trace=List.rev (!trace)} end

  (* One case per route class. [expected] is the outcome of live
     planning: Boolean/equality/truth/CNF/resolution/alignment steps
     with a recorded conclusion are prepared; pop and bounded steps
     are returned as requirements (a pop also needs its Scope). *)
  type case_ = {label:string,expected:string,assumptions:term list,
    text:string}
  val cases:case_ list = [
    {label="resolution",expected="prepared",
     assumptions=[disj(p,q),neg p,neg q],
     text="((assume @clause (or p q)) (assume @np (not p)) "^
       "(assume @nq (not q)) (step @q q :rule resolution "^
       ":premises (@clause @np)) "^
       "(step @done false :rule resolution :premises (@q @nq)))"},
    {label="cnf",expected="prepared",
     assumptions=[neg(disj(p,imp(p,q)))],
     text="((assume @negative (not (or p (=> p q)))) "^
       "(step @clause (or p (=> p q)) "^
       ":rule cnf_implies_neg1 :args ((=> p q))) "^
       "(step @done false :rule contra :premises (@clause @negative)))"},
    {label="factoring",expected="prepared",
     assumptions=[disj(p,disj(p,q)),neg p,neg q],
     text="((assume @clause (or p p q)) (assume @np (not p)) "^
       "(assume @nq (not q)) (step @factored (or p q) :rule factoring "^
       ":premises (@clause)) (step @q q :rule resolution "^
       ":premises (@factored @np)) "^
       "(step @done false :rule resolution :premises (@q @nq)))"},
    {label="simple boolean",expected="prepared",
     assumptions=[neg(disj(neg boolSyntax.F,p))],
     text="((assume @input (not (or (not false) p))) "^
       "(step @picked (not (not false)) :rule not_or_elim "^
       ":premises (@input) :args (0)) "^
       "(step @done false :rule not_not_elim :premises (@picked)))"},
    {label="simple equality",expected="prepared",
     assumptions=[eq(app(f,p),app(f,q)),app(f,p),neg(app(f,q))],
     text="((assume @equation (= (f p) (f q))) "^
       "(assume @source (f p)) (assume @negative (not (f q))) "^
       "(step @q (f q) :rule eq_resolve :premises (@source @equation)) "^
       "(step @done false :rule contra :premises (@q @negative)))"},
    {label="truth family",expected="prepared",
     assumptions=[eq(p,boolSyntax.T),neg p],
     text="((assume @equal (= p true)) (assume @negative (not p)) "^
       "(step @p p :rule true_elim :premises (@equal)) "^
       "(step @done false :rule contra :premises (@p @negative)))"},
    {label="bounded",expected="needs 1",
     assumptions=[p,imp(p,q),neg q],
     text="((assume @p p) (assume @imp (=> p q)) (assume @negative "^
       "(not q)) (step @q q :rule modus_ponens :premises (@p @imp)) "^
       "(step @done false :rule contra :premises (@q @negative)))"},
    {label="pop",expected="needs 2",
     assumptions=[neg p],
     text="((step @clause (or p (=> p q)) "^
       ":rule cnf_implies_neg1 :args ((=> p q))) "^
       "(assume-push @local p) "^
       "(step-pop @scope (=> p p) :rule scope :premises (@local)))"}]

  fun is_prefix [] _ = true
    | is_prefix (x::xs) (y::ys) = x = y andalso is_prefix xs ys
    | is_prefix _ [] = false
  fun is_refusal (o_:observation) =
    String.isPrefix "refused" (#outcome o_)

  (* Live, tight-budget (exactly enough, and one short) and stale runs
     of one path; [live] must have been observed already. *)
  fun check_path label (c:case_) path (live:observation) =
    let
      val name = label ^ (case path of Plan => " plan" | Replay => " replay")
      val spec = {assumptions= #assumptions c,text= #text c}
      val exact = #before live + #charged live
      val same = observe spec path (SOME exact) false
      val short = observe spec path (SOME (exact-1)) false
      val stale = observe spec path NONE true
    in
      require (name ^ ": live path charged nothing") (#charged live > 0);
      require (name ^ ": an exact budget changed the outcome or charge")
        (#outcome same = #outcome live andalso
         #charged same = #charged live andalso #steps same = #steps live
         andalso #trace same = #trace live);
      require (name ^ ": one unit short was not refused")
        (is_refusal short andalso
         #before short + #charged short <= exact andalso
         is_prefix (#trace short) (#trace live));
      require (name ^ ": a stale packet was not refused")
        (is_refusal stale andalso #steps stale = 0)
    end

  fun check_case (c:case_) =
    let
      val spec = {assumptions= #assumptions c,text= #text c}
      val plan = observe spec Plan NONE false
      val _ = require (#label c ^ ": planning outcome " ^ #outcome plan)
        (#outcome plan = #expected c)
      val _ = check_path (#label c) c Plan plan
      val replay = observe spec Replay NONE false
    in
      if #expected c = "prepared" then
        (require (#label c ^ ": replay outcome " ^ #outcome replay)
           (#outcome replay = "replayed" andalso #steps replay > 0);
         check_path (#label c) c Replay replay)
      else
        require (#label c ^ ": a pending case replayed")
          (#steps replay = 0)
    end

  fun run () =
    List.app (fn c =>
      (testutils.tprint ("CPC owned classification: " ^ #label c);
       check_case c;testutils.OK ())) cases
end
