(* Contract tests for the source-condition clause preparers. The plain rule,
   the exists-argument clause and the canonical clause each capture the
   Source terms into one retained tree, name the lexical binders and charge
   Work for it. Every check goes through the exported preparation,
   admission and execution functions and states a relation computed within
   one run. No value captured from earlier code is pinned. Unittest
   registers run as the group source_condition_builder_contract. *)
structure SmtReplaySourceConditionTests =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure P = SmtReplayProof
  structure C = SmtLib_OwnedNamedContextSeeds
  structure Scope = SmtReplayOwnedScopeReceipt

  val p = ``sce_builder_p:bool``
  val z = ``sce_builder_z:bool``
  val x = ``sce_builder_x:num``
  val f = ``sce_builder_f:num->bool``
  val quoted = "sce_builder_witness"
  fun instance v = Term.mk_comb (f,v)
  fun imp a b = boolSyntax.mk_imp (a,b)
  fun forall v body = boolSyntax.mk_forall (v,body)
  val prefix = "__smt_sce_binder_"
  (* Free Boolean variables spelled like the first candidate binder names. *)
  fun colliders () = List.tabulate (10,fn n =>
    Term.mk_var (prefix ^ Int.toString n ^ "_0",Type.bool))
  (* One law with an existential antecedent and two shadowed forall binders
     in the consequent; guard holds the colliders, or T when empty. *)
  fun law guard =
    imp (boolSyntax.mk_exists (x,instance x))
      (imp guard (forall x (forall x (imp (instance x) z))))
  val clean = law boolSyntax.T
  val collided = law (boolSyntax.list_mk_conj (colliders ()))

  type env = {graph:G.graph,root:G.scope,work:W.portfolio,sources:S.sources,
    catalogue:C.catalogue,frame:Scope.receipt}
  fun setup limit assumptions : env =
    let val g = G.new () val r = G.root_scope g
        val s = S.new g r 512 {assumptions=assumptions,goal=z}
        val w = W.begin g r s
          {limits={input_limit=5,output_limit=1000,template_limit=50000},
           work_limit=limit}
        val catalogue = C.execute (C.prepare (C.begin_rules_original w
          {check_type=fn _ => ()}))
    in {graph=g,root=r,work=w,sources=s,catalogue=catalogue,
      frame=Scope.root w} end
  val roomy = 20000000
  fun evidence (e:env) index =
    let val source = C.project_rule (#work e) (#catalogue e)
          (List.nth (C.seeds_for (#work e) (#catalogue e),index))
        val d = C.projected_rule_for (#work e) source
        val recipe = P.execute_source_rule (#work e)
          (P.prepare_source_rule (#work e)
            {source= #proof d,frame= #frame e,caller= #root e,steps=[],
             terminal=P.SourceTruth,check_type=fn _ => ()})
    in P.condition_evidence_for_rule (#work e) recipe end
  fun charged (e:env) = #charged (W.audit (#work e))
  fun retired (e:env) = #retired (W.audit (#work e))
  fun require why yes = if yes then () else raise Fail why
  fun refusal action = (ignore (action ());NONE)
    handle Feedback.HOL_ERR error => SOME (Feedback.top_function_of error,
      Feedback.message_of error)
  fun witness (e:env) term =
    G.closure_root (#graph e) (#root e)
      (G.variable (#graph e) (#root e) G.Generated term)
  fun argument (e:env) term =
    G.closure_root (#graph e) (#root e)
      (#node (G.import (#graph e) (#root e) 100 term))
  fun realize (e:env) value =
    P.realize_source_condition_evidence (#work e) value

  (* Exact theorem: conclusion, the exact hypothesis set, each hypothesis
     an original Source root, and no oracle tag. *)
  fun same_set xs ys =
    List.all (fn a => List.exists (fn b => Term.aconv a b) ys) xs andalso
    List.all (fn b => List.exists (fn a => Term.aconv a b) xs) ys
  fun exact (e:env) theorem concl hyps =
    Term.aconv (Thm.concl theorem) concl andalso
    same_set (Thm.hyp theorem) hyps andalso
    List.all (fn hyp => List.exists (fn node =>
      Portable.pointer_eq (hyp,G.representative (#graph e) node))
      (S.assumption_nodes (#sources e))) (Thm.hyp theorem) andalso
    null (Tag.axioms_of (Thm.tag theorem))

  (* The three paths, each from the clean or the collided law. Every path
     returns its environment and the evidence it produced. *)
  fun rule_plan (e:env) check_type =
    P.prepare_source_condition_rule (#work e)
      {evidence=evidence e 0,frame= #frame e,caller= #root e,
       steps=[P.EvidenceAssertion],terminal=P.SourceTruth,
       check_type=check_type}
  fun by_rule law =
    let val e = setup roomy [law]
    in (e,P.execute_source_condition_rule (#work e) (rule_plan e (fn _ => ())))
    end
  fun ready_for (e:env) =
    P.admit_source_condition_exists_argument (#work e)
      (P.prepare_source_condition_exists_argument (#work e)
        {evidence=evidence e 0,frame= #frame e,caller= #root e,
         name=quoted,ty=numSyntax.num,check_type=fn _ => ()})
  fun bind (e:env) ready child =
    P.execute_source_condition_exists_argument (#work e)
      {ready=ready,argument=child}
  fun witness_term () = Term.mk_var (quoted,numSyntax.num)
  fun by_argument law =
    let val e = setup roomy [law]
    in (e,bind e (ready_for e) (witness e (witness_term ()))) end
  fun canonical_start (e:env) =
    P.execute_source_canonical_plan (#work e)
      {ready=P.admit_source_canonical_plan (#work e)
        (P.prepare_source_canonical_start (#work e)
          {evidence=evidence e 0,check_type=fn _ => ()}),arguments=[]}
  fun canonical_future (e:env) state check_type =
    P.prepare_source_canonical_future (#work e)
      {state=state,operation=P.CanonicalExists,
       quotations=[(quoted,numSyntax.num)],check_type=check_type}
  fun canonical_ready (e:env) = P.admit_source_canonical_plan (#work e)
    (canonical_future e (canonical_start e) (fn _ => ()))
  fun canonical_bind (e:env) ready child =
    P.execute_source_canonical_plan (#work e) {ready=ready,arguments=[child]}
  fun by_canonical law =
    let val e = setup roomy [law]
        val state = canonical_bind e (canonical_ready e)
          (witness e (witness_term ()))
    in (e,P.source_canonical_current_for (#work e) state) end

  (* Theorems. *)
  fun rule_theorem () =
    let val e = setup roomy [imp p (forall x (boolSyntax.mk_eq (x,x))),p]
        val child = argument e ``0:num``
        val rule = P.execute_source_condition_rule (#work e)
          (P.prepare_source_condition_rule (#work e)
            {evidence=evidence e 0,frame= #frame e,caller= #root e,
             steps=[P.EvidenceAssertion,P.EvidenceStep P.SourceCondition,
                    P.EvidenceStep (P.SourceSpec child)],
             terminal=P.SourceEquality,check_type=fn _ => ()})
        val joined = P.execute_source_conditions (#work e)
          (P.prepare_source_conditions (#work e)
            {rule=rule,premises=[evidence e 1],check_type=fn _ => ()})
    in require "rule path changed the conditional SPEC theorem"
      (exact e (realize e joined) (boolSyntax.mk_eq (``0:num``,``0:num``))
         [imp p (forall x (boolSyntax.mk_eq (x,x))),p]) end
  (* The consequent shared by the conditional endpoints of the clean law. *)
  val inner = forall x (forall x (imp (instance x) z))
  fun rule_assertion_theorem () =
    let val (e,result) = by_rule clean
        val wanted = boolSyntax.mk_eq (clean,boolSyntax.T)
    in require "rule path changed the assertion theorem"
      (exact e (realize e result) wanted [clean]) end
  fun argument_theorem () =
    let val (e,result) = by_argument clean
        val wanted = imp (instance (witness_term ()))
          (boolSyntax.mk_eq (imp boolSyntax.T inner,boolSyntax.T))
    in require "argument path changed the conditional endpoint or Hyp"
      (exact e (realize e result) wanted [clean]) end
  fun canonical_theorem () =
    let val (e,result) = by_canonical clean
        val wanted = imp (instance (witness_term ()))
          (imp boolSyntax.T inner)
    in require "canonical path changed the conditional endpoint or Hyp"
      (exact e (realize e result) wanted [clean]) end

  (* Fresh binder origins: emitted names carry the private prefix, are
     distinct, and avoid every variable the clause already uses. *)
  fun rows (e:env) value =
    #binders (P.source_condition_binder_origins_for (#work e)
      (P.prepare_source_condition_binder_origins (#work e) value))
  fun var_name term = #1 (Term.dest_var term)
  fun well_formed (e:env) law rows =
    let val emitted = List.map (fn (_,_,v) => var_name v) rows
        val used = List.map var_name (Term.all_vars law)
        fun distinct [] = true
          | distinct (a::rest) =
              not (List.exists (fn b => a = b) rest) andalso distinct rest
    in length rows >= 2 andalso distinct emitted andalso
       List.all (fn name => String.isPrefix prefix name andalso
         not (List.exists (fn old => old = name) used)) emitted andalso
       List.all (fn (_,old,v) => not (Term.term_eq old v)) rows end
  fun origins_of path law =
    let val (e,result) = path law val rs = rows e result
    in require "emitted binders are not fresh private names"
         (well_formed e law rs);
       rs end
  fun origin_test path () =
    let val plain = origins_of path clean
        val clash = origins_of path collided
        fun shape rs = List.map (fn (p,old,_) => (p,old)) rs
        fun names rs = List.map (fn (_,_,v) => var_name v) rs
    in require "binder lexical origins changed with the identifier set"
         (ListPair.allEq (fn ((a,b),(c,d)) => a = c andalso Term.term_eq b d)
            (shape plain,shape clash));
       require "colliding identifiers did not move the emitted binder names"
         (names plain <> names clash) end

  (* A future argument minted in a scope other than the actual frame, and a
     caller that is not the actual frame, are refused. *)
  fun sibling (e:env) =
    G.new_construction_scope (#graph e)
      {construction= #root e,lexical= #root e}
  fun foreign_child (e:env) =
    let val scope = sibling e
        val node = G.variable (#graph e) scope G.Generated (witness_term ())
    in G.closure_root (#graph e) scope node end
  (* Each refusal names its origin and retires the owner. *)
  fun refused_with (e:env) origin action =
    refusal action = SOME origin andalso retired e
  val foreign_frame = ("closure_child","different graph or caller scope")
  fun wrong_argument_frame () =
    let val e = setup roomy [clean] val ready = ready_for e
        val child = foreign_child e
    in require "argument bound a variable from a foreign frame"
      (refused_with e foreign_frame (fn () => bind e ready child)) end
  fun wrong_argument_caller () =
    let val e = setup roomy [clean] val scope = sibling e
    in require "argument caller other than the actual frame was admitted"
      (refused_with e ("prepare_source_argument",
         "caller must be the actual frame") (fn () =>
         P.prepare_source_condition_exists_argument (#work e)
           {evidence=evidence e 0,frame= #frame e,caller=scope,
            name=quoted,ty=numSyntax.num,check_type=fn _ => ()})) end
  fun wrong_canonical_frame () =
    let val e = setup roomy [clean] val ready = canonical_ready e
        val child = foreign_child e
    in require "canonical future bound a variable from a foreign frame"
      (refused_with e foreign_frame (fn () =>
         canonical_bind e ready child)) end
  fun wrong_rule_frame () =
    let val e = setup roomy [clean] val child = foreign_child e
    in require "rule child from a foreign frame was admitted"
      (refused_with e foreign_frame (fn () =>
         P.prepare_source_condition_rule (#work e)
           {evidence=evidence e 0,frame= #frame e,caller= #root e,
            steps=[P.EvidenceAssertion,P.EvidenceStep (P.SourceSpec child)],
            terminal=P.SourceTruth,check_type=fn _ => ()})) end

  (* A second execution or admission is refused and retires the owner. *)
  fun second_rule () =
    let val e = setup roomy [clean]
        val plan = rule_plan e (fn _ => ())
        val _ = P.execute_source_condition_rule (#work e) plan
    in require "consumed rule plan executed again"
      (refused_with e ("execute_source_condition_rule","consumed")
         (fn () => P.execute_source_condition_rule (#work e) plan)) end
  fun second_argument () =
    let val e = setup roomy [clean] val ready = ready_for e
        val _ = bind e ready (witness e (witness_term ()))
        val child = witness e (witness_term ())
    in require "consumed argument ready executed again"
      (refused_with e ("execute_source_argument","ready already consumed")
         (fn () => bind e ready child)) end
  fun second_argument_admission () =
    let val e = setup roomy [clean]
        val plan = P.prepare_source_condition_exists_argument (#work e)
          {evidence=evidence e 0,frame= #frame e,caller= #root e,
           name=quoted,ty=numSyntax.num,check_type=fn _ => ()}
        val _ = P.admit_source_condition_exists_argument (#work e) plan
    in require "argument plan was admitted twice"
      (refused_with e ("admit_source_argument",
         "plan already admitted or consumed") (fn () =>
         P.admit_source_condition_exists_argument (#work e) plan)) end
  fun second_canonical () =
    let val e = setup roomy [clean] val ready = canonical_ready e
        val _ = canonical_bind e ready (witness e (witness_term ()))
        val child = witness e (witness_term ())
    in require "consumed canonical ready executed again"
      (refused_with e ("canonical_execute","ready already consumed")
         (fn () => canonical_bind e ready child)) end

  (* Charged prefix: the preparation succeeds with exactly its own total
     charge as the allowance and is refused with one unit less. A refusal
     keeps a prefix of the successful charges that grows with the allowance
     and never exceeds it. *)
  datatype outcome = Done | Refused
  fun attempt law stage limit =
    let val e = setup limit [law]
        val action = stage e
        val before = charged e
        val outcome = (action ();Done)
          handle Feedback.HOL_ERR _ => Refused
    in (outcome,before,charged e,retired e) end
  fun prefix_test law stage () =
    let val (_,before,total,_) = attempt law stage roomy
        val _ = require "preparation charged nothing" (total > before)
        val (exact_outcome,_,exact_charge,exact_retired) =
          attempt law stage total
        val (spare_outcome,_,spare_charge,_) = attempt law stage (total+7)
        val (short,_,short_charge,short_retired) =
          attempt law stage (total-1)
        val _ = require "exact allowance refused or overcharged"
          (exact_outcome = Done andalso exact_charge = total andalso
           spare_outcome = Done andalso spare_charge = total andalso
           not exact_retired)
        val _ = require "allowance minus one was not refused and retired"
          (short = Refused andalso short_retired)
        fun sample limit =
          let val (outcome,_,paid,gone) = attempt law stage limit
          in require "refusal exceeded its allowance or kept Work live"
               (outcome = Refused andalso paid <= limit andalso gone);
             paid end
        val span = total - before
        val limits = [before,before+span div 3,before+2*span div 3,total-1]
        val paid = List.map sample limits
        fun grows (a::(rest as b::_)) = a <= b andalso grows rest
          | grows _ = true
    in require "refused charges are not a growing prefix"
         (grows paid andalso short_charge <= total-1
          andalso List.last paid = short_charge) end
  fun rule_stage e =
    let val value = evidence e 0
    in fn () => ignore (P.prepare_source_condition_rule (#work e)
         {evidence=value,frame= #frame e,caller= #root e,
          steps=[P.EvidenceAssertion],terminal=P.SourceTruth,
          check_type=fn _ => ()}) end
  fun argument_stage e =
    let val value = evidence e 0
    in fn () => ignore (P.prepare_source_condition_exists_argument (#work e)
         {evidence=value,frame= #frame e,caller= #root e,name=quoted,
          ty=numSyntax.num,check_type=fn _ => ()}) end
  fun canonical_stage e =
    let val state = canonical_start e
    in fn () => ignore (canonical_future e state (fn _ => ())) end

  fun test label action = (testutils.tprint label;action ();testutils.OK ())
  fun run () =
    (test "source condition rule path: exact theorem and Hyp" rule_theorem;
     test "source condition rule path: assertion theorem"
       rule_assertion_theorem;
     test "source condition argument path: exact theorem and Hyp"
       argument_theorem;
     test "source condition canonical path: exact theorem and Hyp"
       canonical_theorem;
     test "source condition rule path: fresh binder origins"
       (origin_test by_rule);
     test "source condition argument path: fresh binder origins"
       (origin_test by_argument);
     test "source condition canonical path: fresh binder origins"
       (origin_test by_canonical);
     test "source condition rule path: foreign-frame child refused"
       wrong_rule_frame;
     test "source condition argument path: foreign-frame future refused"
       wrong_argument_frame;
     test "source condition argument path: non-actual caller refused"
       wrong_argument_caller;
     test "source condition canonical path: foreign-frame future refused"
       wrong_canonical_frame;
     test "source condition rule path: second execution refused"
       second_rule;
     test "source condition argument path: second execution refused"
       second_argument;
     test "source condition argument path: second admission refused"
       second_argument_admission;
     test "source condition canonical path: second execution refused"
       second_canonical;
     test "source condition rule path: charged prefix on refusal"
       (prefix_test clean rule_stage);
     test "source condition argument path: charged prefix on refusal"
       (prefix_test clean argument_stage);
     test "source condition canonical path: charged prefix on refusal"
       (prefix_test clean canonical_stage))
end
