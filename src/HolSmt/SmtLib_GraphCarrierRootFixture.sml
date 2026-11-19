(* Test support: live fixtures for the policy provers of
   SmtLib_GraphCarrierRoot (a goal, its stock carrier law, a native
   contract, a focus admission and, for the opaque case, genuine retained
   profiles). Shared by selftest postludes 279 and 290 and by
   SmtLib_GraphCarrierRootPolicyTests. *)
structure SmtLib_GraphCarrierRootFixture =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure P = SmtReplayProof
  structure Q = SmtReplayFocusAdmission
  structure RP = SmtReplayResourcePolicy
  structure NC = SmtReplayNativeContract
  structure H = SmtLib_GraphLawTypeInstance
  val cap = 100000
  val metadata : RP.semantic_policy =
    {input_limit=RP.Uncapped,output_limit=RP.Uncapped,
     template_limit=RP.Uncapped}
  val native : NC.limits =
    {semantic_limits={input_limit=cap,output_limit=cap,template_limit=cap},
     import_limit=cap,type_work_limit=2000000}
  type fixture = {graph:G.graph,scope:G.scope,sources:S.sources,
    work:W.portfolio,native:NC.contract,admission:Q.policy_focus,
    law:P.closed_fact,node:G.node}
  fun require text yes = if yes then () else raise Fail text
  (* [policy] is the Work portfolio's metadata policy and [work_limit]
     bounds the portfolio, setup included. *)
  fun setup_policy policy work_limit term fixed limits : fixture =
    let val graph = G.new () val scope = G.root_scope graph
        val sources = S.new_with_policy graph scope RP.Uncapped
          {goal=term,assumptions=[]}
        val view = G.record_opened_view_with_policy graph scope
          (RP.AtMost (IntInf.fromInt cap)) (#node (S.goal_source sources))
        val imported = G.import_with_policy graph scope
          (RP.AtMost (IntInf.fromInt cap)) (Thm.concl fixed)
        val opened = G.record_opened_view_with_policy graph scope
          (RP.AtMost (IntInf.fromInt cap)) (#node imported)
        val law = P.record_closed_from_import_with_policy graph scope
          {node= #node opened,theorem=fixed,template_limit=RP.Uncapped,
           check_type=fn _=>()}
        val work = W.begin_with_policy graph scope sources
          {limits=policy,work_limit=work_limit}
        val contract = NC.capture work limits
        val admission = Q.initial_goal_with_policy work {view=SOME view}
    in {graph=graph,scope=scope,sources=sources,work=work,native=contract,
        admission=admission,law=law,node= #node view} end
  fun setup_limited work_limit = setup_policy metadata work_limit
  fun setup term fixed limits = setup_limited RP.Uncapped term fixed limits
  fun expected (e : fixture) =
    {graph= #graph e,scope= #scope e,sources= #sources e,work= #work e}
  fun producer (e : fixture) callback = H.begin_original_with_policy
    (#graph e) (#scope e)
    {original= #law e,work= #work e,native_contract= #native e,
     check_type=callback}
  type opaque =
    {fixture:fixture,profiles:G.policy_opaque_profile list,
     body_profiles:G.policy_opaque_profile list,
     root_profiles:G.policy_opaque_profile list,body_frame:G.scope}
  (* Genuine Source -> ALPHA equality -> P scoped wrapper -> Q Generated.
     No raw node is adopted as a focus or labelled a registered Source view.
     [body_profiles] come from the frame inside the binder, [root_profiles]
     from the root frame; [profiles] is both. *)
  fun opaque_setup_limited work_limit body_issued limits : opaque =
    let val graph=G.new() val scope=G.root_scope graph
        val n=Term.mk_var("profiled_carrier_n",numSyntax.num)
        val z=Term.mk_var("profiled_carrier_z",Type.bool)
        val opaque=Term.mk_abs(z,boolSyntax.mk_neg z)
        val f=Term.mk_var("profiled_carrier_f",
          Type.mk_type("fun",[Term.type_of opaque,
            Type.mk_type("fun",[numSyntax.num,Type.bool])]))
        val term=boolSyntax.mk_forall(n,Term.list_mk_comb(f,[opaque,n]))
        val sources=S.new_with_policy graph scope RP.Uncapped
          {goal=term,assumptions=[]}
        val frame=G.new_scope graph scope []
        val binder=G.variable graph frame G.Bound n
        val body_frame=G.new_scope graph frame [(n,binder)]
        val origin=if body_issued then body_frame else scope
        val retained= #node(G.import_with_policy graph origin
          (RP.AtMost(IntInf.fromInt cap)) opaque)
        val q=Term.mk_var("profiled_carrier_q",Type.bool)
        val beta=Term.mk_comb(Term.mk_abs(q,q),boolSyntax.T)
        val wrapped=boolSyntax.mk_conj(boolSyntax.mk_eq(opaque,opaque),beta)
        val wrapper=G.import_with_policy graph origin
          (RP.AtMost(IntInf.fromInt cap)) wrapped
        val discovery=G.discover_partial_with_policy graph origin
          {original= #node wrapper,maximum=RP.AtMost(IntInf.fromInt cap),
           scan_limit=RP.AtMost 2000000,step=fn()=>()}
        val body_profiles=G.partial_profiles_with_policy graph origin discovery
        (* The original Source's whole predicate is a DISTINCT retained
           opaque node. Its real no-op profile is required by the equality's
           left side as well as the RHS's smaller retained operand. *)
        val original_predicate=Term.rand
          (G.representative graph (#node(S.goal_source sources)))
        val root_wrapper=G.import_with_policy graph scope
          (RP.AtMost(IntInf.fromInt cap))
          (boolSyntax.mk_conj
            (boolSyntax.mk_eq(original_predicate,original_predicate),beta))
        val root_discovery=G.discover_partial_with_policy graph scope
          {original= #node root_wrapper,maximum=RP.AtMost(IntInf.fromInt cap),
           scan_limit=RP.AtMost 2000000,step=fn()=>()}
        val root_profiles=
          G.partial_profiles_with_policy graph scope root_discovery
        val profiles=body_profiles @ root_profiles
        val _=require "opaque fixture lost actual retained operand"
          (case G.view graph retained of G.OpaqueRetained=>true | _=>false)
        val work=W.begin_with_policy graph scope sources
          {limits=metadata,work_limit=work_limit}
        val contract=NC.capture work limits
        fun step()=(NC.validate_for work contract;W.spend_policy work 1)
        val operator=G.variable graph scope G.RigidSource f
        val head=G.application graph body_frame (operator,retained)
        val body=G.application graph body_frame (head,binder)
        val predicate=W.with_step work (fn()=>
          G.recorded_abstraction_with_profile_policy graph scope
            {maximum=RP.Uncapped,
             native_limit= #output_limit(#semantic_limits limits),
             type_work_limit= #type_work_limit limits,
             binder=binder,body=body,body_frame=body_frame,
             profiles=profiles,step=step})
        val universal=G.constant graph scope
          (Term.rator(G.representative graph (#node(S.goal_source sources))))
        val node=G.application graph scope (universal,predicate)
        val original= #node(S.goal_source sources)
        val theorem=Thm.ALPHA (G.representative graph original)
          (G.representative graph node)
        val equality=Term.rator(Term.rator(Thm.concl theorem))
        val equality_head=G.constant graph scope equality
        val partial=G.application graph scope (equality_head,original)
        val equation=G.application graph scope (partial,node)
        val saved=P.record_generated_equality_with_policy_scoped_profiles
          graph scope {node=equation,theorem=theorem,
            template_limit=RP.Uncapped,profiles=profiles,check_type=fn _=>()}
        val parent=Q.initial_goal_with_policy work {view=NONE}
        val admission=Q.generated_scoped_with_policy
          {graph=graph,scope=scope,sources=sources,work=work} parent saved
        val fixed=HolSmtTheory.NUM_FORALL_TO_INT
        val imported=G.import_with_policy graph scope
          (RP.AtMost(IntInf.fromInt cap)) (Thm.concl fixed)
        val opened=G.record_opened_view_with_policy graph scope
          (RP.AtMost(IntInf.fromInt cap)) (#node imported)
        val law=P.record_closed_from_import_with_policy graph scope
          {node= #node opened,theorem=fixed,template_limit=RP.Uncapped,
           check_type=fn _=>()}
    in {fixture={graph=graph,scope=scope,sources=sources,work=work,
          native=contract,admission=admission,law=law,node=node},
        profiles=profiles,body_profiles=body_profiles,
        root_profiles=root_profiles,body_frame=body_frame} end
  fun opaque_setup body_issued limits =
    let val {fixture,profiles,...}=
          opaque_setup_limited RP.Uncapped body_issued limits
    in (fixture,profiles) end
end
