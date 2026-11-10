(* The existing local SPEC programme; admission belongs to its caller. *)
signature SmtReplayLocalSpecialize =
sig
  (* Only this unobserved constructor can issue a cacheable metric. There
     is deliberately no import from a general G.profiled_metric, whose
     retained observer might run callbacks. No native admission is granted. *)
  type metric
  val prepare_metric : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {node:SmtReplayGraph.node,
     profiles:SmtReplayGraph.policy_opaque_profile list} -> metric
  val metric_data : SmtReplayGraph.graph -> SmtReplayGraph.scope -> metric ->
    {node:SmtReplayGraph.node,raw:IntInf.int,inc:IntInf.int,
     types:Type.hol_type list}
  (* Caller must validate its NC and actual supplied Scope receipt on EVERY
     invocation, BEFORE this guard. Only callback-free captured metrics may
     be skipped at an unchanged revision AND scope-retirement epoch. The
     returned closure owns its cache; no global cache or authority is made. *)
  val metric_cache_guard :
    {metrics:(SmtReplayGraph.node * metric) list,
     work:SmtReplayInvocationWork.portfolio,graph:SmtReplayGraph.graph,
     scope:SmtReplayGraph.scope,error:string -> exn} -> unit -> unit

  type profile={raw:IntInf.int,inc:IntInf.int,ann:IntInf.int,ty:IntInf.int}
  type profile_operations=
    {tick:unit -> unit,type_weight:Type.hol_type -> IntInf.int,
     type_seen:Type.hol_type -> unit,input:IntInf.int,output:IntInf.int,
     template:IntInf.int,ceiling:IntInf.int,error:string -> exn}
  (* Only after the genuine requester bounds the complete retained input
     graph, including opaque binders and repeated Type annotations. Predicted
     substitution results must be admitted before their materialization.
     This is the existing local native walker, not a profile authority. *)
  val native_profile : profile_operations -> Term.term -> profile
  type forecast_operations=
    {profile:Term.term -> profile,tick:unit -> unit,pay:IntInf.int -> unit,
     in_bound:profile -> unit,out_bound:profile -> unit,
     charge:profile -> profile list -> profile list -> unit,first:profile,
     variable_compare:Term.term * Term.term -> order,error:string -> exn}
  (* SAME proof-free predictor used by the owned local SPEC programme.
     The actual owner supplies a fully admitted profile before any native
     syntax destructor or substitution, and quotes predicted input/result/
     Hyp/Type portfolios before substitution. This helper mints no proof,
     Source right, size certificate or binder permission. Comparisons and
     callbacks retain the caller's genuine guards and actual Work charges. *)
  val forecast : forecast_operations -> Term.term -> Term.term list ->
    profile list -> Term.term * Term.term list
  (* Alternate syntax-only miss classification. The old owned caller uses
     the exact public dest_forall above. No authentication failure may be
     caught as an ordinary syntax miss by this supplied destructor. *)
  val forecast_using :
    {dest_forall:Term.term -> Term.term * Term.term,
     substitute:Term.term * Term.term * Term.term -> Term.term} ->
    forecast_operations -> Term.term -> Term.term list ->
    profile list -> Term.term * Term.term list
  type closing_operations=
    {out_bound:profile -> unit,law_bound:profile -> unit,
     charge:profile -> profile list -> profile list -> unit}
  (* SAME complete DISCH/ALPHA/EQ_MP portfolio, before the law is built. *)
  val close_forecast : closing_operations -> {first:profile,final:profile} ->
    {law:profile,equation:profile}
  val callback_forest :
    {visit:unit -> unit,type_weight:Type.hol_type -> IntInf.int,
     ceiling:IntInf.int,error:string -> exn} ->
    Type.hol_type list -> IntInf.int
  (* The actual owned requester must first admit every native input,
     predicted intermediate/result, surviving hypothesis and Type portfolio.
     call retains its existing guards/observation programme. This helper
     grants neither Source ownership nor an operand/binder admission. *)
  val run :
    {original:Term.term,arguments:Term.term list,steps:Term.term list,
     canonical:unit -> Term.term,call:(unit -> Thm.thm) -> Thm.thm,
     error:string -> exn} -> {proof:Thm.thm,canonical:Term.term}
end
