(* One shared execution of the already admitted local specialization law. *)
structure SmtReplayLocalSpecialize :> SmtReplayLocalSpecialize =
struct
  structure G=SmtReplayGraph
  structure W=SmtReplayInvocationWork
  (* Opaque at the signature: no observed capture can enter this cache.
     G's policy profiles and closure guards are themselves callback-free. *)
  type metric=G.profiled_metric
  fun prepare_metric graph scope request=
    G.prepare_scoped_profiled_metric graph scope request
  fun metric_data graph scope (capture:metric)=
    G.profiled_metric_data graph scope capture
  fun metric_cache_guard {metrics,work,graph,scope,error} =
    let
      (* New helper record and its five fields only. The consumer retains
         its original setup3; the existing per-call fees remain below. *)
      val _=W.spend_policy work 6
      val checked_metrics=ref NONE
      fun guard()=
        let
          (* Retained fact validation also runs between replay actions.
             This callback-free guard still debits the SAME original Work;
             it grants no action or native-proof authority. *)
          val _=W.spend_guard_policy work 9
          val stamp=(G.validation_revision graph scope,
            G.scope_retirement_epoch graph scope)
          val _=if !checked_metrics=SOME stamp then ()else
            List.app(fn(node,capture)=>
              let val held=metric_data graph scope capture
              in if #node held=node then ()else
                raise error "metric changed"end)metrics
          val _=W.spend_guard_policy work 6
          val after=(G.validation_revision graph scope,
            G.scope_retirement_epoch graph scope)
        in checked_metrics:=if after=stamp then SOME stamp else NONE end
    in guard end

  type profile={raw:IntInf.int,inc:IntInf.int,ann:IntInf.int,ty:IntInf.int}
  type profile_operations=
    {tick:unit -> unit,type_weight:Type.hol_type -> IntInf.int,
     type_seen:Type.hol_type -> unit,input:IntInf.int,output:IntInf.int,
     template:IntInf.int,ceiling:IntInf.int,error:string -> exn}
  fun native_profile ({tick,type_weight,type_seen,input,output,template,
      ceiling,error}:profile_operations) =
    let
      fun fail message=raise error message
      val memo=ref([]:(Term.term * profile)list)
      fun lookup _ []=NONE
        | lookup term((old,value)::rest)=
            (tick();if Portable.pointer_eq(term,old)then SOME value
             else lookup term rest)
      (* Public dest_abs may reconstruct bound syntax. This is a size/Type
         preflight only, not native-AST or endpoint pointer provenance. *)
      fun profile term=case lookup term(!memo)of SOME value=>value
        | NONE=>
          let val _=tick() val ty=Term.type_of term
              val own=type_weight ty
              val _=type_seen ty
              val p:profile=if Term.is_comb term then
                  let val(a,b)=Term.dest_comb term
                      val x=profile a val y=profile b
                  in {raw=1+ #raw x+ #raw y,inc=1+ #inc x+ #inc y,
                      ann=own+ #ann x+ #ann y,ty=own}end
                else if Term.is_abs term then
                  let val(v,b)=Term.dest_abs term
                      val variable=profile v val body=profile b
                  in {raw=1+ #raw body,inc=2+ #inc body,
                      ann=own+ #ann variable+ #ann body,ty=own}end
                else if Term.is_var term orelse Term.is_const term then
                  {raw=1,inc=1,ann=own,ty=own}
                else fail "unknown native syntax"
              val _=if #raw p<=IntInf.max(input,
                  IntInf.max(output,template))andalso
                  #inc p<=IntInf.max(input,IntInf.max(output,template))
                  andalso #ann p<=ceiling then ()else
                fail "actual native syntax exceeds caller bound"
              val _=memo:=(term,p):: !memo
          in p end
    in profile end
  type forecast_operations=
    {profile:Term.term -> profile,tick:unit -> unit,pay:IntInf.int -> unit,
     in_bound:profile -> unit,out_bound:profile -> unit,
     charge:profile -> profile list -> profile list -> unit,first:profile,
     variable_compare:Term.term * Term.term -> order,error:string -> exn}
  fun forecast_using {dest_forall,substitute}
      ({profile,tick,pay,in_bound,out_bound,charge,first,
      variable_compare,error}:forecast_operations) =
    let
      fun fail message=raise error message
      (* Only free occurrences of the actual binder are substituted.
         Shadowing cuts the subtree; memoization retains edge incidence. *)
      fun occurrences variable term=
        let val saved=ref([]:(Term.term * IntInf.int)list)
            fun find _ []=NONE
              | find x((old,n)::rest)=
                  (tick();if Portable.pointer_eq(x,old)then SOME n
                   else find x rest)
            fun same a b=
              (pay(1+ #ty(profile a)+ #ty(profile b));
               variable_compare(a,b)=EQUAL)
            fun walk current=case find current(!saved)of SOME n=>n
              | NONE=>
                let val _=tick()
                    val n=if Term.is_var current then
                        if same current variable then 1 else 0
                      else if Term.is_comb current then
                        let val(a,b)=Term.dest_comb current
                        in walk a+walk b end
                      else if Term.is_abs current then
                        let val(v,b)=Term.dest_abs current
                        in if same v variable then 0 else walk b end
                      else 0
                    val _=saved:=(current,n):: !saved
                in n end
        in walk term end
      fun specialize current [] []=(current,[])
        | specialize current(arg::rest)(ap::more)=
          let val _=tick() val current_p=profile current
              val _=in_bound current_p
              val(variable,body)=dest_forall current
              val variable_p=profile variable val bp=profile body
              val _=pay(1+ #ty variable_p+ #ty ap)
              val _=if Type.compare(Term.type_of variable,
                  Term.type_of arg)=EQUAL then ()else
                fail "native specialization argument Type differs"
              val count=occurrences variable body
              val predicted:profile=
                {raw= #raw bp-count+count* #raw ap,
                 inc= #inc bp-count+count* #inc ap,
                 ann= #ann bp-count* #ty variable_p+count* #ann ap,
                 ty= #ty bp}
              val _=out_bound predicted
              val(_,lambda)=Term.dest_comb current
              val lp=profile lambda
              val combined:profile=
                {raw=1+ #raw lp+ #raw ap,inc=1+ #inc lp+ #inc ap,
                 ann= #ty bp+ #ann lp+ #ann ap,ty= #ty bp}
              val _=out_bound combined
              val _=charge predicted[current_p,ap,combined][first,first]
              (* Actual proof-free prediction after prospective admission.
                 No REFL/Beta/count_body preflight is used. *)
              val next=substitute(variable,arg,body)
              val measured=profile next
              val _=if #raw measured= #raw predicted andalso
                  #inc measured= #inc predicted andalso
                  #ann measured= #ann predicted then ()else
                fail "specialization prediction differs"
              val(answer,tail)=specialize next rest more
          in(answer,next::tail)end
        | specialize _ _ _=fail "private argument portfolio differs"
    in specialize end
  val forecast=forecast_using
    {dest_forall=boolSyntax.dest_forall,substitute=fn(variable,arg,body)=>
       Term.subst[{redex=variable,residue=arg}]body}
  type closing_operations=
    {out_bound:profile -> unit,law_bound:profile -> unit,
     charge:profile -> profile list -> profile list -> unit}
  fun close_forecast ({out_bound,law_bound,charge}:closing_operations)
      {first:profile,final:profile} =
    let
      val law_p:profile=
        {raw=3+ #raw first+ #raw final,inc=3+ #inc first+ #inc final,
         ann=9+ #ann first+ #ann final,ty=1}
      val _=law_bound law_p
      val equation_p:profile=
        {raw=3+2* #raw law_p,inc=3+2* #inc law_p,
         ann=9+2* #ann law_p,ty=1}
      val _=out_bound equation_p
      val _=charge law_p[final][first]
      val _=charge equation_p[law_p,law_p][]
      val _=charge law_p[equation_p,law_p][]
    in {law=law_p,equation=equation_p}end
  fun callback_forest {visit,type_weight,ceiling,error} types =
    let val callback_weight=List.foldl(fn(ty,n)=>
          (visit();n+type_weight ty))(0:IntInf.int)types
    in if callback_weight<=ceiling then callback_weight else
      raise error "local native callback forest exceeds caller Type work"end
  structure O=SmtReplayRuleObservation
  fun run {original,arguments,steps,canonical,call,error} =
    let
      val assumed=call(fn()=>O.ASSUME original)
      fun run proof [] []=proof
        | run proof(arg::rest)(prediction::more)=
            let val result=call(fn()=>O.SPEC arg proof)
                val _=if Term.aconv(Thm.concl result)prediction andalso
                    List.all(fn hyp=>Portable.pointer_eq(hyp,original))
                      (Thm.hyp result)then ()else
                  raise error "native specialization shape/Hyp differs"
            in run result rest more end
        | run _ _ _=raise error "private argument portfolio differs"
      val specialized=run assumed arguments steps
      val closed=call(fn()=>O.DISCH original specialized)
      val canonical=canonical()
      val alignment=call(fn()=>O.ALPHA(Thm.concl closed)canonical)
      val proof=call(fn()=>O.EQ_MP alignment closed)
    in {proof=proof,canonical=canonical} end
end
