(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplaySchemaBuilderTests =
struct
open HolKernel testutils;
fun run () =
let
val _=tprint "schema constructor sharing bounds and native fallback";
fun arrow (a,b)=Type.mk_type ("fun",[a,b]);
val cache=SmtReplaySchemaBuilder.new_context ();
val f=Term.mk_var ("schema_f",arrow (Type.bool,Type.bool));
val x=Term.mk_var ("schema_x",Type.bool);
val cold= SmtReplaySchemaBuilder.application cache (f,x);
val warm= SmtReplaySchemaBuilder.application cache (f,x);
val _=assert (fn () => Portable.pointer_eq (cold,warm)) ();
fun valid (f,x) result =
 let val (actual_f,actual_x)=Term.dest_comb result
 in assert (fn () => Portable.pointer_eq (f,actual_f) andalso
       Portable.pointer_eq (x,actual_x)) () end;
val _=valid (f,x) cold;
val _=List.app (fn n=>
 let val input=Term.mk_var ("schema_pressure_" ^ Int.toString n,Type.bool)
     val result= SmtReplaySchemaBuilder.application cache (f,input)
     val {retained_nodes,entries}= SmtReplaySchemaBuilder.stats_for_test cache
 in valid (f,input) result;
    assert (fn () => retained_nodes<=8192 andalso entries<=8192) () end)
 (List.tabulate (9000,Lib.I));
val _=assert (fn () => Portable.pointer_eq
 (cold,SmtReplaySchemaBuilder.application cache (f,x))) ();
fun lists 0=Type.bool
 | lists n=Type.mk_thy_type {Thy="list",Tyop="list",Args=[lists (n-1)]};
fun type_case depth should_store =
 let val ty=lists depth
     val input=Term.mk_var ("schema_typed",ty)
     val operator=Term.mk_var ("schema_typed_f",arrow (ty,Type.bool))
     val fresh=SmtReplaySchemaBuilder.new_context ()
     val result= SmtReplaySchemaBuilder.application fresh (operator,input)
     val _=valid (operator,input) result
 in assert (fn () =>
   (#entries (SmtReplaySchemaBuilder.stats_for_test fresh)>0)=should_store)
   () end;
val _=type_case 61 true;
val _=type_case 62 false;
val binder=Term.mk_abs (x,x);
val binder_op=Term.mk_var ("schema_binder_f",arrow
 (Term.type_of binder,Type.bool));
val fresh=SmtReplaySchemaBuilder.new_context ();
val _=valid (binder_op,binder)
 (SmtReplaySchemaBuilder.application fresh (binder_op,binder));
val _=assert (fn () =>
  #entries (SmtReplaySchemaBuilder.stats_for_test fresh)=0) ();
val name="schema_sharing_epoch";
val _=Theory.new_constant (name,Type.bool);
val stale=Term.prim_mk_const {Thy=Theory.current_theory (),Name=name};
val epoch_cache=SmtReplaySchemaBuilder.new_context ();
val prior= SmtReplaySchemaBuilder.application epoch_cache (f,stale);
val _=Theory.delete_const name;
val after= SmtReplaySchemaBuilder.application epoch_cache (f,stale);
val _=valid (f,stale) after;
val _=assert (fn () => not (Portable.pointer_eq (prior,after)) andalso
  #entries (SmtReplaySchemaBuilder.stats_for_test epoch_cache)=0) ();
val calls=ref 0;
val x=Term.mk_var ("local_id_x",Type.bool);
val resource=Feedback.mk_HOL_ERR "SmtResource" "local_id_test"
 "resource-gated: exact first resolver error";
val bad=Term.mk_var ("local_id_bad",Type.bool);
val interrupt=Term.mk_var ("local_id_interrupt",Type.bool);
fun resolve term =
 (calls:= !calls+1;
  if Portable.pointer_eq (term,bad) then raise resource
  else if Portable.pointer_eq (term,interrupt) then raise Interrupt
  else String.size (#1 (Term.dest_var term)));
val cached=SmtReplaySchemaBuilder.node_ids_for_call resolve;
val first=cached x;
val _=assert (fn () => cached x=first andalso !calls=1) ();
val alias=Term.mk_var ("local_id_x",Type.bool);
val _=assert (fn () => cached alias=first) ();
val _=assert (fn () => !calls=
 (if Portable.pointer_eq (alias,x) then 1 else 2)) ();
fun failure predicate source =
 case ((ignore (cached source);NONE) handle error=>SOME error) of
   SOME error=>assert predicate error
 | NONE=>raise Fail "local ID helper swallowed a terminal error";
fun same_resource (Feedback.HOL_ERR detail)=
  SmtResource.is_resource_gate detail andalso
  Feedback.message_of detail="resource-gated: exact first resolver error"
 | same_resource _=false;
val _=failure same_resource bad;
val _=failure same_resource bad;
val _=failure (fn Interrupt=>true | _=>false) interrupt;
val _=List.app (fn n=>
 let val term=Term.mk_var ("local_id_pressure_" ^ Int.toString n,Type.bool)
 in assert (fn () => cached term=String.size (#1 (Term.dest_var term))) () end)
 (List.tabulate (9000,Lib.I));
val before_calls= !calls;
val _=assert (fn () => cached x=first andalso !calls=before_calls) ();
val fresh=Term.mk_var ("local_id_after_full",Type.bool);
val _=ignore (cached fresh);
val _=ignore (cached fresh);
val _=assert (fn () => !calls=before_calls+2) ();
val _=failure same_resource bad;
val _=failure (fn Interrupt=>true | _=>false) interrupt;

val _=OK ();
val _=tprint "replay node ID hints preserve admissions and epoch ownership";
val visits=ref 0;
val absent=Term.mk_var ("replay_id_absent",Type.bool);
fun replay_resolve term =
 (visits:= !visits+1;
  if Portable.pointer_eq (term,bad) then raise resource
  else if Portable.pointer_eq (term,interrupt) then raise Interrupt
  else if Portable.pointer_eq (term,absent) then NONE
  else SOME (String.size (#1 (Term.dest_var term))));
val replay=SmtReplaySchemaBuilder.node_ids_for_replay replay_resolve;
val initial=replay x;
val _=assert (fn () => replay x=initial andalso !visits=1) ();
val _=assert (fn () => replay alias=initial) ();
val _=assert (fn () => !visits=
 (if Portable.pointer_eq (alias,x) then 1 else 2)) ();
fun replay_failure expected term = case Exn.capture replay term of
 Exn.Exn error=>assert expected error
 | _=>raise Fail "replay ID hint swallowed a terminal error";
val prior_visits= !visits;
val _=assert (fn () => replay absent=NONE andalso replay absent=NONE) ();
val _=assert (fn () => !visits=prior_visits+2) ();
val _=replay_failure same_resource bad;
val _=replay_failure same_resource bad;
val _=replay_failure (fn Interrupt=>true | _=>false) interrupt;
val _=replay_failure (fn Interrupt=>true | _=>false) interrupt;
val _=List.app (fn n=>
 let val term=Term.mk_var ("replay_id_pressure_" ^ Int.toString n,Type.bool)
 in assert (fn () => replay term=
      SOME (String.size (#1 (Term.dest_var term)))) () end)
 (List.tabulate (9000,Lib.I));
val prior_visits= !visits;
val _=assert (fn () => replay x=initial andalso !visits=prior_visits) ();
val _=ignore (replay fresh);
val _=ignore (replay fresh);
val _=assert (fn () => !visits=prior_visits+2) ();
val _=replay_failure same_resource bad;
val _=replay_failure (fn Interrupt=>true | _=>false) interrupt;

val native=SmtSkeletonProve.new_cache_index 8192;
val hinted=SmtReplaySchemaBuilder.node_ids_for_replay
 (SmtSkeletonProve.new_cache_index 8192);
val y=Term.mk_var ("replay_native_y",Type.bool);
val z=Term.mk_var ("replay_native_z",Type.bool);
val w=Term.mk_var ("replay_native_w",wordsSyntax.mk_int_word_type 3);
val terms=[x,x,alias,y,boolSyntax.mk_conj (x,y),
 boolSyntax.mk_conj (x,y),w,wordsSyntax.mk_word_add (w,w),
 boolSyntax.mk_forall (y,boolSyntax.mk_imp (y,x)),
 boolSyntax.mk_forall (z,boolSyntax.mk_imp (z,x))];
val _=List.app (fn term=>assert (fn () => native term=hinted term) ()) terms;

(* The replay context, rather than a hint lookup, owns invalidation of
   both the resolver and its positive physical table. *)
val epoch=Z3_ProofReplay.new_fp_node_index_for_test ();
val _=List.app (fn n=>ignore (epoch (Term.mk_var
 ("replay_epoch_seed_" ^ Int.toString n,Type.bool))))
 (List.tabulate (10,Lib.I));
val saved=epoch x;
val _=assert (fn () => saved<>SOME 0) ();
val name="replay_id_epoch";
val _=Theory.new_constant (name,Type.bool);
val _=Portable.finally (fn () => Theory.delete_const name)
 (fn () => assert (fn () => epoch x=SOME 0) ()) ();
val _=assert (fn () => epoch x=SOME 0) ();
in OK () end
end
