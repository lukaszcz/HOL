(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtBitBlastProveTests =
struct
open HolKernel testutils Parse;
fun run () =
let
val _=tprint "bounded bit conversions and native Boolean replay"
val cache=SmtBitBlastProve.new_context ();
val sources=[``((x:word3) + y) = (y + x)``,
 ``((x:word3) + x) = (x << 1)``,
 ``((x:word3) + 3w) = (3w + x)``,
 ``((x:word2) + y) = (y + x)``,
 ``!x:word3. x + 0w = x``];
fun valid target law =
 (assert null (Thm.hyp law);
  assert (Term.aconv target) (boolSyntax.lhs (Thm.concl law));
  Library.check_oracle_tags "SmtBitBlastProveTests" "controls" law);
val _=List.app (fn source=>
 let val old=Conv.QCONV blastLib.BBLAST_CONV source
     val cold=Conv.QCONV (SmtBitBlastProve.convert cache) source
     val warm=Conv.QCONV (SmtBitBlastProve.convert cache) source
 in valid source cold;valid source warm;
    assert (Term.aconv (Thm.concl old)) (Thm.concl cold);
    assert (Term.aconv (Thm.concl cold)) (Thm.concl warm); ()
 end) sources;
val _=List.app (fn source=>
 let val law=Conv.QCONV (SmtBitBlastProve.convert cache) source
 in valid source law; assert (fn t=>not (Term.aconv boolSyntax.T t))
      (boolSyntax.rhs (Thm.concl law)); () end)
 [``(0w:word3) = 1w``,``(x:word3) = 1w``];
val terminal=Feedback.mk_HOL_ERR "SmtResource" "test"
  "resource-gated: exact first terminal";
val ordinary=Feedback.mk_HOL_ERR "SmtBitBlastProveTests" "test" "ordinary decline";
val source=``((x:word3) + 1w) = y``;
fun is_terminal error=case error of Feedback.HOL_ERR detail=>
 SmtResource.is_resource_gate detail andalso
 Feedback.message_of detail = "resource-gated: exact first terminal"
 | _=>false;
fun failure expected thunk = case
 ((ignore (thunk ());NONE) handle error=>SOME error) of
 SOME error=>assert expected error
 | NONE=>raise Fail "expected failure";
val _=failure is_terminal (fn () =>
 SmtBitBlastProve.convert (SmtBitBlastProve.new_context_with_for_test
   {bit=fn _=>fn _=>raise terminal,boolean=Lib.I}) source);
val _=failure (fn Interrupt=>true | _=>false) (fn () =>
 SmtBitBlastProve.convert (SmtBitBlastProve.new_context_with_for_test
   {bit=fn _=>fn _=>raise Interrupt,boolean=Lib.I}) source);
val _=failure is_terminal (fn () =>
 SmtBitBlastProve.convert (SmtBitBlastProve.new_context_with_for_test
   {bit=Lib.I,boolean=fn _=>fn _=>raise terminal}) source);
val _=failure (fn Interrupt=>true | _=>false) (fn () =>
 SmtBitBlastProve.convert (SmtBitBlastProve.new_context_with_for_test
   {bit=Lib.I,boolean=fn _=>fn _=>raise Interrupt}) source);
fun decline _ _=raise ordinary;
val fallback_cache=SmtBitBlastProve.new_context_with_for_test
 {bit=decline,boolean=Lib.I};
val declined=Conv.QCONV (SmtBitBlastProve.convert fallback_cache) source;
val expected=Conv.QCONV (blastLib.BBLAST_CONV_WITH_STAGES
 {word_simp=I,bit_blast=fn worker=>Lib.mapfilter (decline worker),
  rewrite=Rewrite.ONCE_REWRITE_CONV,prover=I}) source;
val _=valid source declined;
val _=assert (Term.aconv (Thm.concl expected)) (Thm.concl declined);
val {misses,retained_dag_nodes=nodes,...}=
 SmtBitBlastProve.stats_for_test fallback_cache;
val _=assert (fn x=>x=0) misses;
val _=assert (fn x=>x=0) nodes;
val _=ignore (SmtBitBlastProve.convert cache source);
val _=ignore (SmtBitBlastProve.convert cache source);
val {hits,...}=SmtBitBlastProve.stats_for_test cache;
val _=assert (fn x=>x>0) hits;

val invalid_source=SmtBitBlastProve.new_context_with_for_test
 {bit=fn _=>fn _=>Thm.REFL boolSyntax.T,boolean=Lib.I}
val invalid_fallback=Conv.QCONV (SmtBitBlastProve.convert invalid_source)
 source
val _=valid source invalid_fallback
val _=assert (fn n=>n=0)
 (#retained_dag_nodes (SmtBitBlastProve.stats_for_test invalid_source))

val before_state=SmtBitBlastProve.stats_for_test cache
val name="bitblast_cache_epoch"
val _=Theory.new_constant (name,Type.bool)
val _=Portable.finally (fn () => Theory.delete_const name)
 (fn () =>
  let val law=Conv.QCONV (SmtBitBlastProve.convert cache) source
      val after=SmtBitBlastProve.stats_for_test cache
  in valid source law;
     assert (fn n=>n> #misses before_state) (#misses after);() end) ()
val ty=wordsSyntax.mk_int_word_type 8
fun pressure i=wordsSyntax.mk_index
 (wordsSyntax.mk_word_add
   (Term.mk_var ("bit_lru_left_" ^ Int.toString i,ty),
    Term.mk_var ("bit_lru_right_" ^ Int.toString i,ty)),
  numLib.term_of_int 7)
val initial=pressure 0
val law=Conv.QCONV (SmtBitBlastProve.convert cache) initial
val _=List.app (fn i=>
 let val target=pressure i
     val proof=Conv.QCONV (SmtBitBlastProve.convert cache) target
     val state=SmtBitBlastProve.stats_for_test cache
 in valid target proof;
    assert (fn n=>n<=8192) (#retained_dag_nodes state);() end)
 (List.tabulate (96,fn i=>i))
val again=Conv.QCONV (SmtBitBlastProve.convert cache) initial
val _=valid initial again
val _=assert (Term.aconv (Thm.concl law)) (Thm.concl again)
in OK () end
end
