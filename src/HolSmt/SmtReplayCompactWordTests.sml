(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayCompactWordTests =
struct
open HolKernel Parse testutils;
fun require true _=() | require false text=raise Fail text;
fun checked source theorem =
 (require (Term.aconv source (Thm.concl theorem)) "wrong compact endpoint";
  require (null (Thm.hyp theorem)) "compact proof retained hypotheses";
  Library.check_oracle_tags "SmtReplayCompactWordTests" "checked" theorem);
fun fails action = case Exn.capture action () of
 Exn.Exn Interrupt=>raise Interrupt
 | Exn.Exn _=>() | _=>raise Fail "negative compact case succeeded";
fun run () = let
 val _=tprint "compact word proofs, cache kinds, and source admissions";
 val producer=Z3_ProofReplay.new_compact_word_prover_for_test ();
 val atom_context=SmtBitBlastProve.new_context ();
 val atom=``((a:word32)+b)=c``;
 val first_atom=SmtBitBlastProve.convert_atomic atom_context atom;
 val cold_atom=SmtBitBlastProve.stats_for_test atom_context;
 val second_atom=SmtBitBlastProve.convert_atomic atom_context atom;
 val warm_atom=SmtBitBlastProve.stats_for_test atom_context;
 val _=require (#hits warm_atom> #hits cold_atom andalso
   #retained_dag_nodes warm_atom<=8192 andalso
   Term.aconv (Thm.concl first_atom) (Thm.concl second_atom))
   "whole atom conversions did not share the original bit-cache budget";
 val _=require (not (Option.isSome (SmtReplayImport.bounded_raw_size
   8192 (Thm.concl first_atom))))
   "large atom conversion lost its unfolded-size boundary";
 val _=require (null (Thm.hyp second_atom)) "atom cache retained hypotheses";
 val _=Library.check_oracle_tags "SmtReplayCompactWordTests"
   "large atom cache" second_atom;
 val goal=``((x:word8)+(x+1w)) + (x+(x+1w)) = (x+(x+1w)) << 1``;
 val _=checked goal (producer goal);
 val _=fails (fn ()=>producer ``(x:word8)=x+1w``);
 val wide=Term.mk_var ("wide",wordsSyntax.mk_int_word_type 33);
 val _=require (not (SmtReplayCompactWord.eligible
   (boolSyntax.mk_eq (wide,wide)))) "wide word entered compact producer";
 val _=require (not (SmtReplayCompactWord.eligible ``(f:word8 -> word8) x=x``))
   "unsupported function entered compact producer";
 val _=Theory.new_type ("bit0",1);
 val _=Portable.finally (fn ()=>Theory.delete_type "bit0") (fn ()=>
   let val dim=Type.mk_thy_type {Thy=Theory.current_theory (),Tyop="bit0",
         Args=[fcpSyntax.mk_int_numeric_type 1]}
       val variable=Term.mk_var ("foreign",wordsSyntax.mk_word_type dim)
   in require (not (SmtReplayCompactWord.eligible
        (boolSyntax.mk_eq (variable,variable))))
        "foreign bit0 declaration confused numeric dimensions" end) ();
 val x=Term.mk_var ("x",wordsSyntax.mk_int_word_type 8);
 val word_ty=Term.type_of x;
 fun hole i ty=Term.mk_var ("compact_test_hole_" ^ Int.toString i,ty);
 fun shared 0 seed=seed
   | shared n seed=let val child=shared (n-1) seed
       in wordsSyntax.mk_word_add (child,child) end;
 val operand=shared 13 (Term.mk_var ("operand",word_ty));
 val _=require (not (Option.isSome
   (SmtReplayImport.bounded_raw_size 8192 operand)))
   "large-operand test lost its unfolded size";
 val owner=SmtSkeletonProve.new_sat_context ();
 val calls=ref 0;
 fun prove source=(calls:= !calls+1;producer source);
 fun request data=
   let val actual=Term.subst [x |-> data] goal
   in checked actual (SmtReplayCompactWord.prove_in owner prove hole
      actual [x |-> data] goal) end;
 val _=request operand;
 val _=request (shared 13 (Term.mk_var ("other_operand",word_ty)));
 val _=require (!calls=1) "compact program was reproved for new operands";
 val _=Theory.new_constant ("compact_program_epoch",Type.bool);
 val _=Portable.finally (fn ()=>Theory.delete_const "compact_program_epoch")
   (fn ()=>request operand) ();
 val _=require (!calls=2) "program certificate survived a signature change";
 val failure_owner=SmtSkeletonProve.new_sat_context ();
 fun rejected work=SmtReplayCompactWord.prove_in failure_owner work hole
   goal [] goal;
 val _=fails (fn ()=>rejected (fn key=>
   Drule.ADD_ASSUM boolSyntax.T (producer key)));
 val _=fails (fn ()=>rejected (fn key=>
   Thm.mk_oracle_thm "compact_negative" ([],key)));
 val resource=(SmtResource.check_term_size_for "BitVector"
     "compact-first-error" (SmtResource.max_bv_replay_term_nodes+1);
     Fail "unreachable") handle error=>error;
 val _=case Exn.capture (fn ()=>rejected (fn _=>raise resource)) () of
   Exn.Exn error=>require (Feedback.exn_to_string error=
     Feedback.exn_to_string resource) "compact program changed first error"
 | _=>raise Fail "compact program swallowed resource failure";
 val _=case Exn.capture (fn ()=>rejected (fn _=>raise Interrupt)) () of
   Exn.Exn Interrupt=>() | _=>raise Fail "compact program swallowed Interrupt";
 val _=checked goal (rejected producer);
 val (field,bit,atomic)=Z3_ProofReplay.new_fp_conversion_caches_for_test ();
 val conversion_source=``p /\ T``;
 val conversions=ref 0;
 fun refl ()=(conversions:= !conversions+1;Thm.REFL conversion_source);
 fun simplified ()=(conversions:= !conversions+1;
   simpLib.SIMP_CONV boolSimps.bool_ss [] conversion_source);
 val original=field conversion_source refl;
 val _=ignore (bit conversion_source simplified);
 val _=ignore (atomic conversion_source simplified);
 val again=field conversion_source refl;
 val _=require (!conversions=3 andalso
   Term.aconv (Thm.concl original) (Thm.concl again))
   "conversion recipes shared a cache namespace";
 val source_producer=Z3_ProofReplay.new_compact_source_prover_for_test ();
 val _=checked ``(x:word8)=x`` (source_producer ``(x:word8)=x``);
 val huge=List.foldl (fn (i,prior)=>wordsSyntax.mk_word_add (prior,
     Term.mk_var ("source_gate_" ^ Int.toString i,word_ty))) x
   (List.tabulate (3000,Lib.I));
 val _=case Exn.capture source_producer (boolSyntax.mk_eq (huge,huge)) of
   Exn.Exn (Feedback.HOL_ERR detail)=>require
     (SmtResource.is_resource_gate detail andalso String.isSubstring
       "general-reduction" (Feedback.exn_to_string (Feedback.HOL_ERR detail)))
     "compact cache bypassed original source gate"
 | _=>raise Fail "oversized actual source was admitted";
 val _=OK ();
 val _=tprint "compact normalized measurements preserve binder metrics";
 val binders=[``(\x:bool. x)``,``(\y:bool. y)``,``(\x:bool. y)``,
   ``(\x:word8. x+x)``,``(\x:bool. (\y:bool. x /\ y))``];
 val terms=binders @ List.map (fn term=>boolSyntax.mk_eq (term,term)) binders;
 val _=List.app (fn term=>require
   (SmtReplayCompactWord.measure_normalized_for_test term=
    SmtSkeletonProve.term_measure term) "binder metric changed") terms;
 fun boolean_shared 0=boolSyntax.T
   | boolean_shared n=let val child=boolean_shared (n-1)
       in boolSyntax.mk_conj (child,child) end;
 val binder=Term.mk_abs (Term.mk_var ("bound",Type.bool),boolean_shared 22);
 fun diagnostic worker=case Exn.capture worker binder of
   Exn.Exn (Feedback.HOL_ERR detail)=>
     if SmtResource.is_resource_gate detail then
       Feedback.exn_to_string (Feedback.HOL_ERR detail)
     else raise Fail "unexpected metric failure"
 | _=>raise Fail "binder metric source gate disappeared";
 val _=require (diagnostic SmtReplayCompactWord.measure_normalized_for_test=
   diagnostic SmtSkeletonProve.term_measure) "binder first exception changed";
 val _=OK ();
 val _=tprint "recent constructor and node hints retain fixed capacities";
 val builder=SmtReplaySchemaBuilder.new_recent_context ();
 val neg=boolSyntax.negation;
 val _=List.app (fn i=>let
     val input=Term.mk_var ("recent_builder_" ^ Int.toString i,Type.bool)
     val result=SmtReplaySchemaBuilder.application builder (neg,input)
     val {entries,retained_nodes}=SmtReplaySchemaBuilder.stats_for_test builder
   in require (Term.aconv result (Term.mk_comb (neg,input))) "bad constructor";
      require (entries<=8192 andalso retained_nodes<=8192)
        "recent builder grew past its bound" end)
   (List.tabulate (5000,Lib.I));
 val fresh=Term.mk_var ("recent_tail",Type.bool);
 val first=SmtReplaySchemaBuilder.application builder (neg,fresh);
 val second=SmtReplaySchemaBuilder.application builder (neg,fresh);
 val _=require (Portable.pointer_eq (first,second))
   "recent constructor cache froze after pressure";
 val visits=ref 0;
 val hint=SmtReplaySchemaBuilder.node_ids_for_recent_replay
   (fn _=>(visits:= !visits+1;SOME 7));
 val seed=Term.mk_var ("hint_seed",Type.bool);
 val _=ignore (hint seed);
 val _=List.app (fn i=>ignore (hint (Term.mk_var
   ("hint_pressure_" ^ Int.toString i,Type.bool))))
   (List.tabulate (8192,Lib.I));
 val _=ignore (hint fresh);
 val prior_visits= !visits;
 val _=ignore (hint fresh);
 val _=require (!visits=prior_visits) "recent hints stopped retaining new nodes";
 val _=ignore (hint seed);
 val _=require (!visits=prior_visits+1) "recent hint exceeded its fixed capacity";
 in OK () end;
end
