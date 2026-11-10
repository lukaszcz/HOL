(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayWordProgramTests =
struct
open HolKernel;
val ERR=Feedback.mk_HOL_ERR "SmtReplayWordProgramTests";
fun require text condition=if condition then () else raise ERR "run" text;
fun hole position ty=Term.mk_var
  ("word_program_test_" ^ Int.toString position,ty);
fun word_expression ty depth seed base =
 let
  fun constant n=wordsSyntax.mk_n2w
    (numSyntax.mk_numeral (Arbnum.fromInt n),wordsSyntax.dest_word_type ty)
  fun step 0 value=value
    | step n value=step (n-1)
        (wordsSyntax.mk_word_xor
          (wordsSyntax.mk_word_add (value,constant ((n+seed) mod 256)),value))
 in step depth base end;
fun fixture ty depth seed name =
 let val word=word_expression ty depth seed (Term.mk_var (name,ty))
 in (boolSyntax.mk_eq (word,word),fn () => Thm.REFL word) end;
fun valid source theorem =
 (require "wrong source conclusion" (Term.aconv source (Thm.concl theorem));
  require "retained hypotheses" (List.null (Thm.hyp theorem));
  Library.check_oracle_tags "SmtReplayWordProgramTests" "result" theorem);
fun stats owner =
 let val _= #refresh_caches (owner:SmtSkeletonProve.sat_context) ()
     val entries= !(#proofs owner)
     val total=List.foldl (fn ((key,theorem,cost),n)=>
       (require "cache key and conclusion do not share an occurrence"
          (Portable.pointer_eq (key,Thm.concl theorem));
        require "cached hypotheses" (List.null (Thm.hyp theorem));
        require "unbounded program" (Option.isSome
          (SmtReplayImport.bounded_raw_size 8192 key));
        n+cost)) 0 entries
 in require "joint cache budget" (total= !(#nodes owner) andalso total<=8192);
    (length entries,total) end;
fun checked owner admissions productions (source,make) =
 SmtReplayWordProgram.prove_in owner hole source (fn () =>
   (admissions:= !admissions+1;
    ignore (SmtReplayWordProgram.prepare_source owner source);
    fn () =>(productions:= !productions+1;make ())));
fun classify error=case error of Interrupt=>"Interrupt"
 | Timeout.TIMEOUT duration=>"TIMEOUT " ^ Time.toString duration
 | Feedback.HOL_ERR detail=>Feedback.top_structure_of detail ^ "." ^
     Feedback.top_function_of detail ^ ":" ^ Feedback.message_of detail
 | _=>General.exnName error;
fun expect expected action =case Exn.capture action () of
    Exn.Res _=>raise ERR "run" "missing expected exception"
  | Exn.Exn error=>require "changed first exception"
      (classify error=classify expected);
fun run () =
let
 val ty=wordsSyntax.mk_int_word_type 8
 val owner=SmtSkeletonProve.new_sat_context ()
 val admissions=ref 0
 val productions=ref 0
 val first=fixture ty 100 7 "program_first"
 val second=fixture ty 100 7 "program_second"
 val _=valid (#1 first) (checked owner admissions productions first)
 val _=require "cold source producer not called" (!productions=1)
 val (entries,_) = stats owner
 val _=require "compact theorem was not retained" (entries>0)
 val _=valid (#1 second) (checked owner admissions productions second)
 val _=require "canonical input renaming did not reuse proof"
   (!admissions=2 andalso !productions=1)
 val _=List.app (fn name=>
   let val fresh=SmtSkeletonProve.new_sat_context ()
       val admitted=ref 0
       val calls=ref 0
       val input=fixture ty 100 7 name
       val _=valid (#1 input) (checked fresh admitted calls input)
       val _=valid (#1 input) (checked fresh admitted calls input)
   in require "source variable captured by a program parameter"
        (!calls=2 andalso #1 (stats fresh)=0) end)
   ["word_program_test_4000","word_program_test_10000"]
 val failure=Feedback.mk_HOL_ERR "SmtResource" "program-first"
   "resource-gated: word-program sentinel"
 val timeout=Timeout.TIMEOUT (Time.fromMilliseconds 7)
 val _=List.app (fn error=>
   (expect error (fn () => SmtReplayWordProgram.prove_in owner hole
      (#1 second) (fn () =>raise error));
    require "hit called producer after failed source admission"
      (!productions=1))) [failure,timeout,Interrupt]
 val _=List.app (fn error=>
   let val fresh=SmtSkeletonProve.new_sat_context ()
       val called=ref 0
       fun attempt ()=SmtReplayWordProgram.prove_in fresh hole (#1 first)
         (fn () =>fn () =>(called:= !called+1;raise error))
       val _=expect error attempt
       val _=expect error attempt
   in require "failed producer was cached" (!called=2);
      require "failed cache is not empty" (#1 (stats fresh)=0) end)
   [failure,timeout,Interrupt]
 val _=List.app (fn make=>
   let val fresh=SmtSkeletonProve.new_sat_context ()
       val called=ref 0
       fun attempt ()=SmtReplayWordProgram.prove_in fresh hole (#1 first)
         (fn () =>fn () =>(called:= !called+1;make ()))
       fun rejected ()=case Exn.capture attempt () of
           Exn.Res _=>raise ERR "run" "invalid producer was accepted"
         | Exn.Exn (Feedback.HOL_ERR _)=>()
         | Exn.Exn error=>raise error
       val _=rejected ()
       val _=rejected ()
   in require "invalid producer was cached" (!called=2);
      require "invalid producer retained an entry" (#1 (stats fresh)=0) end)
   [fn () =>Thm.REFL boolSyntax.T,
    fn () =>Drule.ADD_ASSUM boolSyntax.T (#2 first ()),
    fn () =>Thm.mk_oracle_thm "word-program-rejected" ([],#1 first)]
 fun type_nodes ty=1+(if Type.is_vartype ty then 0 else
   List.foldl (fn (arg,n)=>type_nodes arg+n) 0
     (#Args (Type.dest_thy_type ty)))
 fun argument_type limit =
   let fun grow arg=let val function=Type.mk_type ("fun",[arg,ty])
       in if type_nodes function=limit then arg
          else if type_nodes function>limit then raise ERR "run" "Type fixture"
          else grow (Type.mk_type ("list",[arg])) end
   in grow Type.bool end
 fun type_fixture limit =
   let val arg=argument_type limit
       val operator=Term.mk_var ("program_function",Type.mk_type
         ("fun",[arg,ty]))
       val base=Term.mk_comb (operator,Term.mk_var ("program_argument",arg))
       val word=word_expression ty 100 7 base
   in (boolSyntax.mk_eq (word,word),fn () =>Thm.REFL word) end
 val _=List.app (fn (limit,stored)=>
   let val fresh=SmtSkeletonProve.new_sat_context ()
       val admissions=ref 0
       val calls=ref 0
       val input=type_fixture limit
       val _=valid (#1 input) (checked fresh admissions calls input)
       val _=valid (#1 input) (checked fresh admissions calls input)
   in require "Type boundary changed admission or source calls"
        (!admissions=2 andalso !calls=(if stored then 1 else 2));
      require "Type boundary cache admission"
        ((#1 (stats fresh)>0)=stored) end) [(64,true),(65,false)]
 val _=List.app (fn (width,stored)=>
   let val fresh=SmtSkeletonProve.new_sat_context ()
       val admissions=ref 0
       val calls=ref 0
       val input=fixture (wordsSyntax.mk_int_word_type width)
         100 7 "program_width"
       val _=valid (#1 input) (checked fresh admissions calls input)
       val _=valid (#1 input) (checked fresh admissions calls input)
   in require "word width boundary"
        (!calls=(if stored then 1 else 2) andalso
         ((#1 (stats fresh)>0)=stored)) end) [(32,true),(33,false)]
 (* The source has few Type/term nodes and an immediate native proof.
    Its dimension's cardinality is enormous; optional metadata must decline
    before numeric-Type decoding attempts to construct that integer. *)
 fun tower 0=fcpSyntax.mk_int_numeric_type 2
   | tower n=Type.mk_type ("fun",[tower (n-1),
       fcpSyntax.mk_int_numeric_type 2])
 val tower_word=Term.mk_var ("program_tower",
   wordsSyntax.mk_word_type (tower 6))
 val tower_source=boolSyntax.mk_eq (tower_word,tower_word)
 val tower_owner=SmtSkeletonProve.new_sat_context ()
 val tower_admitted=ref 0
 val tower_calls=ref 0
 val tower_input=(tower_source,fn () =>Thm.REFL tower_word)
 val _=Timeout.apply (Time.fromSeconds 2) (fn () =>
   (valid tower_source (checked tower_owner tower_admitted
      tower_calls tower_input);
    valid tower_source (checked tower_owner tower_admitted
      tower_calls tower_input))) ()
 val _=require "large dimension changed original admission/producer"
   (!tower_admitted=2 andalso !tower_calls=2 andalso
    #1 (stats tower_owner)=0)
 (* Compound dimensions were already supported by the optional cache. *)
 val one_dim=fcpSyntax.mk_int_numeric_type 1
 val two_dim=fcpSyntax.mk_int_numeric_type 2
 val compound_dims=[Type.mk_type ("sum",[one_dim,one_dim]),
   Type.mk_type ("prod",[two_dim,two_dim]),
   Type.mk_type ("fun",[two_dim,two_dim]),
   Type.mk_type ("cart",[two_dim,two_dim])]
 val _=List.app (fn dim=>
   let val fresh=SmtSkeletonProve.new_sat_context ()
       val admissions=ref 0
       val calls=ref 0
       val word_ty=wordsSyntax.mk_word_type dim
       val input=fixture word_ty 100 7 "program_compound_first"
       val again=fixture word_ty 100 7 "program_compound_second"
       val _=valid (#1 input) (checked fresh admissions calls input)
       val _=valid (#1 again) (checked fresh admissions calls again)
   in require "compound dimension lost existing admission/reuse"
        (!admissions=2 andalso !calls=1 andalso #1 (stats fresh)>0) end)
   compound_dims
 (* A base of one stays small even for an enormous exponent. *)
 val unit_dim=Type.mk_type ("fun",[tower 6,one_dim])
 val unit_ty=wordsSyntax.mk_word_type unit_dim
 fun unit_fixture name =
   let val atoms=List.tabulate (100,fn n=>
         let val v=Term.mk_var (name ^ Int.toString n,unit_ty)
         in boolSyntax.mk_eq (v,v) end)
       val body=boolSyntax.list_mk_conj atoms
   in (boolSyntax.mk_eq (body,body),fn () =>Thm.REFL body) end
 val unit_owner=SmtSkeletonProve.new_sat_context ()
 val unit_admissions=ref 0
 val unit_calls=ref 0
 val unit_first=unit_fixture "program_unit_first"
 val unit_second=unit_fixture "program_unit_second"
 val _=Timeout.apply (Time.fromSeconds 2) (fn () =>
   (valid (#1 unit_first)
      (checked unit_owner unit_admissions unit_calls unit_first);
    valid (#1 unit_second)
      (checked unit_owner unit_admissions unit_calls unit_second))) ()
 val _=require "bounded power lost a small result with a large exponent"
   (!unit_admissions=2 andalso !unit_calls=1 andalso
    #1 (stats unit_owner)>0)
 val large=fixture ty 700 7 "program_large"
 val fresh=SmtSkeletonProve.new_sat_context ()
 val calls=ref 0
 val admitted=ref 0
 val _=valid (#1 large) (checked fresh admitted calls large)
 val _=valid (#1 large) (checked fresh admitted calls large)
 val _=require "unbounded compact source entered cache"
   (!calls=2 andalso #1 (stats fresh)=0)
 val binder=Term.mk_abs (Term.mk_var ("program_bound",Type.bool),boolSyntax.T)
 val operator=Term.mk_var ("program_binder_function",Type.mk_type
   ("fun",[Term.type_of binder,ty]))
 val word=word_expression ty 100 7 (Term.mk_comb (operator,binder))
 val bound_source=boolSyntax.mk_eq (word,word)
 val bound_owner=SmtSkeletonProve.new_sat_context ()
 val bound_calls=ref 0
 fun bound ()=SmtReplayWordProgram.prove_in bound_owner hole bound_source
   (fn () =>fn () =>(bound_calls:= !bound_calls+1;Thm.REFL word))
 val _=valid bound_source (bound ())
 val _=valid bound_source (bound ())
 val _=require "binder was cached"
   (!bound_calls=2 andalso #1 (stats bound_owner)=0)
 val _=List.app (fn seed=>
   let val input=fixture ty 100 seed "program_pressure"
       val _=valid (#1 input) (checked owner admissions productions input)
   in ignore (stats owner) end) (List.tabulate (12,fn n=>n+20))
 val last=fixture ty 100 31 "program_last"
 val before_calls= !productions
 val _=valid (#1 last) (checked owner admissions productions last)
 val _=require "recent pressure entry was not reused"
   (!productions=before_calls)
 val name="word_program_signature_fence"
 val _=Theory.new_constant (name,Type.bool)
 val _=require "signature addition retained programs" (#1 (stats owner)=0)
 val _=valid (#1 first) (checked owner admissions productions first)
 val _=Theory.delete_const name
 val _=require "signature deletion retained programs" (#1 (stats owner)=0)
 val changed=SmtSkeletonProve.new_sat_context ()
 val _=valid (#1 first)
   (SmtReplayWordProgram.prove_in changed hole (#1 first)
     (fn () =>fn () =>
       (Theory.new_constant (name,Type.bool);#2 first ())))
 val _=require "signature-changing producer was cached"
   (#1 (stats changed)=0)
 val _=Theory.delete_const name
in ignore (stats owner) end;
end
