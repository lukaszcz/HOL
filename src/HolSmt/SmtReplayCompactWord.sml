(* Copyright (c) 2026 The HOL4 contributors. *)

(* Checked finite-word programs. Actual source admission stays with the
   replay owner. Programs and Boolean shapes use its existing bounded proof
   caches; operands enter only after the generic theorem has been checked. *)
structure SmtReplayCompactWord :> SmtReplayCompactWord =
struct
open HolKernel;
exception Declined;
fun bounded_type ty =
 let val left=ref 64
     fun visit ty=if !left=0 then false else
       (left:= !left-1;
        if Type.is_vartype ty then String.size (Type.dest_vartype ty)<=64
        else let val {Tyop,Args,...}=Type.dest_thy_typeid ty
          in String.size (KernelSig.name_of Tyop)<=64 andalso
             String.size (KernelSig.seg_of Tyop)<=64 andalso
             List.all visit Args end)
 in visit ty end;
(* Completed syntax checks only; admission still belongs to the owner. *)
fun new_type_guard () =
 let val types=Array.array (16,NONE:Type.hol_type option)
     val next=ref 0
     fun check ty=if Array.exists (fn SOME old=>
           Portable.pointer_eq (old,ty) | NONE=>false) types then true
       else if bounded_type ty then
         (Array.update (types,!next,SOME ty);
          next:=(!next+1) mod Array.length types;true)
       else false
 in check end;
fun bounded_name term =
 if Term.is_var term then String.size (#1 (Term.dest_var term))<=64
 else if Term.is_const term then
   let val {Name,Thy,...}=Term.dest_thy_const term
   in String.size Name<=64 andalso String.size Thy<=64 end
 else true;
fun bounded_source source =
 let val small_type=new_type_guard ()
  fun inspect term=not (Term.is_abs term) andalso bounded_name term andalso
    small_type (Term.type_of term) andalso
    List.all inspect (SmtResource.term_children term)
 in Option.isSome (SmtReplayImport.bounded_raw_size 8192 source) andalso
   inspect source end;

 exception DomainDecline;
 fun numeric_id n = #Tyop (Type.dest_thy_typeid
   (fcpSyntax.mk_int_numeric_type n))
 val one_id=numeric_id 1
 val even_id=numeric_id 2
 val odd_id=numeric_id 3
 fun bounded_width ty =
  if Type.is_vartype ty then raise DomainDecline else
  let val {Tyop,Args,...}=Type.dest_thy_typeid ty
      fun same old=KernelSig.id_compare (Tyop,old)=EQUAL
      fun child ()=case Args of [arg]=>bounded_width arg
        | _=>raise DomainDecline
  in if same one_id andalso null Args then 1
     else if same even_id then
       let val n=child () in if n<=16 then 2*n else raise DomainDecline end
     else if same odd_id then
       let val n=child () in if n<16 then 2*n+1 else raise DomainDecline end
     else raise DomainDecline
  end

 fun finite_domain source =
  let
   val word_names=["n2w","word_add","word_sub","word_mul","word_div",
     "word_mod","word_quot","word_rem","word_1comp","word_2comp",
     "word_and","word_or","word_xor","word_nand","word_nor","word_xnor",
     "word_lsl_bv","word_lsr_bv","word_asr_bv","word_ror_bv","word_rol_bv",
     "word_lsl","word_lsr","word_asr","word_ror","word_rol",
     "word_extract","word_bits","word_signed_bits","word_slice",
     "word_join","word_concat","w2w","sw2sw","word_lsb","word_msb",
     "word_bit","word_lt","word_le","word_gt","word_ge","word_lo",
     "word_ls","word_hi","word_hs","word_L","word_H","word_T"]
   val boolean=[boolSyntax.T,boolSyntax.F,boolSyntax.negation,
     boolSyntax.conjunction,boolSyntax.disjunction,boolSyntax.implication,
     boolSyntax.equality,boolSyntax.conditional]
   fun literal bound term=case Lib.total numLib.dest_numeral term of
       SOME n=>if Arbnum.compare (n,bound)<>GREATER then ()
         else raise DomainDecline
     | NONE=>raise DomainDecline
   fun allowed term=List.exists (Term.same_const term) boolean orelse
     let val {Thy,Name,...}=Term.dest_thy_const term
     in (Thy="words" andalso List.exists (fn n=>n=Name) word_names) orelse
        (Thy="fcp" andalso Name="'") end
   fun walk term =
    if Term.type_of term=numSyntax.num then literal (Arbnum.fromInt 32) term
    else
      let
       val ty=Term.type_of term
       val _=if wordsSyntax.is_word_type ty then
         if bounded_width (wordsSyntax.dest_word_type ty)<=32 then ()
         else raise DomainDecline
        else ()
       val _=case Lib.total wordsSyntax.dest_word_mul term of
           SOME (a,b)=>if wordsSyntax.is_word_literal a orelse
             wordsSyntax.is_word_literal b then () else raise DomainDecline
         | NONE=>()
      in case Lib.total wordsSyntax.dest_n2w term of
           SOME (number,_)=>literal
             (Arbnum.pow (Arbnum.two,Arbnum.fromInt 32)) number
         | NONE=>if Term.is_const term then
             if allowed term then () else raise DomainDecline
           else if Term.is_comb term then
             (walk (Term.rator term);walk (Term.rand term))
           else if Term.is_var term andalso
             (ty=Type.bool orelse wordsSyntax.is_word_type ty) then ()
           else raise DomainDecline
      end
  in walk source;true end handle DomainDecline=>false;

fun eligible source=bounded_source source andalso finite_domain source;

fun prepare_program hole source =
let
 fun small_type ty =
   let val remaining=ref 64
       fun walk ty=(remaining:= !remaining-1;
         if !remaining<0 then raise Declined
         else if Type.is_vartype ty then ()
         else List.app walk (#Args (Type.dest_thy_type ty)))
   in walk ty;if Type.uptodate_type ty then () else raise Declined end
 fun inspect term=if Term.is_abs term then raise Declined
   else if Term.is_var term orelse Term.is_const term then
     (small_type (Term.type_of term);
      if Term.uptodate_term term then () else raise Declined)
   else ()
 val {complete,...}=SmtResource.bounded_structure_with_children
   (fn term=>if Term.is_comb term then [Term.rator term,Term.rand term]
     else []) inspect 8192 source
 val _=complete orelse raise Declined
 val resolve=SmtSkeletonProve.new_cache_index 8192
 val id=SmtReplaySchemaBuilder.node_ids_for_call
   (fn t=>case resolve t of SOME key=>key | NONE=>raise Declined)
 (* This optional producer accepts only the actual finite numeric Type
    constructors. Other dimensions retain the original replay route. *)
 fun numeric_width ty=bounded_width ty
   handle DomainDecline=>raise Declined
 fun small_word ty = if not (wordsSyntax.is_word_type ty) then () else
   let val width=numeric_width (wordsSyntax.dest_word_type ty)
   in if width>0 andalso width<=32 then () else raise Declined end
   handle Feedback.HOL_ERR detail=>
     if SmtResource.is_resource_gate detail then raise Feedback.HOL_ERR detail
     else raise Declined
        | Overflow=>raise Declined
 val counts=ref (Redblackmap.mkDict Int.compare)
 val visited=ref (HOLset.empty Int.compare)
 val variables=ref ([]:term list)
 fun scan t =
   let val key=id t
       val _=counts:=Redblackmap.insert (!counts,key,
         1+Option.getOpt (Redblackmap.peek (!counts,key),0))
   in if HOLset.member (!visited,key) then () else
      (visited:=HOLset.add (!visited,key);
       if Term.is_var t then variables:=t:: !variables
       else if Term.is_comb t then (scan (Term.rator t);scan (Term.rand t))
       else if Term.is_abs t then raise Declined else ()) end
 val _=scan source
 val memo=ref (Redblackmap.mkDict Int.compare)
 val definitions=ref ([]:term list)
 val aliases=ref ([]:(term*term) list)
 fun abstract t=case Redblackmap.peek (!memo,id t) of SOME result=>result
   | NONE=>let
       val body=if Term.is_comb t then
           Term.mk_comb (abstract (Term.rator t),abstract (Term.rand t))
         else t
       val ty=Term.type_of t
       val _=small_word ty
       val uses=Redblackmap.find (!counts,id t)
       val size=if uses<=1 then SOME 1 else
         SmtReplayImport.bounded_raw_size 8192 body
       val profitable=case size of NONE=>true
         | SOME n=>(uses-1)*(n-1)>8
       val chosen=Term.is_comb t andalso uses>1 andalso profitable andalso
         (ty=Type.bool orelse wordsSyntax.is_word_type ty) andalso
         not (wordsSyntax.is_word_literal t)
       val result=if not chosen then body else
         let val index=length (!aliases)
             val _=index<5000 orelse raise Declined
             val variable=hole (4000+index) ty
             val _=aliases:=(variable,t):: !aliases
             val _=definitions:=boolSyntax.mk_eq (body,variable):: !definitions
         in variable end
       val _=memo:=Redblackmap.insert (!memo,id t,result)
     in result end
 val result=abstract source
 fun balanced []=boolSyntax.T
   | balanced [t]=t
   | balanced ts=let val n=length ts div 2
       in boolSyntax.mk_conj (balanced (List.take (ts,n)),
         balanced (List.drop (ts,n))) end
 val context=balanced (List.rev (!definitions))
 val program=boolSyntax.mk_imp (context,result)
 val size=case SmtReplayImport.bounded_raw_size 8192 program of
     SOME n=>n | NONE=>raise Declined
 val input_substitutions=ListPair.map (fn (i,v)=>
     v |-> hole (10000+i) (Term.type_of v))
   (List.tabulate (length (!variables),fn i=>i),List.rev (!variables))
 val proposed=List.map #1 (!aliases) @ List.map #residue input_substitutions
 val _=not (List.exists (fn input=>List.exists
   (Term.term_eq input) proposed) (!variables)) orelse raise Declined
 val key=Term.subst input_substitutions program
 val raw=SmtReplayImport.bounded_raw_size 8192 key
 val _=Option.isSome raw orelse raise Declined
 val cost=SmtResource.dag_nodes_up_to 8193 key
in {key=key,context=context,result=result,aliases=List.rev (!aliases),
    inputs=input_substitutions,memo= !memo,cost=cost,
    dag=HOLset.numItems (!visited),id=id} end;



exception GeneralMeasure
fun measure_normalized_for_test input =
   let val small_type=new_type_guard ()
    fun inspect term=if Term.is_var term orelse Term.is_const term orelse
        Term.is_abs term then
      if small_type (Term.type_of term) andalso bounded_name term then ()
      else raise GeneralMeasure
     else ()
    val {complete,...}=SmtResource.bounded_structure_with_children
      SmtSkeletonProve.term_children inspect
      SmtResource.max_bv_replay_term_nodes input
   in if complete then SmtResource.term_measure input
      else SmtSkeletonProve.term_measure input end
   handle GeneralMeasure=>SmtSkeletonProve.term_measure input

fun prove_schema bit field_law word_law source =
 let
  val resolve=SmtSkeletonProve.new_cache_index
    SmtResource.max_bv_replay_term_nodes
  val id=SmtReplaySchemaBuilder.node_ids_for_call
    (fn t=>case resolve t of SOME key=>key | NONE=>raise Declined)
  val memo=ref (Redblackmap.mkDict Int.compare)
  fun atomic input =
   let
    val variables=Term.free_vars input
    val sigma=ListPair.map (fn (variable,i)=>variable |->
       Term.mk_var ("smt_compact_operand_" ^ Int.toString i,
         Term.type_of variable))
       (variables,List.tabulate (length variables,fn i=>i))
    val key=Term.subst sigma input
    val actual=ref NONE
    fun make ()=case !actual of SOME theorem=>theorem
      | NONE=>let
        val normalized=Library.replay_word_normalize_conv key
        val converted=Conv.QCONV (SmtBitBlastProve.convert_atomic bit)
          (boolSyntax.rhs (Thm.concl normalized))
        val theorem=Thm.TRANS normalized converted
        val _=actual:=SOME theorem
       in theorem end
    val generic=Profile.profile_with_exn_name "program/atomic-conversion"
      (fn ()=>field_law key make
        handle Feedback.HOL_ERR detail=>
          if SmtResource.is_resource_gate detail then
            raise Feedback.HOL_ERR detail else make ()) ()
    val reverse=List.map (fn {redex,residue}=>residue |-> redex) sigma
   in SmtSkeletonProve.nodewise_exact_left input (Thm.INST reverse generic) end
  fun convert input=case Redblackmap.peek (!memo,id input) of
      SOME theorem=>theorem
    | NONE=>let
       val theorem=if Term.type_of input=Type.bool andalso
           not (Term.is_var input) andalso
           not (Option.isSome (SmtSkeletonProve.skeleton_children input))
         then atomic input
         else if Term.is_comb input then
           Thm.MK_COMB (convert (Term.rator input),convert (Term.rand input))
         else Thm.REFL input
       val _=memo:=Redblackmap.insert (!memo,id input,theorem)
      in theorem end
  val converted=Profile.profile_with_exn_name "program/boolean-lowering"
    convert source
  val residue=boolSyntax.rhs (Thm.concl converted)
  val measure=Profile.profile_with_exn_name "program/sat-measure"
    measure_normalized_for_test residue
  val _= #dag_nodes measure<=SmtResource.max_bv_replay_term_nodes
    orelse raise Declined
  val reverse=ref ([]:{redex:term,residue:term} list)
  val atom_order=SmtSkeletonProve.new_semantic_order ()
  val atoms=ref (Redblackmap.mkDict atom_order)
  val constructors=ref (Redblackmap.mkDict
    (Lib.pair_compare (KernelSig.id_compare,Lib.list_compare Int.compare)))
  val next=ref 0
  fun fresh ()=let val key= !next in next:=key+1;key end
  val physical=Array.array (4093,[]:(term*(term*int)) list)
  val physical_nodes=ref 0
  fun boolean input =
   let val bucket=SmtReplayImport.pointer_bucket 4 4093 input
   in case List.find (fn (old,_)=>Portable.pointer_eq (old,input))
       (Array.sub (physical,bucket)) of SOME (_,value)=>value
    | NONE=>let
       val value=case SmtSkeletonProve.skeleton_children input of
           NONE=>(case Redblackmap.peek (!atoms,input) of
               SOME value=>value
             | NONE=>let
                 val variable=Term.mk_var ("smt_compact_atom_" ^
                   Int.toString (length (!reverse)),Type.bool)
                 val value=(variable,fresh ())
                 val _=reverse:=(variable |-> input):: !reverse
                 val _=atoms:=Redblackmap.insert (!atoms,input,value)
                in value end)
         | SOME children=>let
             val values=List.map boolean children
             val (head,_)=boolSyntax.strip_comb input
             val {Name,...}=Term.dest_thy_constid head
             val key=(Name,List.map #2 values)
            in case Redblackmap.peek (!constructors,key) of
                SOME value=>value
              | NONE=>let
                  val term=List.foldl (fn ((child,_),operator)=>
                    Term.mk_comb (operator,child)) head values
                  val value=(term,fresh ())
                  val _=constructors:=Redblackmap.insert
                    (!constructors,key,value)
                 in value end
            end
       val _=physical_nodes:= !physical_nodes+1
       val _= !physical_nodes<=SmtResource.max_bv_replay_term_nodes
         orelse raise Declined
       val _=Array.update (physical,bucket,
         (input,value)::Array.sub (physical,bucket))
      in value end
   end
  val target=Profile.profile_with_exn_name "program/sat-naming"
    (fn term=> #1 (boolean term)) residue
  fun native ()=SmtBitBlastProve.prove_boolean bit target
  fun reusable ()=if Option.isSome
      (SmtReplayImport.bounded_raw_size 8192 target) then
    word_law target native else native ()
  val _=Profile.profile_with_exn_name "program/sat-observer"
    SmtSkeletonProve.observe_sat_target target
  val started=Time.now ()
  val generic=Profile.profile_with_exn_name "program/boolean-sat" reusable ()
  val _=Option.app (fn observe=>observe
    (target,Time.- (Time.now (),started)))
    (!SmtSkeletonProve.sat_completion_observer)
  val theorem=Profile.profile_with_exn_name "program/sat-instantiation"
    (Thm.INST (!reverse)) generic

 in Thm.EQ_MP (Thm.SYM converted) theorem end;

fun prove_in owner prover hole actual
 (substitutions:{redex:term,residue:term} list) schema =
 let val prepared=Profile.profile_with_exn_name "program/prepare"
       (prepare_program hole) schema
     val {key,inputs,aliases,id,...}=prepared
     val _=bounded_source key andalso
       finite_domain key orelse raise Declined
     val realization=ref (Redblackmap.mkDict Int.compare)
     fun lookup t=List.find (fn {redex,...}=>Term.term_eq redex t)
       substitutions
     fun realize t=case Redblackmap.peek (!realization,id t) of
       SOME value=>value
     | NONE=>let val value=case lookup t of
           SOME {residue,...}=>residue
         | NONE=>if Term.is_comb t then
            let val f=Term.rator t val x=Term.rand t
                val g=realize f val y=realize x
            in if Portable.pointer_eq (f,g) andalso Portable.pointer_eq (x,y)
               then t else Term.mk_comb (g,y) end else t
       in realization:=Redblackmap.insert (!realization,id t,value);value end
     val generic=SmtSkeletonProve.cached_sat_proof owner key (#cost prepared)
       (fn () =>(Profile.profile_with_exn_name "program/prove" prover key))
     val generic=SmtSkeletonProve.exact_conclusion key generic
     val _=assert null (Thm.hyp generic)
     val _=Library.check_oracle_tags "SmtReplayCompactWord" "program" generic
     val aliases=List.map (fn (v,t)=>(v,realize t)) aliases
     val sigma=List.map (fn {redex,residue}=>residue |-> realize redex) inputs @
       List.map (fn (v,t)=>v |-> t) aliases
     val law=Profile.profile_with_exn_name "program/instantiate"
       (Thm.INST sigma) generic
     val definitions=SmtCircuitSat.balanced_conjunction
       (List.map (Thm.REFL o #2) aliases)
     val theorem=Profile.profile_with_exn_name "program/finish"
       (SmtSkeletonProve.exact_conclusion actual o
        (fn theorem=>Thm.MP theorem definitions)) law
 in theorem end;

end;
