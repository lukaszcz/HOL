(* Copyright (c) 2026 The HOL4 contributors. *)

(* Compact checked word programs share the existing SAT certificate cache.
   Full source admission precedes every lookup. A program's size never
   replaces the source metric or the original producer's resource checks. *)
structure SmtReplayWordProgram :> SmtReplayWordProgram =
struct
open HolKernel;
exception Declined;
val ERR=Feedback.mk_HOL_ERR "SmtReplayWordProgram";
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
 (* Bound cardinalities before numeric-Type decoding can exponentiate a
    small function Type. Saturation selects only this optional cache;
    compound dimensions with cardinality <=32 keep their existing route. *)
 fun bounded_width dim =
   let
    fun cap n=Int.min (33,n)
    fun power base exponent =
      if base=1 then 1 else if exponent>5 then 33 else
      let fun loop 0 value=value
            | loop n value=if value=33 then 33
              else loop (n-1) (cap (value*base))
      in loop exponent 1 end
    fun visit ty=if Type.is_vartype ty then raise Declined else
      case Type.dest_type ty of
          ("one",[])=>1
        | ("bit0",[arg])=>cap (2*visit arg)
        | ("bit1",[arg])=>cap (2*visit arg+1)
        | ("sum",[left,right])=>cap (visit left+visit right)
        | ("prod",[left,right])=>cap (visit left*visit right)
        | ("fun",[domain,range])=>power (visit range) (visit domain)
        | ("cart",[element,index])=>power (visit element) (visit index)
        | _=>raise Declined
   in visit dim end
 fun small_word ty = if not (wordsSyntax.is_word_type ty) then () else
   let val width=bounded_width (wordsSyntax.dest_word_type ty)
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
       val chosen=Term.is_comb t andalso
         Redblackmap.find (!counts,id t)>1 andalso
         (ty=Type.bool orelse wordsSyntax.is_word_type ty)
       val result=if not chosen then body else
         let val index=length (!aliases)
             val _=index<5000 orelse raise Declined
             val variable=hole (4000+index) ty
             val _=aliases:=(variable,t):: !aliases
             val _=definitions:=boolSyntax.mk_eq (variable,body):: !definitions
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

fun prepare_source context target =
 let
  val _= #refresh_caches (context:SmtSkeletonProve.sat_context) ()
  val _=Term.type_of target=Type.bool orelse
    raise SmtSkeletonProve.ERR "propositional_prove"
      "target is not Boolean"
  val graph=SmtSkeletonProve.phase "skeleton/propositional-cnf"
    (SmtSkeletonProve.build_cnf_graph_mode true) target
  val SmtSkeletonProve.GraphNode {kind,equality,...}= #root graph
  fun native () =
    let val actual=case kind of SmtSkeletonProve.GraphTrue=>boolTheory.TRUTH
          | _=> #theorem (SmtSkeletonProve.phase "skeleton/propositional-sat"
              (SmtSkeletonProve.checked_graph_sat_prove_in
                context (#entries graph)) (#root graph))
        val _=List.null (Thm.hyp actual) orelse
          raise SmtSkeletonProve.ERR "propositional_prove"
            "SAT theorem has hypotheses"
        val result=SmtSkeletonProve.exact_conclusion target
          (Thm.EQ_MP (Thm.SYM equality) actual)
        val _=Library.check_oracle_tags "SmtSkeletonProve"
          "propositional-replay" result
    in result end
 in native end;
fun prove_in (owner:SmtSkeletonProve.sat_context) hole source admit =
let
 val make=admit ()
 val actual=ref NONE
 fun original ()=case !actual of SOME theorem=>theorem
   | NONE=>let val theorem=make ()
           in actual:=SOME theorem;theorem end
 fun work () =
  let
   val _= #refresh_caches owner ()
   val prepared=prepare_program hole source
   val {key,context,result,aliases,inputs,memo,cost,dag,id}=prepared
   val _=dag>256 orelse raise Declined
   val _=not (List.exists (fn substitution=>
       List.exists (fn (variable,_)=>
         Term.term_eq (#redex substitution) variable) aliases) inputs)
       orelse raise Declined
   val capture=SmtSkeletonProve.cache_signature ()
   val generic=SmtSkeletonProve.cached_sat_proof owner key cost
     (fn () =>let
       val _=cost<=8192 orelse raise Declined
       val theorem=original ()
       val _=List.null (Thm.hyp theorem) orelse
         raise ERR "prove_in" "original proof has hypotheses"
       val _=Library.check_oracle_tags
         "SmtReplayWordProgram" "original" theorem
       val theorem=SmtSkeletonProve.exact_conclusion source theorem
       val _=SmtSkeletonProve.cache_signature_matches capture
         orelse raise Declined
       val definitions=Vector.fromList
         (Drule.CONJUNCTS (Thm.ASSUME context))
       val alias_map=List.foldl (fn ((i,(_,term)),table)=>
         Redblackmap.insert (table,id term,i))
         (Redblackmap.mkDict Int.compare)
         (ListPair.zip (List.tabulate (length aliases,fn i=>i),aliases))
       val cache=Array.array (257,[]:(term*thm) list)
       val used=ref 0
       fun convert term =
        let val bucket=SmtReplayImport.pointer_bucket 2 257 term
            val previous=Array.sub (cache,bucket)
        in case List.find (fn (old,_)=>Portable.pointer_eq (old,term))
               previous of SOME (_,proof)=>proof
         | NONE=>let
           val _= !used<8192 orelse raise Declined
           val _=used:= !used+1
           val proof=if Term.is_comb term then
               Thm.TRANS (Thm.REFL term)
                 (Thm.MK_COMB (convert (Term.rator term),
                   convert (Term.rand term)))
             else Thm.REFL term
           val proof=case Redblackmap.peek (alias_map,id term) of
               NONE=>proof
             | SOME index=>Thm.TRANS proof
                 (Thm.SYM (Vector.sub (definitions,index)))
           val proof=Thm.TRANS proof
             (Thm.REFL (Redblackmap.find (memo,id term)))
           val _=Array.update
             (cache,bucket,(term,proof)::Array.sub (cache,bucket))
         in proof end
        end
       val conversion=convert source
       val compact=Thm.DISCH context (Thm.EQ_MP conversion theorem)
       val compact=SmtSkeletonProve.exact_conclusion key
         (Thm.INST inputs compact)
       val _=List.null (Thm.hyp compact) orelse
         raise ERR "prove_in" "compact proof has hypotheses"
       val _=Library.check_oracle_tags "SmtReplayWordProgram" "compact" compact
       val _=SmtSkeletonProve.cache_signature_matches capture
         orelse raise Declined
      in compact end)
  in case !actual of SOME theorem=>theorem
    | NONE=>let
        val substitution=List.map (fn {redex,residue}=>residue |-> redex)
          inputs @ List.map (fn (variable,term)=>variable |-> term) aliases
        val instantiated=Thm.INST substitution generic
        val definitions=SmtCircuitSat.balanced_conjunction
          (List.map (Thm.REFL o #2) aliases)
        val result=Thm.MP instantiated definitions
      in SmtSkeletonProve.exact_conclusion source result end
  end
in work () handle Declined=>original () end;
end;
