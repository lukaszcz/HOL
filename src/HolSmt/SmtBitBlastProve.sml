(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtBitBlastProve :> SmtBitBlastProve =
struct
open HolKernel;
exception Terminal of exn;
fun protect worker input = worker input
  handle error as Feedback.HOL_ERR detail =>
    if SmtResource.is_resource_gate detail then raise Terminal error
    else raise error;
type context = {convert:Conv.conv,atomic:Conv.conv,boolean:Conv.conv,
  prove:Conv.conv,
  stats:unit -> {hits:int,misses:int,evictions:int,retained_dag_nodes:int}};
fun build bit_override prover_override : context =
 let
datatype result = Taut of thm | NotTaut | Unknown;
fun boolean_eligible source =
 let
  fun boolean term =
    if Term.is_var term then Term.type_of term=Type.bool
    else if Term.term_eq term boolSyntax.T orelse
      Term.term_eq term boolSyntax.F then true
    else if boolSyntax.is_neg term then boolean (boolSyntax.dest_neg term)
    else if boolSyntax.is_cond term then
      let val (a,b,c)=boolSyntax.dest_cond term
      in boolean a andalso boolean b andalso boolean c end
    else
      let val pair=if boolSyntax.is_conj term then
              SOME (boolSyntax.dest_conj term)
            else if boolSyntax.is_disj term then
              SOME (boolSyntax.dest_disj term)
            else if boolSyntax.is_imp term then
              SOME (boolSyntax.dest_imp term)
            else if boolSyntax.is_eq term then
              SOME (boolSyntax.dest_eq term) else NONE
      in case pair of NONE=>false | SOME (a,b)=>
           boolean a andalso boolean b end
 in SmtResource.term_nodes_up_to 8193 source<=8192 andalso boolean source end;
fun prove source =
 if not (boolean_eligible source) then Unknown else
 let
  val (_,_,lfn,clauses)=def_cnf.to_cnf false (boolSyntax.mk_neg source)
  val inventory=Array.tabulate (Array.length clauses,
    fn i=> #1 (Array.sub (clauses,i)))
 in case SmtCnfProve.prove inventory of SmtCnfProve.Unknown=>Unknown
  | SmtCnfProve.Model _=>NotTaut
  | SmtCnfProve.Refuted proof=>
     let val used=Thm.hypset proof
         val needed=List.filter (fn (c,_)=>HOLset.member (used,c))
           (Array.foldr (op ::) [] clauses)
     in Taut (Thm.CCONTR source (dpll.undoCNF lfn needed proof)) end
 end handle def_cnf.to_cnf_unsat theorem=>
   Taut (Thm.CCONTR source (Drule.UNDISCH (Thm.NOT_ELIM theorem)));
fun with_fallback worker source =
 case prove source of
   Unknown=>worker source
 | Taut theorem=>theorem
 | NotTaut=>raise Feedback.mk_HOL_ERR "blastLib" "SAT_CONV" "";
val entries=ref ([] : ((int * int) * thm * int) list);
val retained=ref 0;
val cache_hits=ref 0;
val cache_misses=ref 0;
val cache_evictions=ref 0;
val signature_witness=ref (SmtSkeletonProve.cache_signature ());
val index=ref (SmtSkeletonProve.new_cache_index
 SmtResource.max_bv_replay_term_nodes);
fun refresh () =
 if SmtSkeletonProve.cache_signature_matches (!signature_witness) then () else
 (entries:=[];retained:=0;
  index:=SmtSkeletonProve.new_cache_index SmtResource.max_bv_replay_term_nodes;
  signature_witness:=SmtSkeletonProve.cache_signature ());
fun bit_eligible source =
 let
  fun small_type ty =
   let val left=ref 64
       fun walk ty=if !left=0 then false else
        (left:= !left-1;Type.is_vartype ty orelse
         List.all walk (#Args (Type.dest_thy_type ty)))
   in walk ty end
  fun inspect term=not (Term.is_abs term) andalso
    small_type (Term.type_of term) andalso
    List.all inspect (SmtResource.term_children term)
 in Option.isSome (SmtReplayImport.bounded_raw_size 8192 source) andalso
   inspect source end;
fun cached_conversion kind allowed worker source =
 if not allowed then worker source else
 let
  val _=refresh ()
  val key=Option.map (fn id=>(kind,id)) ((!index) source)
  fun find _ [] _=NONE
    | find wanted ((entry as (id,law,cost))::rest) prior =
      if wanted=id then
       (entries:=entry::List.revAppend (prior,rest);SOME law)
      else find wanted rest (entry::prior)
  val cached=case key of NONE=>NONE | SOME id=>find id (!entries) []
 in case cached of SOME theorem=>
    (cache_hits:= !cache_hits+1;
     SmtSkeletonProve.nodewise_exact_left source theorem)
  | NONE=>
    let
     val witness=SmtSkeletonProve.cache_signature ()
     val theorem=worker source
     val _=cache_misses:= !cache_misses+1
     val _=assert null (Thm.hyp theorem)
     val _=Library.check_oracle_tags "SmtBitBlastProve" "bit" theorem
     val theorem=SmtSkeletonProve.nodewise_exact_left source theorem
     val cost=SmtResource.dag_nodes_up_to 8193 (Thm.concl theorem)
     fun fit [] nodes=([],nodes)
       | fit ((entry as (_,_,old_cost))::rest) nodes =
         if nodes+cost<=8192 then (entry::rest,nodes)
         else (cache_evictions:= !cache_evictions+1;
               fit rest (nodes-old_cost))
     val _=refresh ()
     val _=case key of NONE=>() | SOME id=>
      if cost>8192 orelse
        not (SmtSkeletonProve.cache_signature_matches witness) then () else
       let val (older,nodes)=fit (List.rev (!entries)) (!retained)
       in entries:=(id,theorem,cost)::List.rev older;
          retained:=nodes+cost end
    in theorem end
 end;
fun exact_cached_bit allowed worker source =
  cached_conversion 0 allowed worker source;
exception NoIndex;
fun exact_rewrite laws source =
 let
  val node_index=SmtSkeletonProve.new_cache_index
    SmtResource.max_bv_replay_term_nodes
  fun id term=case node_index term of SOME value=>value
    | NONE=>raise NoIndex
  val lookup=List.foldl (fn (theorem,table)=>Redblackmap.insert
    (table,id (boolSyntax.lhs (Thm.concl theorem)),theorem))
    (Redblackmap.mkDict Int.compare) laws
  val memo=ref (Redblackmap.mkDict Int.compare)
  fun visit term =
   if Term.is_abs term then raise NoIndex else
   let val key=id term in
    case Redblackmap.peek (!memo,key) of SOME result=>result
    | NONE=>let
       val result=case Redblackmap.peek (lookup,key) of
          SOME theorem=>SmtSkeletonProve.nodewise_exact_left term theorem
        | NONE=>if Term.is_comb term then
            Thm.MK_COMB (visit (Term.rator term),visit (Term.rand term))
          else if Term.is_abs term then
            let val (variable,body)=Term.dest_abs term
            in Thm.ABS variable (visit body) end
          else Thm.REFL term
       val _=memo:=Redblackmap.insert (!memo,key,result)
      in result end
   end
 in visit source end
 handle NoIndex=>Conv.QCONV (Rewrite.ONCE_REWRITE_CONV laws) source;


 fun convert_with boolean source =
  let
   val complete=ref true
   fun bit worker inputs = List.mapPartial
    (fn input =>
      let val allowed=bit_eligible input
          val _=if allowed then () else complete:=false
      in SOME (exact_cached_bit allowed (bit_override worker) input) end
      handle error => if SmtResource.terminal_diagnostic_exception error
        then raise Terminal error
        else (complete:=false;NONE)) inputs
   fun rewrite laws input =
    if !complete then protect (exact_rewrite laws) input
    else protect (Conv.QCONV (Rewrite.ONCE_REWRITE_CONV laws)) input
  in blastLib.BBLAST_CONV_WITH_STAGES
    {word_simp=Lib.I,bit_blast=bit,rewrite=rewrite,
     prover=fn worker=>if boolean then
       protect (prover_override (with_fallback worker))
       else fn _=>raise Conv.UNCHANGED}
    source
  end handle Terminal error=>raise error
 val convert=convert_with true
 in {prove=blastLib.BBLAST_PROVE_WITH_CONVERSION convert,
     convert=convert,atomic=(fn source=>cached_conversion 1
       (bit_eligible source) (convert_with false) source),
     boolean=with_fallback SmtSkeletonProve.checked_sat_prove,stats=fn ()=>
       {hits= !cache_hits,misses= !cache_misses,evictions= !cache_evictions,
        retained_dag_nodes= !retained}} end;
fun new_context () = build Lib.I Lib.I;
fun new_context_with_bit_conversion bit = build bit Lib.I;
fun new_context_with_for_test {bit,boolean} = build bit boolean;
fun convert (context:context) = #convert context;
fun convert_atomic (context:context) = #atomic context;
fun prove_boolean (context:context) = #boolean context;
fun prove (context:context) = #prove context;
fun stats_for_test (context:context) = #stats context ();
end;
