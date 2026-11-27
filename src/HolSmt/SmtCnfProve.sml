(* Copyright (c) 2026 The HOL4 contributors. *)

(* Optional bounded native search for an already-clausified Boolean problem.
   Proofs use the original clauses as assumptions. A model is certified by a
   native existential theorem over fresh Boolean proxies, after checking the
   complete typed source/alias roundtrip for each clause. *)
structure SmtCnfProve :> SmtCnfProve =
struct
open HolKernel;
datatype result = Refuted of thm | Model of thm | Unknown;
exception Decline;
exception Satisfiable of thm;
fun decline _ = raise Decline;
datatype plan = Conflict of int | Force of int * int * plan
              | Split of int * plan * plan;
val clause_limit = 2048;
fun refute source_clauses =
 let
  val variables=ref (Redblackmap.mkDict Term.compare)
  val reverse=ref (Redblackmap.mkDict Int.compare)
  val known_atoms=Array.array (257,NONE)
  val atom_bucket=SmtReplayImport.pointer_bucket 2 (Array.length known_atoms)
  fun primitive term =
   let val remaining=ref 64
       fun small ty=if !remaining=0 then false else
         (remaining:= !remaining-1;Type.is_vartype ty orelse
          List.all small (#Args (Type.dest_thy_type ty)))
       fun visit term=not (Term.is_abs term) andalso
         small (Term.type_of term) andalso
         List.all visit (SmtResource.term_children term)
   in SmtResource.term_nodes_up_to 65 term<=64 andalso visit term end
  fun intern term = case Redblackmap.peek (!variables,term) of
    SOME id=>id
   | NONE=>let val id=Redblackmap.numItems (!variables)+1
               val _=if id<=512 then () else decline "variables"
               val _=variables:=Redblackmap.insert (!variables,term,id)
               val _=reverse:=Redblackmap.insert (!reverse,id,term)
           in id end
  (* A Boolean variable meets the atom bounds by construction. For other
     atoms, reuse admission only on a physical match in the hinted slot. *)
  fun variable term =
   if Term.is_var term andalso Type.compare (Term.type_of term,Type.bool)=EQUAL
   then intern term
   else
    let val bucket=atom_bucket term
        fun admit () =
         if not (primitive term) then decline "opaque-atom"
         else let val id=intern term
         in Array.update (known_atoms,bucket,SOME (term,id)); id end
    in case Array.sub (known_atoms,bucket) of
         SOME (saved,id)=>if Portable.pointer_eq (saved,term) then id
                          else admit ()
       | NONE=>admit ()
    end
  fun signed_id id term = if boolSyntax.is_neg term then
    ~(id (boolSyntax.dest_neg term)) else id term
  val literal_count=ref 0
  val clauses=Array.tabulate (Vector.length source_clauses,fn i=>
    let
      val clause=Vector.sub (source_clauses,i)
      val _=if SmtResource.term_nodes_up_to 8193 clause<=8192 then ()
        else decline "clause-size"
      val literals=if Term.term_eq clause boolSyntax.F then []
        else boolSyntax.strip_disj clause
      val _=literal_count:= !literal_count+length literals
      val _=if !literal_count<=8192 then () else decline "literals"
    in List.map (signed_id variable) literals end)
  val true_id=variable boolSyntax.T
  val false_id=variable boolSyntax.F
  val work=ref 0
  fun tick ()=if !work>=200000 then decline "work" else work:= !work+1
  fun sign n=if n<0 then ~1 else 1
  val nvars=Redblackmap.numItems (!variables)+1
  val values=Array.array (nvars,0)
  val remaining=Array.tabulate (Array.length clauses,
    fn i=>length (Array.sub (clauses,i)))
  val satisfied=Array.array (Array.length clauses,0)
  val occurrences=Array.array (nvars,[] : (int * int) list)
  val _=Array.appi (fn (i,lits)=>List.app (fn lit=>
    let val n=Int.abs lit
    in Array.update (occurrences,n,(i,sign lit)::
      Array.sub (occurrences,n)) end) lits) clauses
  val trail=ref ([] : (int * int * int) list)
  val trail_size=ref 0
  fun change tag array i v =
   (trail:=(tag,i,Array.sub (array,i)):: !trail;
    trail_size:= !trail_size+1;Array.update (array,i,v))
  fun restore base = if !trail_size=base then () else
   case !trail of []=>raise Fail "integer DPLL trail"
    | (tag,i,old)::rest=>
       (Array.update (if tag=0 then values
                      else if tag=1 then remaining else satisfied,i,old);
        trail:=rest;trail_size:= !trail_size-1;restore base)
  fun assign lit =
   let
    val n=Int.abs lit and value=sign lit
    val _=if Array.sub (values,n)=0 then ()
      else raise Fail "integer DPLL double assignment"
    val _=change 0 values n value
    val queue=ref []
    val _=List.app (fn (i,polarity)=>
      (tick ();
       change 1 remaining i (Array.sub (remaining,i)-1);
       if polarity=value then
         change 2 satisfied i (Array.sub (satisfied,i)+1) else ();
       if Array.sub (satisfied,i)=0 andalso Array.sub (remaining,i)<=1
       then queue:=i:: !queue else ())) (Array.sub (occurrences,n))
   in !queue end
  val plan_nodes=ref 0
  fun checked_model () =
   let
    (* T and F are assigned before search. The remaining budget counts only
       assigned variables, before constructing any fresh proxy terms. *)
    val assignment_count=Array.foldl (fn (value,n)=>
      if value=0 then n else n+1) 0 values
    val _=Vector.foldl (fn (clause,budget)=>
      let val cost=SmtResource.term_nodes_up_to (Int.min (4097,budget)) clause
      in if cost<=budget then budget-cost else decline "model-witness" end)
      (200000 div assignment_count) source_clauses
    val atoms=Redblackmap.listItems (!reverse)
    val avoid=ref (List.concat (List.map (Term.free_vars o #2) atoms))
    fun fresh (n,atom) =
      let val v=Term.variant (!avoid) (Term.genvar Type.bool)
          val _=avoid:=v:: !avoid
      in (n,atom,v) end
    val bindings=List.map fresh atoms
    val proxies=List.foldl (fn ((n,_,v),table)=>
      Redblackmap.insert (table,n,v))
      (Redblackmap.mkDict Int.compare) bindings
    fun placeholder atom=Redblackmap.find
      (proxies,Redblackmap.find (!variables,atom))
    (* Only disjunctions are clause structure. The body of a negative
       literal stays one atom, even when its source contains connectives. *)
    fun encode term=if boolSyntax.is_disj term then
      let val (a,b)=boolSyntax.dest_disj term
      in boolSyntax.mk_disj (encode a,encode b) end
      else if boolSyntax.is_neg term then
        boolSyntax.mk_neg (placeholder (boolSyntax.dest_neg term))
      else placeholder term
    val inverse=List.map (fn (_,atom,v)=>v |-> atom) bindings
    val assignments=List.mapPartial (fn (n,_,v)=>
      if Array.sub (values,n)=0 then NONE else SOME
       (v |-> (if Array.sub (values,n)= ~1 then boolSyntax.F
               else boolSyntax.T))) bindings
    val decode=Term.subst inverse
    val assign_values=Term.subst assignments
    fun check clause =
     let
      (* Every clause has at most the native guarded atom size. Check the
         complete typed alias-preserving proxy map before evaluating it. *)
      val schema=encode clause
      val original=decode schema
      val _=if Term.aconv clause original then ()
        else raise Fail "native SAT model source roundtrip"
      val instance=assign_values schema
      val law=Drule.EQT_ELIM (Conv.QCONV (Rewrite.REWRITE_CONV []) instance)
      val _=if null (Thm.hyp law) andalso Term.aconv (Thm.concl law) instance
        then () else raise Fail "native SAT model validation"
      val _=Library.check_oracle_tags "SmtCnfProve" "model" law
     in (schema,law) end
    val checked = Array.fromList (Vector.foldr
      (fn (clause,rest) => check clause :: rest) [] source_clauses)
    val schema = minisatResolve.balanced_array boolSyntax.T fst
      boolSyntax.mk_conj checked
    val variables=List.map #redex assignments
    val quantified=boolSyntax.list_mk_exists (variables,schema)
    fun steps target []=[]
      | steps target ({redex,residue}::rest)=
        let val (_,body)=boolSyntax.dest_exists target
        in (target,residue)::
          steps (Term.subst [redex |-> residue] body) rest end
    val witness=List.foldr (fn ((target,choice),law)=>
      Thm.EXISTS (target,choice) law)
      (minisatResolve.balanced_clause_proof checked)
      (steps quantified assignments)
    val _=if null (Thm.hyp witness) andalso
      Term.aconv (Thm.concl witness) quantified then ()
      else raise Fail "native SAT existential model endpoint"
    val _=Library.check_oracle_tags "SmtCnfProve" "witness" witness
   in raise Satisfiable witness end
  fun proof_node () = if !plan_nodes>=8192 then decline "plan-nodes"
    else plan_nodes:= !plan_nodes+1
  fun search queue =
   case queue of i::rest=>
     if Array.sub (satisfied,i)>0 orelse Array.sub (remaining,i)>1 then
       search rest
     else if Array.sub (remaining,i)=0 then (proof_node ();Conflict i)
     else let
       val lit=valOf (List.find (fn lit=>
         Array.sub (values,Int.abs lit)=0) (Array.sub (clauses,i)))
       val _=proof_node ()
       val added=assign lit
      in Force (lit,i,search (added @ rest)) end
    | []=>
     let
      val votes=Array.array (nvars,0)
      val unresolved=ref false
      val _=Array.appi (fn (i,lits)=>
       if Array.sub (satisfied,i)>0 then () else
        (unresolved:=true;List.app (fn lit=>
          (tick ();let val n=Int.abs lit
           in if Array.sub (values,n)=0 then
             Array.update (votes,n,Array.sub (votes,n)+1) else () end))
          lits)) clauses
      val _=if !unresolved then () else checked_model ()
      val (best,_)=Array.foldli (fn (i,n,(old,score))=>
        if n>score then (i,n) else (old,score)) (0,0) votes
      val _=if best>0 then () else raise Fail "integer DPLL split"
      val _=proof_node ()
      val base= !trail_size
      val left=search (assign best)
      val _=restore base
      val right=search (assign (~best))
      val _=restore base
     in Split (best,left,right) end
  val initial=Array.foldri (fn (i,lits,queue)=>
    if length lits<=1 then i::queue else queue) [] clauses
  val plan=search (assign true_id @ assign (~false_id) @ initial)
  fun term lit=let val atom=Redblackmap.find (!reverse,Int.abs lit)
               in if lit<0 then boolSyntax.mk_neg atom else atom end
  (* Replay visits only literals already admitted while compiling clauses. *)
  fun compiled_literal term =
    signed_id (fn atom => Redblackmap.find (!variables,atom)) term
  fun contradict env literal assumed =
   let val known=Redblackmap.find (env,~literal)
   in if literal<0 then Thm.MP (Thm.NOT_ELIM assumed) known
      else Thm.MP (Thm.NOT_ELIM known) assumed end
  fun derive env wanted theorem =
   let val clause=Thm.concl theorem
   in if Term.aconv clause wanted then theorem
      else if Term.term_eq clause boolSyntax.F then Drule.CONTR wanted theorem
      else if boolSyntax.is_disj clause then
        let val (left,right)=boolSyntax.dest_disj clause
        in Thm.DISJ_CASES theorem
          (derive env wanted (Thm.ASSUME left))
          (derive env wanted (Thm.ASSUME right)) end
      else Drule.CONTR wanted (contradict env (compiled_literal clause) theorem)
   end
  fun clause i=Thm.ASSUME (Vector.sub (source_clauses,i))
  fun replay env (Conflict i)=derive env boolSyntax.F (clause i)
    | replay env (Force (lit,i,rest))=
       let val theorem=derive env (term lit) (clause i)
       in replay (Redblackmap.insert (env,lit,theorem)) rest end
    | replay env (Split (lit,left,right))=
       let val positive=term lit
           val negative=term (~lit)
           val l=replay (Redblackmap.insert
             (env,lit,Thm.ASSUME positive)) left
           val r=replay (Redblackmap.insert
             (env,~lit,Thm.ASSUME negative)) right
       in Thm.DISJ_CASES (Thm.SPEC positive boolTheory.EXCLUDED_MIDDLE) l r end
  val initial_environment=Redblackmap.insert
    (Redblackmap.insert (Redblackmap.mkDict Int.compare,
       true_id,boolTheory.TRUTH),~false_id,
       Drule.EQF_ELIM (Thm.REFL boolSyntax.F))
  val contradiction=replay initial_environment plan
 in contradiction end;

fun prove_vector clauses = Refuted (refute clauses)
  handle Satisfiable witness => Model witness
       | Decline => Unknown;

fun prove clauses =
  if Array.length clauses > clause_limit then Unknown
  else prove_vector (Array.vector clauses);

fun prove_clauses clauses =
  let val count = Array.length clauses in
    if count > clause_limit then Unknown
    else prove_vector
      (Vector.tabulate (count, fn i => #1 (Array.sub (clauses,i))))
  end;

fun prove_conjunction (cnf,extra) =
  let
    (* Every pending subtree accounts for at least one clause. A split
       increases that lower bound by one, and a leaf leaves it unchanged. *)
    fun collect [] clauses _ =
          prove_vector (Vector.fromList (List.revAppend (clauses,extra)))
      | collect (term :: rest) clauses space =
          case Lib.total boolSyntax.dest_conj term of
              NONE => collect rest (term :: clauses) space
            | SOME (left,right) =>
                if space = 0 then Unknown
                else collect (left :: right :: rest) clauses (space-1)
    val space = clause_limit - List.length extra - 1
  in if space < 0 then Unknown else collect [cnf] [] space end;
end;
