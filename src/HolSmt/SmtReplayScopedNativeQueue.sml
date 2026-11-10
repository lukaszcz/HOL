structure SmtReplayScopedNativeQueue :> SmtReplayScopedNativeQueue =
struct
  structure N=SmtReplayNamedContext
  val ERR=Feedback.mk_HOL_ERR "SmtReplayScopedNativeQueue"
  datatype phase=Building | Sealed | Checked | Running | Complete | Closed
  datatype proof=Proof of {owner:unit ref,guard:unit -> unit,index:int,
    conclusion:Term.term,hypotheses:Term.term list,native:unit -> Thm.thm}
  (* Private, fixed actual circuit workers. No arbitrary native callback
     or caller theorem may enter this instruction inventory. *)
  datatype circuit = CircuitTruth
    | DefinitionCNF of Term.term
    | ProveCNF of Term.term * Term.term
  datatype instruction=
      Seed of int * Term.term
    | Circuit of circuit * Term.term
    | Recorded of (unit -> Thm.thm) * Term.term * Term.term list
    | Fixed of Term.term N.primitive * int list * Term.term * Term.term list
    | Boolean of Term.term N.boolean_rule * int list *
        Term.term * Term.term list
  datatype queue=Queue of
    {owner:unit ref,admission:N.admission,fixed:N.fixed_admission,
     epoch:int,symbols:int,phase:phase ref,
     profile:Term.term -> N.profile,
     types:Type.hol_type list ref,seen:Term.term list ref,
     next:int ref,commands:(int * instruction) list ref,
     results:(int,Thm.thm) Redblackmap.dict ref}
  fun held(Proof data)=data
  fun same_name term=term
  fun conclusion(Proof{guard,conclusion,...})=(guard ();conclusion)
  fun hypotheses(Proof{guard,hypotheses,...})=(guard ();hypotheses)
  (* Existing checked theorem metadata, never an oracle or inference. *)
  val clean_forecast_tag=Thm.tag boolTheory.TRUTH
  fun forecast_tag(Proof{guard,...})=(guard ();clean_forecast_tag)
  fun fixed_arity_error ()=ERR "execute" "fixed arity changed"
  fun boolean_arity_error ()=ERR "execute" "Boolean arity changed"
  fun guard(Queue{admission,epoch,symbols,phase,...})=
    ((#guard admission) ();
     (#pay admission) 8;
     if !phase=Closed then raise ERR "guard" "queue closed"else ();
     if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols
       then ()else raise ERR "guard" "declaration lifetime changed")
  fun pay queue amount=
    let val Queue{admission,...}=queue
    in guard queue;(#pay admission) amount end
  fun building(queue as Queue{phase,...})=
    (guard queue;pay queue 2;
     if !phase=Building then ()else
       raise ERR "prepare" "metadata programme already sealed")
  fun create(admission:N.admission)=
    let
      val spend= #pay admission
      val _= #guard admission ()
      (* Fourteen retained fields+constructor, seven refs, two stamps,
         two helper closures, dictionary comparator and fixed record. *)
      val _=spend 34
      fun compare(a,b)=(#guard admission ();spend 1;Int.compare(a,b))
      val inspect=N.inspector admission
      val fixed:N.fixed_admission=
        {pay=spend,guard= #guard admission,
         template_limit= #template_limit admission,
         type_work_limit= #type_work_limit admission,
         error= #error admission}
    in Queue{owner=ref (),admission=admission,fixed=fixed,
      epoch=Type.type_epoch (),symbols=Term.term_epoch (),
      phase=ref Building,profile= #profile inspect,
      types=ref [],seen=ref [],next=ref 0,commands=ref [],
      results=ref(Redblackmap.mkDict compare)}end
  fun profile(queue as Queue{profile=inspect,types,seen,...}) term=
    let
      val _=guard queue
      (* Actual native geometry admission precedes the additional Type
         inventory walk; no raw body or theorem effect is performed. *)
      val value=inspect term
      val _=pay queue 2
      fun member _ []=false
        | member term (old::rest)=
            (pay queue 1;Portable.pointer_eq(term,old)orelse
              member term rest)
      fun visit current=
        (pay queue 1;if member current (!seen)then ()else
          let val _=pay queue 5 val ty=Term.type_of current
              val _=seen:=current:: !seen
              val _=types:=ty:: !types
          in if Term.is_comb current then
              let val _=pay queue 3 val(f,x)=Term.dest_comb current
              in visit f;visit x end
            else if Term.is_abs current then
              raise ERR "profile" "unexpected compact binder"else ()end)
      val _=visit term
    in value end
  val compact_profile=profile
  fun weight(p:N.profile)= #raw p+ #inc p+ #ann p
  fun spelling queue root=
    let
      val _=pay queue 1
      fun visit term=
        (pay queue 1;if Term.is_var term then
            let val _=pay queue 1 val(name,_)=Term.dest_var term
            in IntInf.fromInt(String.size name)end
          else if Term.is_const term then
            let val _=pay queue 1 val row=Term.dest_thy_const term
            in IntInf.fromInt(String.size(#Thy row))+
              IntInf.fromInt(String.size(#Name row))end
          else if Term.is_comb term then
            let val _=pay queue 3 val(f,x)=Term.dest_comb term
            in visit f+visit x end
          else raise ERR "spelling" "unexpected compact binder")
    in visit root end
  fun compare_terms queue(a,b)=
    let val p=profile queue a val q=profile queue b
        val bytes=spelling queue a+spelling queue b
        val _=pay queue(1+weight p+weight q+bytes)
    in Term.compare(a,b)end
  fun same_term queue pair=compare_terms queue pair=EQUAL
  fun validate_proof(queue as Queue{owner,...})(proof as Proof data)=
    (guard queue;pay queue 2;
     if Portable.pointer_eq(owner,#owner data)then ()else
       raise ERR "proof" "different native queue";
     (#guard data) ();proof)
  fun copy queue action []=(guard queue;[])
    | copy queue action(x::rest)=
        (pay queue 2;action x::copy queue action rest)
  fun union queue rows=
    let
      val _=pay queue 2
      fun add term []=(pay queue 1;[term])
        | add term (old::rest)=
            (pay queue 1;case compare_terms queue(term,old)of
                LESS=>(pay queue 1;term::old::rest)
              | EQUAL=>old::rest
              | GREATER=>(pay queue 1;old::add term rest))
      fun visit [] result=(guard queue;result)
        | visit(x::rest)result=(pay queue 1;visit rest(add x result))
    in visit rows []end
  fun type_equal queue a b=
    let val Queue{admission,...}=queue
        val ceiling=IntInf.fromInt(#type_work_limit admission)
        val _=pay queue 2
        val x=N.type_weight_using (pay queue)(#error admission)ceiling a
        val y=N.type_weight_using (pay queue)(#error admission)ceiling b
        val _=pay queue(1+x+y)
    in Type.compare(a,b)=EQUAL end
  (* Shape walking is syntax, not a second fixed-rule registry. Its
     arithmetic describes precisely the supplied shared prepared shape. *)
  fun describe queue shape=
    let
      val Queue{admission,...}=queue
      val ceiling=IntInf.fromInt(#type_work_limit admission)
      (* Actual four captured callbacks. The observer prices this new
         caller's expression visits and result metadata; old N callers
         keep their independently checked static specialization. *)
      val _=pay queue 4
      fun own ty=N.type_weight_using(pay queue)(#error admission)ceiling ty
      fun observe(N.HeldSyntax _)=pay queue 4
        | observe _=pay queue 8
    in N.describe_shape observe(profile queue)own(type_equal queue)shape end
  fun materialize queue shape=
    let
      val Queue{admission,...}=queue
      val(p,_)=describe queue shape
      val cap=IntInf.fromInt(#template_limit admission)
      val ceiling=IntInf.fromInt(#type_work_limit admission)
      val _=if #raw p<=cap andalso #inc p<=cap andalso
          #ann p<=ceiling then ()else
        raise ERR "materialize" "forecast syntax exceeds native cap"
      (* This extra syntax construction is distinct from the already
         quoted future kernel result. Charge its actual geometry too. *)
      val _=pay queue(1+weight p)
      val _=pay queue 1
      val result=N.realize_shape(fn _=>pay queue 1)shape
      val _=ignore(profile queue result)
    in result end
  fun boolean_shape queue shape=
    let val _=pay queue 1
        fun observe(N.PBHeld _)=pay queue 3
          | observe N.PBFalse=pay queue 3
          | observe(N.PBNegation _)=pay queue 5
          | observe _=pay queue 7
    in N.boolean_syntax observe shape end
  fun publish(queue as Queue{owner,next,commands,phase,results,...})
      command term hyp=
    let val _=building queue
        (* Six proof fields+constructor, two retained closures, tuple,
           cons, two writes and scalar next/index reads. *)
        val _=pay queue 15 val id= !next
        val _=next:=id+1 val _=commands:=(id,command):: !commands
    in Proof{owner=owner,guard=fn()=>guard queue,index=id,
      conclusion=term,hypotheses=hyp,native=fn()=>
        (guard queue;pay queue 2;
         case !phase of Running=>Redblackmap.find(!results,id)
           | Complete=>Redblackmap.find(!results,id)
           | _=>raise ERR "native" "proof has not been emitted")}end
  fun seed queue slot term=
    let val _=building queue val _=ignore(profile queue term)
        val _=if slot>=0 andalso type_equal queue
            (Term.type_of term) Type.bool then ()else
          raise ERR "seed" "invalid constructor slot"
        val Queue{admission,...}=queue
        val _=pay queue 4
        val(lhs,rhs)=boolSyntax.dest_eq term
        fun named value=Term.is_var value andalso (#member admission)value
        val constructor=named lhs andalso
          (Term.is_const rhs orelse (Term.is_comb rhs andalso
            let val _=pay queue 3 val(f,x)=Term.dest_comb rhs
            in named f andalso named x end))
        val _=if constructor then ()else
          raise ERR "seed" "not an actual sparse constructor shape"
        val _=pay queue 4
    in publish queue(Seed(slot,term))term[term]end
  fun premise_ids queue proofs=
    (pay queue 1;
     copy queue(fn proof=> #index(held(validate_proof queue proof)))proofs)
  fun fixed queue recipe proofs=
    let val _=building queue
        val Queue{admission,fixed,...}=queue
        val ids=premise_ids queue proofs
        val _=pay queue 1
        val prepared=N.prepare_fixed_quoted (#pay admission)
          conclusion hypotheses fixed (profile queue) same_name
          recipe proofs
        (* The shared preparation has already checked arities and actual
           equation/implication syntax. These joins validate the exact
           intermediate operands before any kernel programme starts. *)
        val _=pay queue 2
        fun joins(a,b)=if same_term queue(a,b)then ()else
          raise ERR "fixed" "incompatible actual fixed operands"
        val _=case(recipe,proofs)of
            (N.Transitivity,[a,b])=>
              joins(#2(boolSyntax.dest_eq(conclusion a)),
                #1(boolSyntax.dest_eq(conclusion b)))
          | (N.EqualityMP,[a,b])=>
              joins(#1(boolSyntax.dest_eq(conclusion a)),conclusion b)
          | (N.ImplicationMP,[a,b])=>
              joins(#1(boolSyntax.dest_imp_only(conclusion a)),conclusion b)
          | _=>()
        val term=materialize queue(#shape prepared)
        val hyp=union queue(#hypotheses prepared)
        val _=pay queue 5
    in publish queue(Fixed(recipe,ids,term,
      #hypotheses prepared))term hyp end
  fun boolean queue opcode proofs=
    let val _=building queue
        val Queue{admission,fixed,...}=queue
        val ids=premise_ids queue proofs
        (* CCONTR's node argument is an authentic compact placeholder.
           Every seed Hyp is a constructor equation, so no hidden local
           negated assumption is introduced or silently dropped here. *)
        val _=case opcode of N.PolicyContradiction term=>
            if Term.is_var term andalso (#member admission)term andalso
                type_equal queue(Term.type_of term)Type.bool then ()else
              raise ERR "boolean" "contradiction target is not a name"
          | _=>()
        val _=pay queue 1
        val prepared=N.prepare_boolean_quoted (#pay admission)
          conclusion hypotheses fixed(profile queue)same_name
          opcode proofs
        val _=case(opcode,proofs)of
            (N.PolicyImplicationMP,[a,b])=>
              if same_term queue(#1(boolSyntax.dest_imp(conclusion a)),
                  conclusion b)then ()else
                raise ERR "boolean" "incompatible actual MP operands"
          | _=>()
        val shape=boolean_shape queue(#shape prepared)
        val term=materialize queue shape
        val hyp=union queue(#hypotheses prepared)
        val _=pay queue 5
    in publish queue(Boolean(opcode,ids,term,
      #hypotheses prepared))term hyp end
  (* These forecast constructors are private to the static instance
     below. The shared Boolean worker has already admitted its complete
     actual CNF/REFL/public-SAT portfolios before calling them. We price
     the additional forecast syntax work, not a second inference quote. *)
  fun circuit_truth queue=
    let val _=building queue val _=ignore(profile queue boolSyntax.T)
        val _=pay queue 4
    in publish queue(Circuit(CircuitTruth,boolSyntax.T))boolSyntax.T[]end
  fun circuit_definition queue definition=
    let
      val _=building queue val _=ignore(profile queue definition)
      val Queue{admission,...}=queue
      val cap=IntInf.fromInt(#template_limit admission)
      val ceiling=IntInf.fromInt(#type_work_limit admission)
      val _=pay queue 5
      fun schema_profile root=
        let
          val Queue{types,...}=queue
          val _=pay queue 1
          fun visit current=
            let val _=pay queue 3 val ty=Term.type_of current
                val _=pay queue 2
                val _=types:=ty:: !types
                val own=N.type_weight_using(#pay admission)
                  (#error admission)ceiling ty
                val p:N.profile=if Term.is_comb current then
                    let val _=pay queue 3 val(f,x)=Term.dest_comb current
                        val a=visit f val b=visit x
                    in {raw=1+ #raw a+ #raw b,
                      inc=1+ #inc a+ #inc b,
                      ann=own+ #ann a+ #ann b,ty=own}end
                  else if Term.is_var current orelse
                      Term.is_const current then
                    {raw=1,inc=1,ann=own,ty=own}
                  else raise ERR "circuit_definition" "binder schema"
                val _=if #raw p<=cap andalso #inc p<=cap andalso
                    #ann p<=ceiling then ()else
                  raise ERR "circuit_definition" "schema syntax cap"
            in p end
        in visit root end
      fun forecast(terms,types) law=
        let
          (* The actual selector and match are shared with the native
             worker. Its fixed Bool schemas have no Type substitution. *)
          val _=pay queue 4
          val _=if null types then ()else
            raise ERR "circuit_definition" "non-Boolean schema instance"
          val source=Thm.concl law
          val _=pay queue 2
          val p=schema_profile source
          (* Each substitution is an owned variable of the SAME Type;
             the shared selector/match produced it, not a caller map. *)
          val _=pay queue 1
          fun check []=guard queue
            | check({redex,residue}::rest)=
                (pay queue 3;
                 if Term.is_var redex andalso Term.is_var residue andalso
                     (#member admission)residue andalso
                     type_equal queue(Term.type_of redex)
                       (Term.type_of residue)then check rest else
                   raise ERR "circuit_definition" "invalid named hole")
          val _=check terms
          val _=pay queue(1+weight p)
          val output=Term.subst terms source
          val _=ignore(profile queue output)
          val _=pay queue 5
        in publish queue(Circuit(DefinitionCNF definition,output))
          output[]end
      fun spelling root=
        let val _=pay queue 1
            fun walk current=
              (pay queue 1;if Term.is_var current then
                  let val _=pay queue 1 val(text,_)=Term.dest_var current
                  in IntInf.fromInt(String.size text)end
                else if Term.is_const current then
                  let val _=pay queue 1 val row=Term.dest_thy_const current
                  in IntInf.fromInt(String.size(#Thy row))+
                    IntInf.fromInt(String.size(#Name row))end
                else if Term.is_comb current then
                  let val _=pay queue 3 val(f,x)=Term.dest_comb current
                  in walk f+walk x end
                else raise ERR "circuit_definition" "binder in gate")
        in walk root end
      fun selector actual=
        let val p=profile queue actual val bytes=spelling actual
            (* Eight stock recognizers inspect only this bounded gate;
               their constant/name/Type comparisons are actual metadata. *)
        in pay queue(8*(1+weight p+bytes))end
      fun matching law actual=
        let val _=pay queue 2 val source=Thm.concl law
            val a=schema_profile source val b=profile queue actual
            val left=spelling source val right=spelling actual
            (* Public matching traverses this selected fixed schema and
               the admitted named input, including repeated hole checks. *)
            val _=pay queue((1+ #raw a)*(1+weight b+left+right))
        in guard queue end
    in SmtCircuitSat.definition_cnf_observed selector matching forecast
      definition end
  fun circuit_prove queue(cnf,target)=
    let val _=building queue
        val _=ignore(profile queue cnf)
        val _=ignore(profile queue target)
        val _=if type_equal queue(Term.type_of cnf)Type.bool andalso
            type_equal queue(Term.type_of target)Type.bool then ()else
          raise ERR "circuit_prove" "non-Boolean SAT port"
        val _=pay queue 5
        val shape=N.boolean_syntax(fn _=>pay queue 3)
          (N.PBImplication(N.PBHeld cnf,N.PBHeld target))
        val output=materialize queue shape
        val _=pay queue 5
    in publish queue(Circuit(ProveCNF(cnf,target),output))output[]end
  structure CircuitNative =
  struct
    type context=queue option
    type proof=proof
    val default_context=NONE
    val concl=conclusion
    val hyp=hypotheses
    val tag=forecast_tag
    fun actual(SOME value)=value
      | actual NONE=raise ERR "circuit" "missing forecast queue"
    fun truth context=circuit_truth(actual context)
    fun definition_cnf context=circuit_definition(actual context)
    fun refl context term=fixed(actual context)(N.ReflexiveName term)[]
    fun balanced_equivalences context proofs=
      let val queue=actual context
          val _=pay queue 2
      in SmtCircuitSat.balanced_equivalences_using
        (fn term=>fixed queue(N.ReflexiveName term)[])
        (fn(a,b)=>fixed queue N.Congruence[a,b])proofs end
    fun prove_cnf context=circuit_prove(actual context)
  end
  structure Boolean=SmtReplayNamedBooleanFn(CircuitNative)
  type 'node boolean_operations =
    {native:SmtReplayNativeContract.limits,
     type_weight:Type.hol_type -> IntInf.int,
     type_of:'node -> Type.hol_type,view:'node -> 'node N.view,
     constant:'node -> Term.term,same:'node * 'node -> bool,
     name:'node -> Term.term,constructor:'node -> proof,
     error:string -> exn}
  fun assemble_boolean queue
      (operations:'node boolean_operations) input=
    let
      val _=building queue
      (* Eighteen fields+record, four local adapters, ten captured
         partial/read closures and SOME are new scoped-call metadata. *)
      val _=pay queue 34
      fun view node=case (#view operations)node of
          N.Atom=>Boolean.Atom | N.Constant _=>Boolean.Constant
        | N.Application pair=>Boolean.Application pair
      fun checked proof=validate_proof queue proof
      fun closed proof=
        let val _=ignore(checked proof)val _=pay queue 1
        in if null(hypotheses proof)then proof else
          raise ERR "assemble_boolean" "open circuit result"end
      fun constructor node=checked((#constructor operations)node)
      val actual:('node,proof)Boolean.operations=
        {native= #native operations,
         spend=fn n=>pay queue(IntInf.fromInt n),pay=pay queue,
         guard=fn()=>guard queue,profile=profile queue,
         type_weight= #type_weight operations,type_of= #type_of operations,
         view=view,constant= #constant operations,same= #same operations,
         name= #name operations,theorem=checked,constructor=constructor,
         closed=closed,equality_mp=fixed queue N.EqualityMP,
         conjunction=boolean queue N.PolicyConjunction,
         implication_mp=boolean queue N.PolicyImplicationMP,
         error= #error operations}
    in Boolean.assemble_with_context(SOME queue)actual input end
  structure Equality=SmtReplayNamedEqualityFn
    (struct type proof=proof val concl=conclusion end)
  type 'node equality_operations =
    {key:'node -> int,same:'node * 'node -> bool,
     name:'node -> Term.term,equality:'node -> ('node * 'node) option,
     application:'node -> ('node * 'node) option,
     constructor:'node -> proof,definition:'node -> proof,
     error:string -> exn}
  fun assemble_equality queue
      (operations:'node equality_operations) input=
    let
      val _=building queue
      (* Nineteen fields+record, seven captured adapters and twelve
         partial applications. No operation grants a Source. *)
      val _=pay queue 39
      fun checked value=validate_proof queue value
      fun constructor node=checked((#constructor operations)node)
      fun definition node=checked((#definition operations)node)
      val actual:('node,proof)Equality.operations=
        {guard=fn()=>guard queue,tick=fn()=>pay queue 1,
         key= #key operations,
         compare_keys=fn(a,b)=>(pay queue 1;Int.compare(a,b)),
         same= #same operations,name= #name operations,
         equality= #equality operations,application= #application operations,
         theorem=checked,constructor=constructor,definition=definition,
         reflexive=fn node=>fixed queue
           (N.ReflexiveName((#name operations)node))[],
         symmetry=fixed queue N.Symmetry,
         transitivity=fixed queue N.Transitivity,
         congruence=fixed queue N.Congruence,
         equality_mp=fixed queue N.EqualityMP,
         conjunction=boolean queue N.PolicyConjunction,
         conjunct_left=boolean queue N.PolicyConjunctLeft,
         error= #error operations}
    in Equality.assemble actual input end
  structure Clause=SmtReplayNamedClauseFn
    (struct
       type input=proof
       val concl=conclusion
       val hyp=hypotheses
       val tag=forecast_tag
       fun read(Proof data)=(#native data)()
     end)
  type ('node,'tree) recorded_operations =
    {metadata_template:SmtReplayResourcePolicy.limit,
     tree_view:'tree -> ('node,'tree) SmtReplayNamedClause.tree_view,
     node_view:'node -> ('node * 'node) option,
     constant_node:'node -> bool,same_node:'node * 'node -> bool,
     named:'node -> Term.term,constant:Term.term -> 'node -> bool,
     constant_term:'node -> Term.term,
     operator:Term.term -> int -> 'node -> 'node list,
     definition:'node -> proof,error:string -> exn}
  fun recorded queue (operations:('node,'tree) recorded_operations)
      {premises,target,target_expanded,fallbacks}=
    let
      val _=building queue
      val Queue{admission,commands,types,...}=queue
      val _=pay queue 34
      fun hypothesis term=
        let val _=pay queue 1
            fun visit []=false
              | visit((_,Seed(_,held))::rest)=
                  (pay queue 1;Portable.pointer_eq(term,held)orelse
                    visit rest)
              | visit(_::rest)=(pay queue 1;visit rest)
        in visit(!commands)end
      fun tree_view tree=
        (pay queue 1;case (#tree_view operations)tree of
            SmtReplayNamedClause.ClauseFalse node=>Clause.ClauseFalse node
          | SmtReplayNamedClause.ClauseLiteral row=>Clause.ClauseLiteral row
          | SmtReplayNamedClause.ClauseOr row=>Clause.ClauseOr row)
      fun node_view node=(pay queue 1;
        case (#node_view operations)node of SOME pair=>
            Clause.NodeApplication pair
          | NONE=>if (#constant_node operations)node then
              Clause.NodeConstant else Clause.NodeAtom)
      fun definition node=validate_proof queue
        ((#definition operations)node)
      val actual:('node,'tree,proof,unit)Clause.operations=
        {guard=fn()=>guard queue,tick=fn()=>pay queue 1,
         pay=pay queue,future=pay queue,profile=profile queue,
         type_weight=N.type_weight admission,
         template=IntInf.fromInt(#template_limit admission),
         metadata_template= #metadata_template operations,
         ceiling=IntInf.fromInt(#type_work_limit admission),
         hypothesis=hypothesis,error= #error operations,
         tree_view=tree_view,node_view=node_view,
         same_node= #same_node operations,named= #named operations,
         constant= #constant operations,
         constant_term= #constant_term operations,
         operator= #operator operations,
         theorem=validate_proof queue,definition=definition,
         dependency=fn _=>()}
      val _=pay queue 1
      val premises=copy queue(fn{tree,edge}=>
        (pay queue 3;{tree=tree,edge=validate_proof queue edge}))premises
      val _=pay queue 5
      val plan as Clause.Plan{programme,final,types=ports,...}=
        Clause.prepare actual {premises=premises,target=target,
          target_expanded=target_expanded,fallbacks=fallbacks}
      val result= #2(Vector.sub(programme,final))
      val _=pay queue 1
      fun remember []=guard queue
        | remember(ty::rest)=(pay queue 2;types:=ty:: !types;remember rest)
      val _=remember ports
      (* This closure can only retain the genuine private Clause plan.
         Its exact Type inventory is checked by the WHOLE queue first;
         the later worker rechecks owner/epochs at each cached port. *)
      val _=pay queue 8
      fun run()= #theorem(Clause.execute
        {guard=fn()=>guard queue,check_type=fn _=>guard queue,
         error= #error operations}plan)
    in publish queue(Recorded(run,#conclusion result,#hypotheses result))
      (#conclusion result)(#hypotheses result)end
  fun seal(queue as Queue{phase,commands,...})=
    let
      val _=building queue
      val _=pay queue 2 (* quote and visit closures *)
      (* Compare the already materialized, binder-free forecast exactly.
         N's held-shape fallback is stdknl-only; native experimental terms
         need not share its pointers. Quote both sides' bounded geometry
         here, never by profiling a result during native execution. *)
      fun quote target=
        let val p=profile queue target val bytes=spelling queue target
            val _=pay queue 2 (* type_names and annotations closures *)
            (* Annotation weight includes Type variables' spelling, but
               Type.compare also reads theory/operator names. *)
            fun type_names ty=
              (pay queue 1;if Type.is_vartype ty then 0 else
                let val _=pay queue 5
                    val {Thy,Tyop,Args}=Type.dest_thy_type ty
                    fun children []=0
                      | children(ty::rest)=
                          (pay queue 1;type_names ty+children rest)
                in IntInf.fromInt(String.size Thy)+
                  IntInf.fromInt(String.size Tyop)+children Args end)
            fun annotations term=
              (pay queue 1;if Term.is_comb term then
                let val _=pay queue 3 val(f,x)=Term.dest_comb term
                in annotations f+annotations x end
              else (pay queue 1;type_names(Term.type_of term)))
            val names=annotations target
        in pay queue(1+2*(weight p+bytes+names))end
      fun visit []=guard queue
        | visit((_,command)::rest)=
            (pay queue 1;
             (case command of Seed _=>()
                | Circuit(_,target)=>quote target
                | Recorded(_,target,_)=>quote target
                | Fixed(_,_,target,_)=>quote target
                | Boolean(_,_,target,_)=>quote target);
             visit rest)
      val _=visit(!commands)
      val _=pay queue 1
    in phase:=Sealed end
  fun type_ports(queue as Queue{types,...})=(guard queue;!types)
  fun check_types(queue as Queue{phase,types,...}) check_type=
    let val _=guard queue val _=pay queue 3
        val _=if !phase=Sealed then ()else
          raise ERR "check_types" "expected sealed metadata queue"
        val _=pay queue 1
        fun visit []=(guard queue;())
          | visit(ty::rest)=
              (pay queue 1;check_type ty;guard queue;visit rest)
        val _=visit(!types)
        val _=pay queue 1
    in phase:=Checked end
    handle primary=>(phase:=Closed;raise primary)
  val clean=N.clean
  fun execute(queue as Queue{phase,commands,results,...}) seed_proof=
    let val _=guard queue val _=pay queue 3
        val _=if !phase=Checked then ()else
          raise ERR "execute" "Type programme has not completed"
        val _=pay queue 1 val _=phase:=Running
        val _=pay queue 2
        fun reverse [] result=(guard queue;result)
          | reverse(x::rest)result=
              (pay queue 2;reverse rest(x::result))
        fun read id=(pay queue 1;case Redblackmap.peek(!results,id)of
            SOME proof=>proof
          | NONE=>raise ERR "execute" "forward native proof reference")
        fun checked target hypotheses proof=
          if Term.compare(target,Thm.concl proof)=EQUAL andalso
              clean proof andalso
              List.all(fn term=>List.exists(fn held=>
                Portable.pointer_eq(term,held))hypotheses)(Thm.hyp proof)
            then proof else raise ERR "execute" "native forecast changed"
        fun run []=(guard queue;())
          | run((id,command)::rest)=
            let val _=pay queue 3
                val proof=case command of Seed(slot,term)=>
                    let val actual=seed_proof slot val _=guard queue
                    in if Portable.pointer_eq(Thm.concl actual,term)andalso
                        clean actual andalso
                        (case Thm.hyp actual of [hyp]=>
                          Portable.pointer_eq(hyp,term)|_=>false)
                      then actual else raise ERR "execute"
                        "different actual constructor ASSUME"end
                  | Circuit(worker,target)=>
                      let val actual=case worker of
                              CircuitTruth=>boolTheory.TRUTH
                            | DefinitionCNF term=>
                                SmtCircuitSat.definition_cnf term
                            | ProveCNF pair=>SmtCircuitSat.prove_cnf pair
                          val _=guard queue
                      in if clean actual andalso null(Thm.hyp actual)
                          andalso Term.compare(target,Thm.concl actual)
                            =EQUAL then actual else
                        raise ERR "execute" "circuit forecast changed"end
                  | Recorded(run,target,hyp)=>
                      let val actual=run()val _=guard queue
                      in checked target hyp actual end
                  | Fixed(recipe,ids,target,hyp)=>
                      checked target hyp
                        (N.primitive_using fixed_arity_error same_name
                          recipe(copy queue read ids))
                  | Boolean(opcode,ids,target,hyp)=>
                      checked target hyp
                        (N.boolean_using boolean_arity_error same_name
                          opcode(copy queue read ids))
                val _=guard queue val _=pay queue 2
                val _=results:=Redblackmap.insert(!results,id,proof)
            in run rest end
        val _=run(reverse(!commands)[])
        val _=pay queue 1
    in phase:=Complete end
    handle primary=>(phase:=Closed;raise primary)
  fun theorem(queue as Queue{phase,results,...}) proof=
    let val _=ignore(validate_proof queue proof) val _=pay queue 2
    in if !phase=Complete then
        Redblackmap.find(!results,#index(held proof))else
      raise ERR "theorem" "native programme has not completed"end
  fun close(Queue{phase,...})=phase:=Closed
end
