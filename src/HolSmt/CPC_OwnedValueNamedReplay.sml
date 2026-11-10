(* Actual indexed CPC inference through existing sealed named/Source ports. *)
structure CPC_OwnedValueNamedReplay :> CPC_OwnedValueNamedReplay =
struct
  structure W=SmtReplayInvocationWork
  structure GP=SmtLib_GraphPreprocess
  structure VP=SmtLib_GraphValueProof
  structure PV=SmtLib_GraphParserValue
  structure F=SmtLib_GraphFrontend
  structure Q=CPC_ProofParser
  structure R=CPC_Proof
  structure Shared=CPC_SharedReplayPlan
  structure P=SmtReplayOwnedValueProof
  structure NC=SmtReplayNativeContract
  structure AtomPairs=SmtReplayValueAtomPairs
  val ERR=Feedback.mk_HOL_ERR "CPC_OwnedValueNamedReplay"
  datatype requirement =
      RuleProgramme of {id:string,rule:R.proof_rule,pop:bool}
    | ScopeProgramme of {id:string,assumption:bool}
    | RecordedConclusion of string
    | CurrentSourceTransport of {id:string,value:PV.value}
    | SourceOpening of SmtReplayGraph.scope * SmtReplayGraph.node
  datatype recipe=Source of int
    | SourceWithAtomEquations of int *
        (PV.proof_term * PV.proof_term) list
    | AndElim of string
    | BooleanPremises of string list
    | BooleanWithAtomEquations of string list *
        (PV.proof_term * PV.proof_term) list
    | BooleanWithFixedXors of
        {premises:string list,aliases:(PV.proof_term * PV.proof_term) list,
         xors:PV.proof_term list,clause:SmtReplayNamedContext.xor_clause}
    | EqualityPremises of {rule:string,premises:string list,
        equality_premises:string list,retain_all:bool}
    | EqualityWithAtomEquations of {rule:string,premises:string list,
        equality_premises:string list,retain_all:bool,
        aliases:(PV.proof_term * PV.proof_term) list}
  datatype truth_family=DeclaredBoolean | FalseIntro | FalseElim
    | TrueIntro | TrueElim | ProcessScope
  fun truth_family equal handler=
    if equal(handler,"bool")then SOME DeclaredBoolean
    else if equal(handler,"false_intro")then SOME FalseIntro
    else if equal(handler,"false_elim")then SOME FalseElim
    else if equal(handler,"true_intro")then SOME TrueIntro
    else if equal(handler,"true_elim")then SOME TrueElim
    else if equal(handler,"process_scope")then SOME ProcessScope
    else NONE
  (* Shared CNF discovery has already authenticated which one of the
     four actual XOR clauses was requested. The enum selects only a fixed
     globally valid library law; it grants no theorem or Source port. *)
  fun fixed_xor_clause equal name=
    if equal(name,"cnf_xor_pos1")then
      SmtReplayNamedContext.XorPositiveOne
    else if equal(name,"cnf_xor_pos2")then
      SmtReplayNamedContext.XorPositiveTwo
    else if equal(name,"cnf_xor_neg1")then
      SmtReplayNamedContext.XorNegativeOne
    else if equal(name,"cnf_xor_neg2")then
      SmtReplayNamedContext.XorNegativeTwo
    else raise ERR "prepare" "private fixed XOR clause family"
  datatype planned_node = Held of PV.proof_term | Truth
    | Conjunction of planned_node * planned_node
    | Equality of planned_node * planned_node
    | Application of planned_node * planned_node
    | Falsity
    | Negation of planned_node
    | Disjunction of planned_node * planned_node
    | SyntaxConjunction of planned_node * planned_node
    | Implication of planned_node * planned_node
    | Conditional of planned_node * planned_node * planned_node
  type literal={atom:PV.proof_term,negative:bool}
  type command={id:string,target:PV.value,recipe:recipe}
  type fact={node:PV.proof_term,provenance:R.term_provenance}
  type entry={node:PV.value,edge:P.edge}
  datatype invocation=Invocation of
    {work:W.portfolio,active:bool ref,guard:unit -> unit,block:P.block,
     remaining:command list ref,entries:(string,entry) Redblackmap.dict ref}
  datatype preparation=Prepared of invocation | Needs of requirement list
  fun protected work action=action()
    handle primary=>(W.close work;raise primary)
  fun header expected (Invocation{work,...})=
    if Portable.pointer_eq(expected,work)then ()else
      raise ERR "owner" "different original Work"
  fun live expected (saved as Invocation{active,guard,block,...})=
    (header expected saved;
     if !active then ()else raise ERR "owner" "CPC receiver retired";
     guard();P.validate_with_policy_for expected block)
  fun close(Invocation{active,block,...})=(active:=false;P.close block)
  fun prepare_with_policy work query packet
      {assertions,native_contract,check_type}=protected work(fn()=>
    let
      val _=GP.validate_query_with_policy work query
      val _=NC.validate_for work native_contract
      val (planned,pending,guard)=W.with_step work(fn()=>
        let
          val contents=VP.contents_with_policy_for work query packet
          val context= #context contents val scope= #scope contents
          val proof= #proof contents
          fun guard()=
            (ignore(VP.contents_with_policy_for work query packet);
             NC.validate_for work native_contract)
          fun pay amount=(guard();W.spend_policy work amount)
          fun tick()=pay 1
          fun string_work(left,right)=pay
            (1+IntInf.fromInt(String.size left)+
             IntInf.fromInt(String.size right))
          fun equal pair=(string_work pair;op = pair)
          fun compare pair=(string_work pair;String.compare pair)
          fun reverse values=
            let fun walk [] result=(guard();result)
                  | walk(value::rest)result=
                      (pay 2;walk rest(value::result))
            in walk values []end
          fun map action []=(guard();[])
            | map action(value::rest)=(pay 2;action value::map action rest)
          fun length []=(guard();0)
            | length(_::rest)=(tick();1+length rest)
          fun nth([],_) = raise Subscript
            | nth(value::_,0)=(tick();value)
            | nth(_::rest,index)=
                (tick();if index<0 then raise Subscript else
                  nth(rest,index-1))
          val _=if equal(#solver contents,"cvc5") andalso
              equal(#cvc_version proof,#resolved(#versions contents))then ()
            else raise ERR "owner" "actual CPC packet/version differs"
          val pending=ref([]:requirement list)
          fun need row=(pay 2;pending:=row:: !pending)
          (* Observe the actual registry search and then use its public
             lookup. The two real scans and actual version metadata are
             both paid; neither produces an inference permission. *)
          fun canonical(rule:R.proof_rule)=
            let
              fun version R.AllCVCVersions=pay 2
                | version(R.CVCVersions values)=
                    List.app(fn text=>
                      (tick();string_work(#cvc_version proof,text)))values
                | version(R.CVCVersionPrefixes values)=
                    List.app(fn text=>
                      (tick();string_work(text,#cvc_version proof)))values
              fun scan []=()
                | scan((row:R.proof_rule)::rest)=
                    (pay 2;string_work(#name row,#name rule);
                     string_work(#name row,#name rule);
                     if #name row= #name rule then
                       version(#version_support row)
                     else scan rest)
              val _=scan R.proof_rule_registry
              val actual=R.lookup_rule(#cvc_version proof)(#name rule)
              fun metadata(row:R.proof_rule)=
                (pay 4;string_work(#name row,#name rule);
                 string_work(#replay_handler row,#replay_handler rule);
                 version(#version_support row))
              val _=metadata rule
              val _=case actual of SOME row=>metadata row | NONE=>()
            in case actual of SOME row=>if row=rule then ()else
                raise ERR "packet" "rule differs from actual CPC registry"
              | NONE=>raise ERR "packet" "rule outside actual CPC registry"
            end
          (* The complete command list is checked before preparing names.
             No speculative prefix is executed when a later Scope/native
             programme has not been migrated. *)
          fun supported(Q.GraphAssume _)=tick()
            | supported(Q.GraphAssumePush(id,_))=
                need(ScopeProgramme{id=id,assumption=true})
            | supported(Q.GraphStep{step,pop})=
                let val _=tick()val _=canonical(#rule step)
                    val handler= #replay_handler(#rule step)
                    val route=Shared.route{equal=equal,visit=tick,copies=fn n=>
                      pay(IntInf.fromInt n)}
                      {pop=pop,handler=handler}
                    val family=Shared.simple_boolean equal handler
                    val equality=case family of NONE=>
                        Shared.simple_equality equal handler
                      | SOME _=>NONE
                in if route=Shared.Simple andalso
                      (Option.isSome family orelse Option.isSome equality)
                      andalso not pop then
                    (case #conclusion step of SOME _=>()
                      | NONE=>need(RecordedConclusion(#id step)))
                  else if (route=Shared.Converted orelse
                      route=Shared.Resolved orelse route=Shared.Aligned)
                      andalso not pop then
                    (case #conclusion step of SOME _=>()
                      | NONE=>need(RecordedConclusion(#id step)))
                  else if route=Shared.Simple andalso not pop andalso
                      Option.isSome(truth_family equal handler)then
                    (case #conclusion step of SOME _=>()
                      | NONE=>need(RecordedConclusion(#id step)))
                  else need(RuleProgramme
                    {id= #id step,rule= #rule step,pop=pop})end
          val _=List.app(fn command=>(tick();supported command))
            (#commands proof)
          val known=ref(Redblackmap.mkDict compare)
          val commands=ref([]:command list)
          val roots=ref([]:PV.value list)
          fun keep value=(PV.usable context scope value;
            pay 2;roots:=value:: !roots)
          fun occurrence_work(SmtLib_Parser.ConstructionOccurrence
              {role,token,children,...})=
            let
              val _=pay 6
              (* This genuine count pass itself is paid. It prepays the
                 following original List.map visits and result cells. *)
              val count=length children
              val _=pay(2*IntInf.fromInt count)
              fun token_equal text=
                let val _=string_work(token,text)
                    val answer=token=text
                    val _=string_work(token,text)
                in answer end
              fun reverse_work()=pay(2*IntInf.fromInt count+1)
            in case role of SmtLib_Parser.ConstructionApplication=>
                 if token_equal "and"then ()else
                   if token_equal "="then
                     (pay(IntInf.fromInt count);
                      if count=2 then pay(IntInf.fromInt count+1)else())
                   else()
              | SmtLib_Parser.ConstructionBinder{variables,...}=>
                  let val size=length variables
                  in pay(IntInf.fromInt size);reverse_work()end
              | SmtLib_Parser.ConstructionLet _=>reverse_work()
              | _=>()
            end
          fun fact(term:F.value_term):fact=
            let val value= #node term val _=keep value
                val provenance=Shared.occurrence_provenance_observed
                  occurrence_work(#occurrence term)
            in {node=PV.proof_term context value,provenance=provenance}end
          fun same(left,right)=
            let val(a,b)=PV.proof_key context left
                val(c,d)=PV.proof_key context right
            in pay 2;a=c andalso b=d end
          fun operands constant arity root=
            let fun walk current arguments=
              (tick();case PV.proof_view context current of
                  PV.ProofApplication(operator,operand)=>
                    (tick();walk operator(operand::arguments))
                | PV.ProofConstant atom=>
                    if Term.same_const atom constant andalso
                        length arguments=arity then SOME arguments else NONE
                | _=>NONE)
            in walk root []end
          fun children(R.ConjunctionProvenance(_,rows))=(tick();rows)
            | children(R.ApplicationProvenance(_,rows))=(tick();rows)
            | children _=raise ERR "discover"
                "missing immediate operand boundary"
          val selected=Shared.selected
            {children=children,
             recorded=Shared.recorded_observed(fn()=>pay 2)operands,
             length=length,node_at=nth,provenance_at=nth,
             error=ERR "discover"}
          fun require_one where_ [one]=(tick();one)
            | require_one where_ _=raise ERR where_
                "expected one operand/premise"
          fun tabulate (count,action) =
            let fun build index = if index=count then (tick();[])else
                  (pay 2;action index::build(index+1))
            in build 0 end
          fun negation_provenance provenance =
            let val children=Shared.child_provenance
                  {equal=equal,length=length,tabulate=tabulate}
                  "not" 1 provenance
            in tick();hd children end
          fun negated node = case operands boolSyntax.negation 1 node of
              SOME [body]=>SOME body | _=>NONE
          fun boolean node =
            (tick();if Type.compare(PV.proof_type_of context node,Type.bool)
                =EQUAL then ()else raise ERR "discover"
                  "non-Boolean rule operand")
          fun cursor_compare((a,b),(c,d))=
            (tick();case Int.compare(a,c)of
               EQUAL=>(tick();Int.compare(b,d))|x=>x)
          exception AliasDemand
          fun planned aliases expected actual =
            (boolean actual;case expected of Held node=>
               if same(node,actual)then ()else
                 (case aliases of NONE=>raise AliasDemand
                  | SOME state=>
                      if AtomPairs.demand work state(node,actual)then ()else
                        raise ERR "discover"
                          "declared rule endpoint differs")
             | Truth=>(case PV.proof_view context actual of
                 PV.ProofConstant atom=>
                   if Term.same_const atom boolSyntax.T then ()else
                     raise ERR "discover" "declared rule endpoint differs"
               | _=>raise ERR "discover" "declared rule endpoint differs")
             | Conjunction(left,right)=>
                 (case operands boolSyntax.conjunction 2 actual of
                   SOME [a,b]=>
                     (planned aliases left a;planned aliases right b)
                 | _=>raise ERR "discover" "declared rule endpoint differs")
             | _=>match_typed aliases expected actual)
          and match_typed aliases expected actual =
            let val _=pay 2
                val matched=ref(Redblackmap.mkDict cursor_compare)
                fun visit expected actual =
                  let val _=tick()val key=PV.proof_key context actual
                val bucket=Option.getOpt(Redblackmap.peek(!matched,key),[])
                fun contains []=(guard();false)
                  | contains(shape::rest)=
                      (tick();Portable.pointer_eq(shape,expected)orelse
                        contains rest)
                fun mismatch()=raise ERR "discover"
                  "declared rule endpoint differs"
                fun check()=case expected of
                    Held node=>if same(node,actual)then ()else
                      (case aliases of NONE=>raise AliasDemand
                       | SOME state=>
                           if AtomPairs.demand work state(node,actual)then
                             ()else mismatch())
                  | Truth=>(case PV.proof_view context actual of
                      PV.ProofConstant atom=>
                        if Term.same_const atom boolSyntax.T then ()else
                          mismatch()|_=>mismatch())
                  | Falsity=>(case PV.proof_view context actual of
                      PV.ProofConstant atom=>
                        if Term.same_const atom boolSyntax.F then ()else
                          mismatch()|_=>mismatch())
                  | Conjunction _=>planned aliases expected actual
                  | Negation body=>
                      (case operands boolSyntax.negation 1 actual of
                         SOME [inner]=>visit body inner|_=>mismatch())
                  | Disjunction(left,right)=>
                      (case operands boolSyntax.disjunction 2 actual of
                         SOME [a,b]=>(visit left a;visit right b)
                       | _=>mismatch())
                  | SyntaxConjunction(left,right)=>
                      (case operands boolSyntax.conjunction 2 actual of
                         SOME[a,b]=>(visit left a;visit right b)
                       | _=>mismatch())
                  | Implication(left,right)=>
                      (case operands boolSyntax.implication 2 actual of
                         SOME[a,b]=>(visit left a;visit right b)
                       | _=>mismatch())
                  | Conditional(condition,yes,no)=>
                      (case operands boolSyntax.conditional 3 actual of
                         SOME[a,b,c]=>
                           (visit condition a;visit yes b;visit no c)
                       | _=>mismatch())
                  | Equality(left,right)=>
                      (case PV.proof_view context actual of
                         PV.ProofApplication(partial,b)=>
                           (tick();case PV.proof_view context partial of
                              PV.ProofApplication(head,a)=>
                                (tick();case PV.proof_view context head of
                                   PV.ProofConstant atom=>
                                     if Term.same_const atom
                                       boolSyntax.equality then
                                       (visit left a;visit right b)
                                     else mismatch()
                                 | _=>mismatch())
                            | _=>mismatch())
                       | _=>mismatch())
                  | Application(left,right)=>
                      (case PV.proof_view context actual of
                         PV.ProofApplication(a,b)=>
                           (visit left a;visit right b)
                       | _=>mismatch())
            in if contains bucket then guard()else
              (check();pay 3;matched:=Redblackmap.insert
                (!matched,key,expected::bucket))end
            in visit expected actual end
          fun find id=(tick();case Redblackmap.peek(!known,id)of
              SOME row=>row | NONE=>raise ERR "discover"
                ("unknown/scoped-out premise "^id))
          fun save id current recipe target=
            (pay 4;known:=Redblackmap.insert(!known,id,current);
             commands:={id=id,target=target,recipe=recipe}:: !commands)
          fun source_index target=
            let fun walk [] _=NONE
                  | walk(value::rest)index=
                      (tick();if same(PV.proof_term context value,target)
                        then SOME index else walk rest(index+1))
            in walk assertions 0 end
          exception PendingEquality
          fun relation node =
            (tick();case PV.proof_view context node of
               PV.ProofApplication(partial,right)=>
                 (tick();case PV.proof_view context partial of
                    PV.ProofApplication(head,left)=>
                      (tick();case PV.proof_view context head of
                         PV.ProofConstant atom=>
                           if Term.same_const atom boolSyntax.equality then
                             SOME((),(left,right))else NONE
                       | _=>NONE)
                  | _=>NONE)
             | _=>NONE)
          fun pair node=case relation node of SOME(_,pair)=>pair
            | NONE=>raise ERR "discover" "expected relation premise"
          fun relation_kind node=case relation node of SOME(kind,_)=>kind
            | NONE=>raise ERR "discover" "expected relation premise"
          fun key node=(tick();PV.proof_key context node)
          val key_compare=cursor_compare
          fun arguments args =
            let fun walk []=(guard();[])
                  | walk(Q.GraphTerm term::rest)=
                      (tick();let val _=keep(#node term)
                       in PV.proof_term context(#node term)::walk rest end)
                  | walk(_::rest)=(tick();walk rest)
            in walk args end
          fun all_relations premises =
            let fun loop []=(guard();())
                  | loop((row:fact)::rest)=
                      (tick();case relation(#node row)of
                         SOME _=>loop rest | NONE=>raise PendingEquality)
            in loop premises end
          fun fold action initial values =
            let fun loop [] result=(guard();result)
                  | loop(value::rest)result=
                      (tick();loop rest(action(value,result)))
            in loop values initial end
          fun map_partial action values =
            let fun loop []=(guard();[])
                  | loop(value::rest)=
                      (tick();case action value of SOME result=>
                         (tick();result::loop rest)|NONE=>loop rest)
            in loop values end
          fun rewrite_using aliases premises source =
            let val replacements=fold(fn((row:fact),table)=>
                  let val (left,right)=pair(#node row)
                  in tick();Redblackmap.insert(table,key left,Held right)end)
                  (Redblackmap.mkDict key_compare)premises
                val _=pay 2
                val memo=ref(Redblackmap.mkDict key_compare)
            in Shared.congruence_rewrite
              {replacement=(case aliases of NONE=>
                 (fn node=>(tick();Redblackmap.peek(replacements,key node)))
               | SOME state=>(fn node=>
                   let
                     (* One actual fold callback; its fields/retained
                        replacement are charged on successful matches. *)
                     val _=pay 1
                   in fold(fn((row:fact),saved)=>
                     let val _=tick()val(left,right)=pair(#node row)
                     in if same(left,node)orelse
                         AtomPairs.demand work state(left,node)then
                         (pay 2;SOME(Held right))else saved end)
                       NONE premises end)),
               lookup=fn node=>(tick();Redblackmap.peek(!memo,key node)),
               publish=fn(node,result)=>(tick();memo:=Redblackmap.insert
                 (!memo,key node,result)),
               view=fn node=>(tick();case PV.proof_view context node of
                   PV.ProofApplication parts=>SOME parts
                 | PV.ProofOpaque=>raise PendingEquality
                 | PV.ProofAbstraction _=>raise PendingEquality
                 | _=>NONE),
               retained=Held,same=fn(node,Held result)=>same(node,result)
                 | _=>(tick();false),
               application=fn parts=>(pay 2;Application parts)} source end
          fun discover aliases(Q.GraphAssume(id,term))=
                let val current=fact term
                in case source_index(#node current)of SOME index=>
                    save id current(Source index)(#node term)
                  | NONE=>(case aliases of NONE=>raise AliasDemand
                    | SOME state=>
                      let
                        (* This is an ordered CURRENT occurrence search,
                           not a permission inferred from a syntax key. *)
                        val _=pay 1
                        fun candidate [] _=(guard();NONE)
                          | candidate(value::rest)index=
                              (pay 2;
                               if AtomPairs.demand work state
                                   (PV.proof_term context value,
                                    #node current)then SOME index else
                                 candidate rest(index+1))
                      in case candidate assertions 0 of
                          SOME index=>
                            let val pairs=AtomPairs.pairs_for work state
                                (* pair + recipe constructor *)
                                val _=pay 2
                            in save id current
                              (SourceWithAtomEquations(index,pairs))
                              (#node term)end
                        | NONE=>
                            (need(CurrentSourceTransport
                               {id=id,value= #node term});
                             tick();known:=Redblackmap.insert
                               (!known,id,current))end)end
            | discover aliases(Q.GraphStep{step,...})=
                let val premises=map find(#premises step)
                    val _=pay 6
                    val target=case #conclusion step of SOME row=>row
                      | NONE=>raise ERR "prepare" "missing planned conclusion"
                    val family=Shared.simple_boolean equal
                      (#replay_handler(#rule step))
                    fun current node provenance =
                      (pay 2;{node=node,provenance=provenance})
                    val equality=case family of NONE=>
                        Shared.simple_equality equal
                          (#replay_handler(#rule step))
                      | SOME _=>NONE
                    fun infer_equality()=
                      let
                    val target_node=PV.proof_term context(#node target)
                    val _=boolean target_node
                    fun shaped shape provenance=
                      (planned aliases shape target_node;
                       current target_node provenance)
                    fun related left right provenance=
                      let
                        (* This is only an unsupported-family filter.
                           The actual constructor and both operands still
                           have to match the shared exact typed plan. *)
                        val _=case PV.proof_view context target_node of
                            PV.ProofApplication(partial,_)=>
                              (tick();case PV.proof_view context partial of
                                 PV.ProofApplication(_,lhs)=>
                                   (tick();if Type.compare
                                     (PV.proof_type_of context lhs,
                                      SmtRegLanProve.reglan_ty)=EQUAL then
                                        raise PendingEquality else())
                               | _=>())
                          | _=>()
                      in shaped(Equality(left,right))
                        (R.EqualityProvenance provenance)end
                    fun atomic_relation left right=related left right
                      (R.AtomicProvenance,R.AtomicProvenance)
                    fun allowed_type node=
                      (tick();if Type.compare(PV.proof_type_of context node,
                          SmtRegLanProve.reglan_ty)=EQUAL then
                        raise PendingEquality else())
                    fun held_relation left right=
                      (allowed_type left;
                       atomic_relation(Held left)(Held right))
                    fun one()= #node(require_one "discover" premises)
                    fun one_provenance()= #provenance
                      (require_one "discover" premises)
                    fun held_related _ left right provenance=
                      related(Held left)(Held right)provenance
                      in case equality of
                        SOME Shared.SimpleRefl=>
                          if null premises then Shared.reflexive
                            {require_one=require_one,relation=held_relation}
                            (arguments(#args step))
                          else raise PendingEquality
                      | SOME Shared.SimpleSymm=>
                          (all_relations premises;
                           Shared.positive_symmetry
                             {pair=pair,one=one,
                              one_provenance=one_provenance,
                              relation_kind=relation_kind,
                              relation_with_kind=held_related})
                      | SOME Shared.SimpleTrans=>
                          let val _=case relation target_node of
                                  SOME(_,(left,_))=>allowed_type left
                                | NONE=>raise PendingEquality
                              fun types []=guard()
                                | types((row:fact)::rest)=
                                    (tick();case relation(#node row)of
                                       SOME(_,(left,_))=>
                                         (allowed_type left;types rest)
                                     | NONE=>types rest)
                              val _=types premises
                          in if Shared.relation_path
                            {visit=tick,relation=relation,
                             map_partial=map_partial,same_kind=op =,
                             same=(case aliases of NONE=>same
                               | SOME state=>(pay 1;fn pair=>same pair orelse
                                   AtomPairs.demand work state pair)),key=key,
                             empty=fn()=>(tick();
                               Redblackset.empty key_compare),
                             member=fn args=>(tick();
                               Redblackset.member args),
                             add=fn args=>(tick();Redblackset.add args),
                             push=fn(node,rest)=>(tick();node::rest),
                             fold=fold,error=ERR "trans"}
                            target_node(map #node premises)then
                            current target_node R.AtomicProvenance
                          else(case aliases of NONE=>raise AliasDemand
                            | SOME _=>raise PendingEquality)end
                      | SOME Shared.SimpleCong=>
                          let val _=all_relations premises
                              val args=arguments(#args step)
                              val source=require_one "cong" args
                              val terms=map_partial
                                (fn row as Q.GraphTerm _=>SOME row|_=>NONE)
                                (#args step)
                              val parsed=require_one "cong" terms
                              val provenance=case parsed of Q.GraphTerm term=>
                                  Shared.occurrence_provenance_observed
                                    occurrence_work(#occurrence term)
                                | _=>raise ERR "prepare" "private argument"
                              val _=case provenance of
                                  R.ApplicationProvenance("or",_)=>
                                    (case aliases of NONE=>raise AliasDemand
                                      | SOME _=>())
                                | _=>()
                          in atomic_relation(Held source)
                            (rewrite_using aliases premises source)end
                      | SOME Shared.SimpleHoCong=>
                          (all_relations premises;
                           Shared.higher_congruence
                             {map=map,pair=fn Held node=>
                                let val(a,b)=pair node
                                in (Held a,Held b)end
                                | _=>raise ERR "prepare" "private node",
                              application=fn parts=>(pay 2;Application parts),
                              relation=atomic_relation,error=ERR "ho_cong"}
                             (map(fn row=>Held(#node row))premises))
                      | SOME Shared.SimpleEqResolve=>
                          (case aliases of NONE=>
                            Shared.equality_resolve_with_aliases relation
                              {node= #node,pair=pair,provenance= #provenance,
                               same=same,current=current,
                               retry=fn detail=>
                                 not(#retired(W.audit_policy work))andalso
                                 not(SmtResource.is_resource_gate detail),
                               error=ERR "eq_resolve"} premises
                          | SOME state=>
                            let val _=pay 1
                                fun same_actual pair=same pair orelse
                                  AtomPairs.demand work state pair
                            in Shared.equality_resolve
                              {node= #node,pair=pair,provenance= #provenance,
                               same=same_actual,current=current,
                               retry=fn detail=>
                                 not(#retired(W.audit_policy work))andalso
                                 not(SmtResource.is_resource_gate detail),
                               error=ERR "eq_resolve"}premises end)
                      | SOME Shared.SimpleContra=>
                          shaped Falsity R.AtomicProvenance
                      | NONE=>raise ERR "prepare"
                          "unsupported equality programme"
                      end
                    fun infer_boolean family =
                      let
                        val target_node=PV.proof_term context(#node target)
                        fun current node provenance=
                          (pay 2;{node=node,provenance=provenance})
                        fun shaped shape provenance=
                          (planned aliases shape target_node;
                           current target_node provenance)
                        fun one()= #node(require_one "discover" premises)
                        fun one_provenance()= #provenance
                          (require_one "discover" premises)
                        fun child token count provenance=
                          (pay 4;Shared.child_provenance
                            {equal=equal,length=length,tabulate=tabulate}
                            token count provenance)
                        fun negative node provenance=
                          (pay 5;(Negation(Held node),
                           R.ApplicationProvenance("not",[provenance])))
                        fun positive node provenance=
                          (pay 2;(Held node,provenance))
                        fun actual_operands constant arity node=
                          case operands constant arity node of
                            SOME nodes=>nodes|NONE=>raise ERR "discover"
                              "incorrect rule operand constructor"
                        fun same_constant node atom=
                          (tick();case PV.proof_view context node of
                             PV.ProofConstant actual=>
                               Term.same_const actual atom|_=>false)
                        fun disjoin entries=
                          let
                            (* Six fields, four fresh closures, one operation
                               record; exactly two incoming signed cells. *)
                            val _=pay 13
                          in Shared.disjoin
                            {visit=tick,falsity=fn()=>(tick();Falsity),
                             atom=fn shape=>shaped shape R.AtomicProvenance,
                             current=shaped,
                             binary=fn parts=>(pay 2;Disjunction parts),
                             provenances=fn entries=>
                               let val values=map #2 entries val _=tick()
                               in values end} entries end
                        fun index()=(tick();case #args step of
                            [Q.GraphIndex index]=>index
                          | _=>raise ERR "discover"
                              "expected one recorded index")
                        val handler= #replay_handler(#rule step)
                      in case family of
                          Shared.SimpleNotOrElim=>
                            (pay 11;
                             Shared.not_or_elim
                            {require_one=require_one,node= #node,
                             negated=negated,
                             provenance= #provenance,selected=selected,
                             index=index,negate=fn node=>
                               (pay 4;Negation(Held node)),
                             current=shaped,error=ERR} premises)

                        | Shared.SimpleNotAnd=>
                            let
                              val _=pay 4
                              val template= #template_limit(#semantic_limits
                                (NC.for_work work native_contract))
                              val _=pay 2
                              val shapes=ref(Redblackmap.mkDict cursor_compare)
                              val _=pay 12
                              fun is_boolean node=
                                (tick();Type.compare
                                  (PV.proof_type_of context node,Type.bool)
                                    =EQUAL)
                              fun shape node=
                                let val _=tick()
                                    val key=PV.proof_key context node
                                in case Redblackmap.peek(!shapes,key)of
                                    SOME result=>result
                                  | NONE=>
                                    let
                                      val _=pay 7
                                      fun binary operator make next=
                                        case operands operator 2 node of
                                          SOME[a,b]=>
                                            (pay 2;make(shape a,shape b))
                                        | _=>next()
                                      fun literal()=
                                        (tick();Held node)
                                      fun equality()=
                                        case operands boolSyntax.equality 2
                                            node of
                                          SOME[a,b]=>if is_boolean a andalso
                                              is_boolean b then
                                                (pay 2;Equality
                                                  (shape a,shape b))
                                              else literal()
                                        | _=>literal()
                                      fun conditional()=
                                        case operands boolSyntax.conditional 3
                                            node of
                                          SOME[a,b,c]=>
                                            (pay 3;Conditional
                                              (shape a,shape b,shape c))
                                        | _=>equality()
                                      fun implication()=
                                        binary boolSyntax.implication
                                          Implication conditional
                                      fun disjunction()=
                                        binary boolSyntax.disjunction
                                          Disjunction implication
                                      fun conjunction()=
                                        binary boolSyntax.conjunction
                                          SyntaxConjunction disjunction
                                      val result=if not(is_boolean node)then
                                          literal()
                                        else if same_constant node
                                            boolSyntax.T then (tick();Truth)
                                        else if same_constant node
                                            boolSyntax.F then (tick();Falsity)
                                        else case negated node of SOME body=>
                                            (pay 2;Negation(shape body))
                                          | NONE=>conjunction()
                                      val _=pay 2
                                      val _=shapes:=Redblackmap.insert
                                        (!shapes,key,result)
                                    in result end
                                end
                              fun negative_literal node provenance=
                                (pay 5;(Negation(shape node),
                                  R.ApplicationProvenance
                                    ("not",[provenance])))
                              fun check message count=
                                (tick();if count<template then ()else
                                   raise ERR "not_and" message)
                              fun aggregate_children provenance=
                                (tick();case provenance of
                                   R.ConjunctionProvenance(_,rows)=>SOME rows
                                 | R.ApplicationProvenance(token,rows)=>
                                     if equal(token,"and")then SOME rows
                                     else NONE
                                 | _=>NONE)
                              fun zip [] []=(guard();[])
                                | zip(node::nodes)(prov::provs)=
                                    (pay 2;(node,prov)::zip nodes provs)
                                | zip _ _=raise ERR "discover"
                                    "recorded aggregate constructor differs"
                              fun append [] tail=(guard();tail)
                                | append(row::rows)tail=
                                    (pay 2;row::append rows tail)
                              val recorded_limit=
                                "recorded aggregate exceeds template limit"
                              fun aggregate body provenance=
                                (pay 17;Shared.aggregate_entries
                                  {children=aggregate_children,
                                   recorded=Shared.recorded_observed tick
                                     operands boolSyntax.conjunction,
                                   length=length,
                                   push=fn {node,provenance}=>fn result=>
                                     (pay 5;(node,provenance)::result),
                                   reverse=reverse,
                                   start=fn(nodes,provs,rest)=>
                                     (pay 4;append(zip nodes provs)rest),
                                   initial=fn(node,provenance)=>
                                     (pay 3;[(node,provenance)]),
                                   check=check recorded_limit,
                                   error=ERR "discover"} body provenance)
                              fun input()=
                                let val node=one()
                                    val provenance=one_provenance()
                                    val _=tick()
                                in case provenance of
                                    R.UnavailableProvenance _=>NONE
                                  | R.AmbiguousProvenance _=>NONE
                                  | R.ApplicationProvenance(token,rows)=>
                                      if equal(token,"or")then
                                        Shared.recorded_observed tick operands
                                          boolSyntax.disjunction(length rows)
                                          node
                                      else (pay 2;SOME[node])
                                  | _=>(pay 2;SOME[node])end
                              fun signed nodes=(tick();map(fn node=>
                                case negated node of SOME atom=>
                                    (pay 3;{atom=atom,negative=true})
                                  | NONE=>(pay 3;
                                      {atom=node,negative=false}))nodes)
                              fun produced () body=
                                (pay 21;Shared.produced_conjunction
                                  {run=fn action=>action(),observe=tick,
                                   input=input,recorded=signed,same=same,
                                   children=operands boolSyntax.conjunction 2,
                                   validate=boolean,
                                   check=check
                                     "produced AND portfolio exceeds template",
                                   pending=fn(left,right,rest)=>
                                     (pay 6;left::right::rest),
                                   leaf=fn(node,provenance,result)=>
                                     (pay 6;(node,provenance)::result),
                                   reverse=reverse,
                                   initial=fn body=>(tick();[body])}body)
                              fun disjoin_entries entries=
                                let
                                  (* Six fields, four closures, record/build.
                                     Signed cells are paid above. *)
                                  val _=pay 12
                                in Shared.disjoin
                                  {visit=tick,falsity=fn()=>(tick();Falsity),
                                   atom=fn shape=>
                                     shaped shape R.AtomicProvenance,
                                   current=shaped,
                                   binary=fn parts=>(pay 2;Disjunction parts),
                                   provenances=fn entries=>
                                     let val values=map #2 entries val _=tick()
                                     in values end} entries end
                              val _=pay 20
                            in Shared.not_and
                              {negated=negated,one=one,
                               one_provenance=one_provenance,
                               negation_provenance=negation_provenance,
                               operands=actual_operands,
                               is_false=fn node=>
                                 same_constant node boolSyntax.F,
                               child_provenance=child,
                               recorded_entries=aggregate,owned=SOME(),
                               produced_entries=produced,map=map,
                               negative=negative_literal,
                               disjoin=disjoin_entries,error=ERR "not_and"}
                            end
                        | Shared.SimpleNotImpliesElim1=>
                            (pay 9;
                             Shared.not_implies_elim1
                            {negated=negated,one=one,operands=actual_operands,
                             child_provenance=child,
                             negation_provenance=negation_provenance,
                             one_provenance=one_provenance,
                             current=current,error=ERR}handler)

                        | Shared.SimpleNotImpliesElim2=>
                            (pay 11;
                             Shared.not_implies_elim2
                            {negated=negated,one=one,operands=actual_operands,
                             child_provenance=child,
                             negation_provenance=negation_provenance,
                             one_provenance=one_provenance,negative=negative,
                             finish=fn(shape,provenance)=>
                               shaped shape provenance,error=ERR}handler)

                        | Shared.SimpleImpliesElim=>
                            (pay 8;
                             Shared.implies_elim
                            {operands=actual_operands,one=one,
                             child_provenance=child,
                             one_provenance=one_provenance,negative=negative,
                             positive=positive,disjoin=disjoin})

                        | Shared.SimpleEquivElim1=>
                            (pay 7;
                             Shared.equiv_elim1
                            {one=one,pair=pair,one_provenance=one_provenance,
                             negative=negative,positive=positive,
                             disjoin=disjoin})

                        | Shared.SimpleEquivElim2=>
                            (pay 7;
                             Shared.equiv_elim2
                            {one=one,pair=pair,one_provenance=one_provenance,
                             negative=negative,positive=positive,
                             disjoin=disjoin})

                        | Shared.SimpleNotEquivElim1=>
                            (pay 10;
                             Shared.not_equiv_elim1
                            {one=one,pair=pair,one_provenance=one_provenance,
                             negative=negative,positive=positive,
                             disjoin=disjoin,negated=negated,
                             negation_provenance=negation_provenance,
                             error=ERR}handler)

                        | Shared.SimpleNotEquivElim2=>
                            (pay 10;
                             Shared.not_equiv_elim2
                            {one=one,pair=pair,one_provenance=one_provenance,
                             negative=negative,positive=positive,
                             disjoin=disjoin,negated=negated,
                             negation_provenance=negation_provenance,
                             error=ERR}handler)

                        | Shared.SimpleIteElim1=>
                            (pay 11;
                             Shared.ite_elim1
                            {same_constant=same_constant,one=one,
                             atom=fn node=>current node R.AtomicProvenance,
                             operands=actual_operands,child_provenance=child,
                             one_provenance=one_provenance,negative=negative,
                             positive=positive,disjoin=disjoin})

                        | Shared.SimpleIteElim2=>
                            (pay 11;
                             Shared.ite_elim2
                            {same_constant=same_constant,one=one,
                             atom=fn node=>current node R.AtomicProvenance,
                             operands=actual_operands,child_provenance=child,
                             one_provenance=one_provenance,negative=negative,
                             positive=positive,disjoin=disjoin})
                        | _=>raise ERR "prepare"
                            "private new Boolean family"
                      end
                    val inferred=case family of SOME Shared.SimpleAndElim=>
                      Shared.and_elim
                        {require_one=require_one,node= #node,
                         provenance= #provenance,selected=selected,
                         current=current,error=ERR "discover"}
                        premises(#args step)
                    | SOME Shared.SimpleNotNotElim=>
                        Shared.not_not_elim
                          {negated=negated,
                           one=fn()=> #node(require_one "discover" premises),
                           one_provenance=fn()=> #provenance
                             (require_one "discover" premises),
                           negation_provenance=negation_provenance,
                           current=current,error=ERR "not_not_elim"}
                    | SOME Shared.SimpleAndIntro=>
                        Shared.and_intro
                          {conjunction=Shared.conjunction
                             {visit=tick,truth=fn()=>(tick();Truth),
                              binary=fn(left,right)=>
                                (pay 2;Conjunction(left,right))},
                           provenances=fn()=>map #provenance premises,
                           current=fn shape=>fn provenance=>
                             let val cursor=PV.proof_term context(#node target)
                                 val _=planned aliases shape cursor
                             in current cursor provenance end}
                          (map(fn premise=>(tick();Held(#node premise)))
                            premises)
                    | NONE=>(case equality of SOME _=>infer_equality()
                      | NONE=>if equal
                          (#replay_handler(#rule step),"resolution")orelse
                          equal(#replay_handler(#rule step),"factoring")orelse
                          equal(#replay_handler(#rule step),"reordering")then
                          let
                            val _=pay 1
                            fun infer_structural()=case aliases of
                                NONE=>raise AliasDemand
                              | SOME state=>
                                let
                                  (* New-only helpers; complete allocation
                                     invoice remains under audit. *)
                                  val _=pay 36
                                  val destination=fact target
                                  val destination_node= #node destination
                                  val handler= #replay_handler(#rule step)
                                  fun constant () value atom=
                                    let val _=tick()
                                        val node=PV.proof_term context value
                                    in case PV.proof_view context node of
                                        PV.ProofConstant term=>
                                          Term.same_const term atom
                                      | _=>false end
                                  fun type_of () value=
                                    (tick();PV.type_of context value)
                                  fun convert value=
                                    (tick();PV.proof_term context value)
                                  fun negate () node=negated node
                                  fun equal_nodes(a,b)=
                                    same(a,b)orelse
                                      AtomPairs.demand work state(a,b)
                                  fun same_literal
                                      ({atom=a,negative=x}:literal)
                                      ({atom=b,negative=y}:literal)=
                                    (tick();x=y andalso equal_nodes(a,b))
                                  fun opposite({atom,negative}:literal)=
                                    (pay 3;{atom=atom,negative=not negative})
                                  fun entry node:literal=
                                    (boolean node;case negated node of
                                        SOME atom=>
                                          (pay 2;{atom=atom,negative=true})
                                      | NONE=>
                                          (pay 2;{atom=node,negative=false}))
                                  fun clause({node,provenance}:fact)=
                                    let
                                      val _=tick()
                                      val nodes=case provenance of
                                          R.ApplicationProvenance("or",rows)=>
                                            (case Shared.recorded_observed
                                                tick operands
                                                boolSyntax.disjunction
                                                (length rows)node of
                                               SOME nodes=>nodes
                                             | NONE=>raise ERR "clause"
                                                 "recorded OR differs")
                                        | R.UnavailableProvenance _=>
                                            raise ERR "clause"
                                              "unavailable clause boundary"
                                        | R.AmbiguousProvenance _=>
                                            raise ERR "clause"
                                              "ambiguous clause boundary"
                                        | _=>(pay 1;[node])
                                    in case(nodes,provenance)of
                                        ([one],R.AtomicProvenance)=>
                                          (tick();case PV.proof_view context
                                              one of PV.ProofConstant atom=>
                                                if Term.same_const atom
                                                    boolSyntax.F then []
                                                else map entry nodes
                                            | _=>map entry nodes)
                                      | _=>map entry nodes end
                                  fun map_eq action([],[])=(guard();[])
                                    | map_eq action(a::left,b::right)=
                                        (pay 3;action(a,b)::
                                          map_eq action(left,right))
                                    | map_eq _ _=raise ERR "resolution"
                                        "private parallel lengths differ"
                                  fun option_map action NONE=(tick();NONE)
                                    | option_map action(SOME value)=
                                        (pay 1;SOME(action value))
                                  fun erase literal []=(tick();NONE)
                                    | erase literal(head::rest)=
                                        (tick();Shared.erase_present
                                          same_literal option_map erase
                                          literal head rest)
                                  fun append [] tail=(guard();tail)
                                    | append(x::rest)tail=
                                        (pay 2;x::append rest tail)
                                  fun joined(left,right)=append left right
                                  fun find action []=(tick();NONE)
                                    | find action(head::rest)=
                                        (tick();if action head then
                                          (tick();SOME head)
                                        else find action rest)
                                  fun exists action []=(tick();false)
                                    | exists action(head::rest)=
                                        (tick();action head orelse
                                          exists action rest)
                                  fun join left right pivot=
                                    (tick();Shared.resolution_join erase
                                      opposite joined ERR "resolution"
                                      left right pivot)
                                  fun dynamic left right=
                                    (pay 2;Shared.resolution_dynamic find
                                      exists same_literal opposite ERR
                                      left right)
                                  fun chain current rest annotations pivots=
                                    (tick();Shared.resolution_chain join
                                      dynamic reverse chain ERR current rest
                                      annotations pivots)
                                  fun chain_recorded left right pivot=
                                    (tick();case(erase pivot left,
                                        erase(opposite pivot)right)of
                                        (SOME a,SOME b)=>append a b
                                      | _=>raise ERR "chain_m_resolution"
                                        ("explicit pivot is absent from " ^
                                        "recorded clauses"))
                                  fun recorded current rest annotations=
                                    (tick();Shared.recorded_resolution_chain
                                      tick chain_recorded recorded ERR
                                      current rest annotations)
                                  fun is_false({atom,negative}:literal)()=
                                    (tick();not negative andalso
                                      (case PV.proof_view context atom of
                                          PV.ProofConstant term=>
                                            Term.same_const term boolSyntax.F
                                        | _=>false))
                                  fun position wanted values=
                                    let val _=tick()
                                        fun walk [] _=(guard();NONE)
                                          | walk(head::rest)index=
                                              (tick();if same_literal wanted
                                                  head then
                                                (tick();SOME index)
                                              else walk rest(index+1))
                                    in walk values 0 end
                                  fun literal_matches
                                      ({atom,negative}:literal)node=
                                    if negative then
                                      (tick();case negated node of
                                          SOME body=>equal_nodes(atom,body)
                                        | NONE=>false)
                                    else equal_nodes(atom,node)
                                  fun matches_entries [] node=
                                        (tick();case PV.proof_view context
                                            node of PV.ProofConstant term=>
                                              Term.same_const term
                                                boolSyntax.F
                                          | _=>false)
                                    | matches_entries[one]node=
                                        literal_matches one node
                                    | matches_entries(one::rest)node=
                                        (tick();case operands
                                            boolSyntax.disjunction 2 node of
                                            SOME[left,right]=>
                                              literal_matches one left
                                              andalso matches_entries rest
                                                right
                                          | _=>false)
                                  fun align source target=
                                    let val _=tick()
                                        val mapping=
                                SmtReplayClauseOccurrences.alignment_mapping
                                  map is_false ()position target source
                                        val _=pay 1
                                    in List.all(fn value=>
                                          (tick();Option.isSome value))
                                        mapping orelse
                                      matches_entries source destination_node
                                    end
                                  val target_literals=clause destination
                                  val clauses=map clause premises
                                  val _=if equal(handler,"resolution")then
                                      let
                                        val explicit=equal
                                          (#name(#rule step),
                                           "chain_m_resolution")
                                        val result=if explicit then
                                            let
                                              val(actual,polarities,atoms)=
                                                case #args step of
                                                  [Q.GraphTerm actual,
                                                   Q.GraphList polarities,
                                                   Q.GraphList atoms]=>
                                                    (actual,polarities,atoms)
                                                | _=>raise ERR
                                                    "chain_m_resolution"
                                            ("expected actual target and " ^
                                                  "two recorded pivot lists")
                                              val count=length premises-1
                                              val _=tick()
                                              val _=if count>=0 andalso
                                                  length polarities=count
                                                  andalso length atoms=count
                                                then ()else raise ERR
                                                  "chain_m_resolution"
                                                "recorded pivot count differs"
                                              val _=keep(#node actual)
                                              val _=if equal_nodes
                                                  (convert(#node actual),
                                                   destination_node)then ()
                                                else raise ERR
                                                  "chain_m_resolution"
                                            ("declared destination differs " ^
                                                "from recorded target")
                                              val _=pay 1
                                              val annotations=map_eq
                                                (Shared.recorded_pivot tick
                                                  constant type_of ()
                                                  convert negate ERR)
                                                (polarities,atoms)
                                            in case clauses of first::rest=>
                                                recorded first rest
                                                  annotations
                                              | []=>raise ERR
                                                  "chain_m_resolution"
                                                  "empty actual premise chain"
                                            end
                                          else let
                                            val annotations=
                                              Shared.pivot_arguments length
                                                map_eq constant ()convert
                                                ERR(#args step)
                                          in case clauses of first::rest=>
                                              #1(chain first rest
                                                annotations[])
                                            | []=>raise ERR "resolution"
                                                "empty resolution chain"
                                          end
                                      in if align result target_literals
                                        then ()else raise ERR "assemble"
                                          ("recorded resolution did not " ^
                                          "prove its target")
                                      end
                                    else let
                                      val source=require_one "alignment"
                                        clauses
                                    in if align source target_literals
                                      then ()else raise ERR "assemble"
                                        "recorded clause alignment failed"
                                    end
                                in destination end
                          in infer_structural()end
                        else if equal
                          (#replay_handler(#rule step),"cnf")then
                          let
                            (* One selected helper closure. No old Boolean
                               path allocates this new-family adapter. *)
                            val _=pay 1
                            fun infer_cnf()=
                              let
                                val _=pay 16
                                val _=if null premises then ()else
                                  raise ERR "cnf"
                                    "CNF producer expects no premises"
                                val argument=case #args step of
                                    Q.GraphTerm term::_=>term
                                  | _=>raise ERR "cnf" "missing graph operand"
                                val _=keep(#node argument)
                                val root=PV.proof_term context(#node argument)
                                val _=boolean root
                                val provenance=
                                  Shared.occurrence_provenance_observed
                                    occurrence_work(#occurrence argument)
                                val _=tick()
                                val whole=(root,provenance)
                                val target_node=PV.proof_term context
                                  (#node target)
                                fun shaped shape incoming=
                                  (planned aliases shape target_node;pay 2;
                                   {node=target_node,provenance=incoming})
                                fun atom node=(pay 2;
                                  (Held node,R.AtomicProvenance))
                                fun negative(node,_)=
                                  (pay 5;(Negation(Held node),
                                    R.ApplicationProvenance
                                      ("not",[R.AtomicProvenance])))
                                fun positive(entry as(node,provenance))=
                                  (tick();case provenance of
                                    R.ApplicationProvenance("not",[_])=>
                                      (case negated node of SOME body=>
                                         negative(body,R.AtomicProvenance)
                                       | NONE=>raise ERR "cnf"
                                           "recorded negation differs")
                                  | _=>atom node)
                                fun fixed operator count=
                                  let
                                    val _=tick()
                                    val _=case #args step of
                                        [Q.GraphTerm _]=>()
                                      | _=>raise ERR "cnf"
                                          "incorrect fixed CNF argument count"
                                    val nodes=case operands operator count root
                                        of SOME nodes=>nodes
                                      | NONE=>raise ERR "discover"
                                          "incorrect rule operand constructor"
                                    val _=pay 1
                                    val _=List.app boolean nodes
                                    val children=case provenance of
                                        R.EqualityProvenance(left,right)=>
                                          (pay 2;[left,right])
                                      | R.ApplicationProvenance(_,rows)=>
                                          if length rows=count then rows else
                                            (pay 1;tabulate(count,
                                              fn _=>R.AtomicProvenance))
                                      | _=>(pay 1;tabulate(count,
                                          fn _=>R.AtomicProvenance))
                                    val _=pay 1
                                    fun zip [] []=(guard();[])
                                      | zip(node::nodes)(entry::entries)=
                                          (pay 2;
                                           (node,entry)::zip nodes entries)
                                      | zip _ _=raise ERR "cnf"
                                          "private fixed boundary differs"
                                  in zip nodes children end
                                fun binary_nodes operator=
                                  case fixed operator 2 of [left,right]=>
                                    (tick();(left,right))
                                  | _=>raise Fail "binary CNF operands"
                                fun check count=
                                  let val _=pay 4
                                      val template= #template_limit
                                        (#semantic_limits
                                          (NC.for_work work native_contract))
                                  in if count>=template then
                                      raise ERR "discover"
                                    "recorded aggregate exceeds template limit"
                                    else()end
                                fun aggregate_entries operator token=
                                  let
                                    val _=pay 8
                                    fun children incoming=
                                      (tick();case incoming of
                                        R.ConjunctionProvenance(_,rows)=>
                                          if equal(token,"and")then SOME rows
                                          else NONE
                                      | R.ApplicationProvenance(head,rows)=>
                                          if equal(head,token)then SOME rows
                                          else NONE
                                      | _=>NONE)
                                    fun zip [] []=(guard();[])
                                      | zip(node::nodes)(entry::entries)=
                                          (pay 2;(node,entry)::
                                            zip nodes entries)
                                      | zip _ _=raise ERR "discover"
                                      "recorded aggregate constructor differs"
                                    fun append [] rest=(guard();rest)
                                      | append(row::rows)rest=
                                          (pay 2;row::append rows rest)
                                    val _=pay 17
                                  in Shared.aggregate_entries
                                    {children=children,
                                     recorded=Shared.recorded_observed tick
                                       operands operator,
                                     length=length,
                                     push=fn {node,provenance}=>fn result=>
                                       (pay 5;(node,provenance)::result),
                                     reverse=reverse,
                                     start=fn(nodes,entries,rest)=>
                                       (pay 4;append(zip nodes entries)rest),
                                     initial=fn(node,entry)=>
                                       (pay 3;[(node,entry)]),
                                     check=check,error=ERR "discover"}
                                    root provenance end
                                fun indexed operator token=
                                  let val _=tick()
                                      val index=case #args step of
                                          [Q.GraphTerm _,Q.GraphIndex index]=>
                                            index
                                        | _=>raise ERR "cnf"
                                            "expected aggregate and index"
                                      val entries=aggregate_entries operator
                                        token
                                  in nth(entries,index)handle Subscript=>
                                    raise ERR "cnf"
                                      "aggregate index out of range"end
                                fun aggregate operator token=
                                  (tick();case #args step of [Q.GraphTerm _]=>
                                      aggregate_entries operator token
                                    | _=>raise ERR "cnf"
                                        "incorrect aggregate argument count")
                                fun xor_nodes()=
                                  (case aliases of NONE=>raise AliasDemand
                                    | SOME state=>
                                      let
                                        val _=AtomPairs.demand_xor work state
                                          root
                                        val _=pay 4
                                        val operator=Term.prim_mk_const
                                          {Thy="HolSmt",Name="xor"}
                                      in binary_nodes operator end)
                                fun ite_nodes()=
                                  case fixed boolSyntax.conditional 3 of
                                    [a,b,c]=>(tick();(a,b,c))
                                  | _=>raise Fail "conditional CNF operands"
                                val literals=Shared.cnf_literals
                                  binary_nodes indexed aggregate xor_nodes
                                  ite_nodes positive negative map ERR
                                  (#name(#rule step))whole
                                val _=pay 12
                              in Shared.disjoin
                                {visit=tick,falsity=fn()=>(tick();Falsity),
                                 atom=fn shape=>shaped shape
                                   R.AtomicProvenance,current=shaped,
                                 binary=fn parts=>
                                   (pay 2;Disjunction parts),
                                 provenances=fn entries=>map #2 entries}
                                literals end
                          in infer_cnf()end
                        else(case truth_family equal
                          (#replay_handler(#rule step))of
                          NONE=>infer_equality()
                        | SOME family=>
                          let val _=pay 1
                    fun infer_truth family=
                      if family=ProcessScope then
                        (case aliases of NONE=>raise AliasDemand
                         | SOME state=>
                          let
                            (* Eight local functions and target-field read.
                               Shared arguments below are fully applied. *)
                            val _=pay 9
                            val target_node=PV.proof_term context(#node target)
                            fun visible node=boolean node
                            fun equal_nodes pair=
                              same pair orelse AtomPairs.demand work state pair
                            fun observed_operands () operator count node=
                              operands operator count node
                            fun copies count=pay(IntInf.fromInt count)
                            fun shaped shape provenance=
                              (planned aliases shape target_node;pay 2;
                               {node=target_node,provenance=provenance})
                            fun held node=(tick();Held node)
                            fun body_provenance(body:F.value_term)=
                              Shared.occurrence_provenance_observed
                                occurrence_work(#occurrence body)
                            fun construct(body:F.value_term)[]=fact target
                              | construct body entries=
                                let
                                  val _=pay 2
                                  val nodes=map #1 entries
                                  val children=map #2 entries
                                  (* Three fields, truth/binary callbacks
                                     and their operation record. *)
                                  val _=pay 6
                                  val antecedent=Shared.conjunction
                                    {visit=tick,truth=fn()=>Truth,
                                     binary=fn parts=>
                                       (pay 2;Conjunction parts)}
                                    (map held nodes)
                                  val provenance=case children of [one]=>one
                                    | _=>(pay 2;R.ConjunctionProvenance
                                        (R.ProcessScopeConjunction,children))
                                  val incoming=body_provenance body
                                in case PV.proof_view context
                                    (PV.proof_term context(#node body))of
                                    PV.ProofConstant atom=>
                                      if Term.same_const atom boolSyntax.F then
                                        (pay 5;shaped(Negation antecedent)
                                          (R.ApplicationProvenance
                                            ("not",[provenance])))else
                                        (pay 6;shaped
                                          (Implication(antecedent,
                                            Held(PV.proof_term context
                                              (#node body))))
                                          (R.ApplicationProvenance
                                            ("=>",[provenance,incoming])))
                                  | _=>(pay 6;shaped
                                      (Implication(antecedent,
                                        Held(PV.proof_term context
                                          (#node body))))
                                      (R.ApplicationProvenance
                                        ("=>",[provenance,incoming])))end
                          in case (#args step,premises)of
                              ([Q.GraphTerm body],[incoming])=>
                                let val _=keep(#node body)
                                    val body_node=PV.proof_term context
                                      (#node body)
                                    val entries=Shared.process_scope_entries
                                      visible equal_nodes observed_operands ()
                                      reverse copies body_node
                                      (#node incoming)(#provenance incoming)[]
                                in case entries of SOME entries=>
                                    construct body entries
                                  | NONE=>fact target end
                            | _=>fact target end)
                      else let
                        (* Nine helper closures and target-field read. *)
                        val _=pay 10
                        val target_node=PV.proof_term context(#node target)
                        fun one()= #node(require_one "discover" premises)
                        fun one_provenance()= #provenance
                          (require_one "discover" premises)
                        fun shaped shape provenance=
                          (planned aliases shape target_node;
                           pay 2;{node=target_node,provenance=provenance})
                        fun relation_with left right provenance=
                          (pay 2;shaped(Equality(left,right))
                            (R.EqualityProvenance provenance))
                        fun constant () () atom=
                          (tick();if Term.same_const atom boolSyntax.T then
                            Truth else(tick();
                            if Term.same_const atom boolSyntax.F then Falsity
                            else raise ERR "prepare"
                              "private nontruth constant"))
                        fun observed_negation () node=negated node
                        fun same_constant () node atom=
                          (tick();case PV.proof_view context node of
                             PV.ProofConstant value=>Term.same_const value atom
                           | _=>false)
                        fun negative node provenance=
                          (pay 5;(Negation(Held node),
                            R.ApplicationProvenance("not",[provenance])))
                        fun retained node=(tick();Held node)
                      in case family of
                          DeclaredBoolean=>fact target
                        | FalseIntro=>Shared.false_intro observed_negation ()
                            one retained constant () () negation_provenance
                            one_provenance relation_with ERR
                        | FalseElim=>Shared.false_elim pair one
                            Shared.equality_provenance one_provenance
                            same_constant () negative shaped ERR
                        | TrueIntro=>Shared.true_intro one retained constant
                            () () one_provenance relation_with
                        | TrueElim=>Shared.true_elim pair one
                            Shared.equality_provenance one_provenance
                            same_constant () retained shaped ERR
                        | ProcessScope=>raise ERR "prepare"
                            "private process-scope selection"
                      end
                          in infer_truth family end))
                    | SOME other=>infer_boolean other
                    val declared=fact target
                    val _=if same(#node inferred,#node declared)then ()else
                      raise ERR "discover" "declared rule endpoint differs"
                    fun equation_ids([],[])=(guard();[])
                      | equation_ids(id::ids,(row:fact)::rows)=
                          (tick();case relation(#node row)of SOME _=>
                             (tick();id::equation_ids(ids,rows))
                           | NONE=>equation_ids(ids,rows))
                      | equation_ids _=raise ERR "prepare" "private arity"
                    val equality_ids=case equality of
                        SOME Shared.SimpleTrans=>
                          equation_ids(#premises step,premises)
                      | _=> #premises step
                    val mode=case family of SOME Shared.SimpleAndElim=>
                        (case #premises step of [id]=>AndElim id
                         | _=>raise ERR "prepare"
                             "private premise arity differs")
                      | _=>(case equality of
                          SOME Shared.SimpleRefl=>EqualityPremises
                            {rule="refl",premises= #premises step,
                             equality_premises=equality_ids,
                             retain_all=false}
                        | SOME Shared.SimpleSymm=>EqualityPremises
                            {rule="symm",premises= #premises step,
                             equality_premises=equality_ids,
                             retain_all=false}
                        | SOME Shared.SimpleTrans=>EqualityPremises
                            {rule="trans-star",premises= #premises step,
                             equality_premises=equality_ids,
                             retain_all=true}
                        | SOME Shared.SimpleCong=>EqualityPremises
                            {rule="cong",premises= #premises step,
                             equality_premises=equality_ids,
                             retain_all=false}
                        | SOME Shared.SimpleHoCong=>EqualityPremises
                            {rule="cong",premises= #premises step,
                             equality_premises=equality_ids,
                             retain_all=false}
                        | _=>BooleanPremises(#premises step))
                    val mode=case aliases of NONE=>mode | SOME state=>
                      let val pairs=AtomPairs.pairs_for work state
                          val xors=AtomPairs.xors_for work state
                      in case xors of _::_=>
                          (case mode of BooleanPremises premises=>
                              let val _=pay 2
                                  val clause=fixed_xor_clause equal
                                    (#name(#rule step))
                                  (* Four fields, record and recipe tag. *)
                                  val _=pay 6
                              in BooleanWithFixedXors
                                {premises=premises,aliases=pairs,xors=xors,
                                 clause=clause}end
                            | _=>raise ERR "prepare" "private fixed law mode")
                        | []=>case pairs of []=>mode | _=>(case mode of
                          BooleanPremises premises=>
                            (pay 2;BooleanWithAtomEquations(premises,pairs))
                        | AndElim id=>
                            (pay 3;BooleanWithAtomEquations([id],pairs))
                        | EqualityPremises{rule,premises,equality_premises,
                            retain_all}=>
                            (pay 6;EqualityWithAtomEquations
                              {rule=rule,premises=premises,
                               equality_premises=equality_premises,
                               retain_all=retain_all,aliases=pairs})
                        | _=>raise ERR "prepare" "private alias recipe")end
                in save(#id step)declared mode(#node target)end
            | discover _ _=raise ERR "prepare" "unsupported Scope in queue"
          val _=if null(!pending)then
              List.app(fn command=>(tick();if null(!pending)then
                (discover NONE command handle AliasDemand=>
                  let
                    (* Only the metadata miss is retried. Actual owner,
                       quota and callback Primaries are never caught. *)
                    val state=AtomPairs.create work query packet
                    (* SOME/private retry argument. No old-route state. *)
                    val _=pay 1
                  in discover(SOME state)command
                    handle PendingEquality=>
                      (case command of Q.GraphStep{step,pop}=>
                         need(RuleProgramme
                           {id= #id step,rule= #rule step,pop=pop})
                       | _=>raise ERR "prepare" "private pending Source")
                  end
                | Shared.AliasCorrespondence _=>
                  let
                    (* Only the metadata miss is retried. Actual owner,
                       quota and callback Primaries are never caught. *)
                    val state=AtomPairs.create work query packet
                    (* SOME/private retry argument. No old-route state. *)
                    val _=pay 1
                  in discover(SOME state)command
                    handle PendingEquality=>
                      (case command of Q.GraphStep{step,pop}=>
                         need(RuleProgramme
                           {id= #id step,rule= #rule step,pop=pop})
                       | _=>raise ERR "prepare" "private pending Source")
                  end
                | PendingEquality=>
                  (case command of Q.GraphStep{step,pop}=>
                     need(RuleProgramme{id= #id step,rule= #rule step,pop=pop})
                   | _=>raise ERR "prepare" "private pending Source"))
                else()))(#commands proof)else()
          val rows=reverse(!commands)val values=reverse(!roots)
          val _=if null rows andalso null(!pending)then
              raise ERR "prepare" "empty CPC proof"else()
        in ((rows,values,compare),reverse(!pending),guard)end)
      val(rows,roots,compare)=planned
    in if not(null pending)then Needs pending else
      case P.prepare work query packet{assertions=assertions,roots=roots,
          native_contract=native_contract,check_type=check_type}of
        P.NeedsOpening openings=>Needs(W.with_step work(fn()=>
          let fun copy []=(guard();[])
                | copy(row::rest)=
                    (guard();W.spend_policy work 2;
                     SourceOpening row::copy rest)
          in copy openings end))
      | P.Prepared block=>Prepared(Invocation{work=work,active=ref true,
          guard=guard,block=block,remaining=ref rows,
          entries=ref(Redblackmap.mkDict compare)})
    end)
  fun replay_next_with_policy expected saved=protected expected(fn()=>
    (header expected saved;W.with_step expected(fn()=>
      let val _=live expected saved
          val Invocation{block,remaining,entries,...}=saved
          fun tick()=(live expected saved;W.spend_policy expected 1)
          fun find id=(tick();case Redblackmap.peek(!entries,id)of
              SOME entry=>entry | NONE=>raise ERR "replay"
                "premise was not completed")
      in case !remaining of []=>(live expected saved;NONE)
        | ({id,target,recipe}:command)::rest=>
          let val edge=case recipe of Source index=>
                  P.source expected block
                    (P.source_port_for expected block index)
                | SourceWithAtomEquations(index,aliases)=>
                    let
                      val port=P.source_port_for expected block index
                      val actual=P.source_data_for expected port
                      val source=P.source expected block port
                      (* Actual port/query/index authority stays in P.
                         The alias is proved by this SAME named block. *)
                      val _=tick()
                      val _=W.spend_policy expected 6
                    in P.assemble_boolean_with_atom_aliases expected block
                      {target=target,premises=[(#value actual,source)],
                       aliases=aliases}end
                | AndElim premise=>
                    let val row=find premise
                    in P.assemble_boolean expected block
                      {target=target,premises=[(#node row,#edge row)]}end
                | BooleanPremises premises=>
                    let fun rows []=(live expected saved;[])
                          | rows(id::rest)=
                              let val _=tick()val row=find id
                              in (#node row,#edge row)::rows rest end
                    in P.assemble_boolean expected block
                      {target=target,premises=rows premises}end
                | BooleanWithAtomEquations(premises,aliases)=>
                    let
                      val _=W.spend_policy expected 1
                      fun rows []=(live expected saved;[])
                        | rows(id::rest)=
                            let val _=tick()val row=find id
                            in (#node row,#edge row)::rows rest end
                      val actual=rows premises
                      val _=W.spend_policy expected 4
                    in P.assemble_boolean_with_atom_aliases expected block
                      {target=target,premises=actual,aliases=aliases}end
                | BooleanWithFixedXors{premises,aliases,xors,clause}=>
                    let
                      val _=W.spend_policy expected 1
                      fun rows []=(live expected saved;[])
                        | rows(id::rest)=
                            let val _=tick()val row=find id
                            in (#node row,#edge row)::rows rest end
                      val actual=rows premises
                      val _=W.spend_policy expected 6
                    in P.assemble_boolean_with_fixed_xors expected block
                      {target=target,premises=actual,aliases=aliases,
                       xors=xors,clause=clause}end
                | EqualityWithAtomEquations
                    {rule,premises,equality_premises,retain_all,aliases}=>
                    let
                      val _=W.spend_policy expected 2
                      fun rows []=(live expected saved;[])
                        | rows(id::rest)=
                            let val _=tick()val row=find id
                            in (#node row,#edge row)::rows rest end
                      val all=rows premises
                      val equations=if retain_all then rows equality_premises
                        else all
                      val _=W.spend_policy expected 5
                      val result=P.assemble_equality_with_atom_aliases
                        expected block
                        {rule=rule,target=target,premises=equations,
                         aliases=aliases}
                      fun support([],result)=(live expected saved;result)
                        | support((_,edge)::rest,result)=
                            let val _=tick()
                                val both=P.derive_boolean expected block
                                  SmtReplayNamedContext.PolicyConjunction
                                  [result,edge]
                                val retained=P.derive_boolean expected block
                                  SmtReplayNamedContext.PolicyConjunctLeft
                                  [both]
                            in support(rest,retained)end
                    in if retain_all then support(all,result)else result end
                | EqualityPremises{rule,premises,equality_premises,
                    retain_all}=>
                    let fun rows []=(live expected saved;[])
                          | rows(id::rest)=
                              let val _=tick()val row=find id
                              in (#node row,#edge row)::rows rest end
                        val all=rows premises
                        val equations=if retain_all then rows equality_premises
                          else all
                        val result=P.assemble_equality expected block
                          {rule=rule,target=target,premises=equations}
                        fun support([],result)=(live expected saved;result)
                          | support((_,edge)::rest,result)=
                              let val _=tick()
                                  val both=P.derive_boolean expected block
                                    SmtReplayNamedContext.PolicyConjunction
                                    [result,edge]
                                  val retained=P.derive_boolean expected block
                                    SmtReplayNamedContext.PolicyConjunctLeft
                                    [both]
                              in support(rest,retained)end
                    in if retain_all then support(all,result)else result end
              val theorem=P.compact_theorem_for expected block edge
              val wanted=P.name expected block target
              val _=tick()
              val _=if Portable.pointer_eq(Thm.concl theorem,wanted)then ()else
                raise ERR "replay" "named endpoint differs"
              val _=tick()val _=entries:=Redblackmap.insert
                (!entries,id,{node=target,edge=edge})
              val _=tick()val _=remaining:=rest
              val _=live expected saved
          in SOME{id=id,node=target}end
      end)))
  fun step_with_policy_for expected saved id=protected expected(fn()=>
    (header expected saved;W.with_step expected(fn()=>
      let val _=live expected saved
          val Invocation{block,entries,...}=saved
          val _=W.spend_policy expected 1
          val row=case Redblackmap.peek(!entries,id)of SOME row=>row
            | NONE=>raise ERR "replay" "command was not completed"
          val _=ignore(P.compact_theorem_for expected block(#edge row))
          val _=live expected saved
      in {block=block,node= #node row,edge= #edge row}end)))
end
