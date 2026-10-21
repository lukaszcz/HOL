signature SmtReplayNamedClauseInput =
sig
  type input
  val concl : input -> Term.term
  val hyp : input -> Term.term list
  val tag : input -> Tag.tag
  val read : input -> Thm.thm
end

(* Syntax and metadata only; no native proof constructors. *)
structure SmtReplayNamedClauseSyntax =
struct
  type profile =
    {raw:IntInf.int,inc:IntInf.int,ann:IntInf.int,ty:IntInf.int}
  datatype ('node,'tree) tree_view = ClauseFalse of 'node
    | ClauseLiteral of {node:'node,atom:'node,negative:bool}
    | ClauseOr of {node:'node,left:'tree,right:'tree}
  datatype 'node node_view = NodeAtom | NodeConstant
    | NodeApplication of 'node * 'node
  type ('node,'tree,'edge,'dependency,'input) operations =
    {guard:unit -> unit,tick:unit -> unit,
     pay:IntInf.int -> unit,future:IntInf.int -> unit,
     profile:Term.term -> profile,type_weight:Type.hol_type -> IntInf.int,
     template:IntInf.int,metadata_template:SmtReplayResourcePolicy.limit,
     ceiling:IntInf.int,hypothesis:Term.term -> bool,error:string -> exn,
     tree_view:'tree -> ('node,'tree) tree_view,
     node_view:'node -> 'node node_view,same_node:'node * 'node -> bool,
     named:'node -> Term.term,constant:Term.term -> 'node -> bool,
     constant_term:'node -> Term.term,
     operator:Term.term -> int -> 'node -> 'node list,
     theorem:'edge -> 'input,definition:'node -> 'edge,
     dependency:'edge -> 'dependency}
  type ('node,'edge,'dependency,'input) congruence_operations =
    {guard:unit -> unit,tick:unit -> unit,
     pay:IntInf.int -> unit,future:IntInf.int -> unit,
     profile:Term.term -> profile,type_weight:Type.hol_type -> IntInf.int,
     template:IntInf.int,metadata_template:SmtReplayResourcePolicy.limit,
     ceiling:IntInf.int,hypothesis:Term.term -> bool,error:string -> exn,
     node_view:'node -> 'node node_view,same_node:'node * 'node -> bool,
     named:'node -> Term.term,constant_term:'node -> Term.term,
     theorem:'edge -> 'input,definition:'node -> 'edge,
     dependency:'edge -> 'dependency}
end

(* A static request specialization.  It creates no runtime adapter
   record, callback closures, fake clause tree, or theorem capability. *)
signature SmtReplayNamedClauseRequest =
sig
  type input
  type ('node,'tree,'edge,'dependency) operations
  type ('node,'tree,'edge) request
  val clause_mode : bool
  val constructor_mode : bool
  val same_final : Term.term * Term.term -> bool
  val guard :
    ('node,'tree,'edge,'dependency) operations ->
    unit -> unit
  val tick :
    ('node,'tree,'edge,'dependency) operations ->
    unit -> unit
  val pay :
    ('node,'tree,'edge,'dependency) operations ->
    IntInf.int -> unit
  val future :
    ('node,'tree,'edge,'dependency) operations ->
    IntInf.int -> unit
  val profile :
    ('node,'tree,'edge,'dependency) operations ->
    Term.term -> SmtReplayNamedClauseSyntax.profile
  val type_weight :
    ('node,'tree,'edge,'dependency) operations ->
    Type.hol_type -> IntInf.int
  val template :
    ('node,'tree,'edge,'dependency) operations ->
    IntInf.int
  val metadata_template :
    ('node,'tree,'edge,'dependency) operations ->
    SmtReplayResourcePolicy.limit
  val ceiling :
    ('node,'tree,'edge,'dependency) operations ->
    IntInf.int
  val hypothesis :
    ('node,'tree,'edge,'dependency) operations ->
    Term.term -> bool
  val error :
    ('node,'tree,'edge,'dependency) operations ->
    string -> exn
  val tree_view :
    ('node,'tree,'edge,'dependency) operations ->
    'tree -> ('node,'tree) SmtReplayNamedClauseSyntax.tree_view
  val node_view :
    ('node,'tree,'edge,'dependency) operations ->
    'node -> 'node SmtReplayNamedClauseSyntax.node_view
  val same_node :
    ('node,'tree,'edge,'dependency) operations ->
    'node * 'node -> bool
  val named :
    ('node,'tree,'edge,'dependency) operations ->
    'node -> Term.term
  val constant :
    ('node,'tree,'edge,'dependency) operations ->
    Term.term -> 'node -> bool
  val constant_term :
    ('node,'tree,'edge,'dependency) operations ->
    'node -> Term.term
  val operator :
    ('node,'tree,'edge,'dependency) operations ->
    Term.term -> int -> 'node -> 'node list
  val theorem :
    ('node,'tree,'edge,'dependency) operations ->
    'edge -> input
  val definition :
    ('node,'tree,'edge,'dependency) operations ->
    'node -> 'edge
  val dependency :
    ('node,'tree,'edge,'dependency) operations ->
    'edge -> 'dependency
  val clause_input : ('node,'tree,'edge) request ->
    {premises:{tree:'tree,edge:'edge} list,target:'tree,
     target_expanded:'tree option,fallbacks:'tree list}
  val pair_input : ('node,'tree,'edge) request -> 'node * 'node
  val node_input : ('node,'tree,'edge) request -> 'node
end

(* The actual model, admission and native executor are one physical body.
   Static clause specialization recovers the original programme literally. *)
functor SmtReplayNamedClausePlanFn
  (structure Native:SmtReplayNamedClauseInput
   structure Request:SmtReplayNamedClauseRequest
   sharing type Native.input=Request.input) =
struct
  open SmtReplayNamedClauseSyntax
  fun clean_using read_tag theorem =
    let val (oracles, _) = Tag.dest_tag (read_tag theorem) in
      List.all (fn oracle => oracle = "DISK_THM") oracles andalso
      List.null (Tag.axioms_of (read_tag theorem))
    end
  fun clean theorem = clean_using Thm.tag theorem
  datatype operation =
      PRInput of Native.input
    | PRAssume of Term.term
    | PRReflexive of Term.term
    | PRReverse of int
    | PRCompose of int * int
    | PRApplyOperator of Term.term * int
    | PRApplyArgument of int * Term.term
    | PRCombine of int * int
    | PREqualityMP of int * int
    | PRDischarge of Term.term * int
    | PRModus of int * int
    | PRLeft of int * Term.term
    | PRRight of Term.term * int
    | PRCases of int * int * int
    | PRNotElim of int
    | PRContradiction of Term.term * int
    | PRJoin of int * int
    | PRFirst of int
  type model =
    {conclusion:Term.term,hypotheses:Term.term list}
  datatype 'dependency plan = Plan of
    {programme:(operation * model) vector,final:int,target:Term.term,
     dependencies:'dependency list,types:Type.hol_type list}
  fun finish_preparation
      valid tick pay future profile weight port fail
      observed_terms verification operations
      dependencies type_ports index target_name final =
    let
        (* No proof/callback has run. Scan only already bounded compact
           Term ports; retain actual operator/partial-function Type ports
           as well as result Types for the external admission callback. *)
        val observed=ref([]:Term.term list)
        val largest_name=ref(0:IntInf.int)
        fun forest term=
          (tick();if List.exists(fn held=>
             (tick();Portable.pointer_eq(term,held)))(!observed)then ()else
           let val _=ignore(profile term)
               val _=observed:=term:: !observed
               val _=port(Term.type_of term)
           in if Term.is_comb term then
                let val(a,b)=Term.dest_comb term in forest a;forest b end
              else if Term.is_abs term then
                fail "binder in actual compact Type callback forest"
              else if Term.is_var term then
                let val text= #1(Term.dest_var term)
                    val amount=IntInf.fromInt(String.size text)
                    val _=pay(1+amount)
                in largest_name:=IntInf.max(!largest_name,amount)end
              else ()end)
        val _=List.app forest(!observed_terms)
        (* EXP builds fresh application cells. Comparisons below are
           admitted binder-free compact comparisons in BOTH kernels,
           including worst-case failed Hyp membership comparisons. *)
        val _=future((1+ !largest_name)* !verification)
        val _=valid()
    in Plan {programme=Vector.fromList(List.rev(!operations)),
      final=index final,target=target_name,dependencies= !dependencies,
      types=List.rev(!type_ports)} end
  fun constructor_value node borrowed definition same named node_view
      constant_term application compose apply_argument recurse expression
      (error:string -> exn) =
             let val direct=borrowed(definition node)
                 val(a,b)=boolSyntax.dest_eq(expression direct)
                 val _=if same a(named node)then ()else
                   raise error "definition names another actual node"
                 val value=case node_view node of NodeConstant=>
                       if same b(constant_term node)then direct
                       else raise error "constant definition changed"
                   | NodeApplication(f,x)=>
                       let val expected=application(named f)(named x)
                           val _=if same b expected then ()else
                             raise error "application definition changed"
                       in compose direct(apply_argument(recurse f)
                           (named x))end
                   | _=>raise error "nonconstructor definition requested"
             in value end
  fun prepare_using aliases
      (operations:('node,'tree,'edge,'dependency) Request.operations)
      (request:('node,'tree,'edge) Request.request) =
    let
        val valid=Request.guard operations
        val tick=Request.tick operations
        val pay=Request.pay operations
        val future=Request.future operations
        val profile=Request.profile operations
        val type_weight=Request.type_weight operations
        val template=Request.template operations
        val metadata_template=Request.metadata_template operations
        val ceiling=Request.ceiling operations
        val hypothesis=Request.hypothesis operations
        val error=Request.error operations
        val tree_view=Request.tree_view operations
        val node_view=Request.node_view operations
        val same_node=Request.same_node operations
        val named=Request.named operations
        val constant=Request.constant operations
        val constant_term=Request.constant_term operations
        val operator=Request.operator operations
        val theorem=Request.theorem operations
        val definition=Request.definition operations
        val dependency=Request.dependency operations
        fun fail text=raise error text
        val type_ports=ref([]:Type.hol_type list)
        val portfolio=ref(0:IntInf.int)
        fun weight(p:profile)= #raw p+ #inc p+ #ann p
        fun shape(p:profile)=
          if #raw p<=template andalso #inc p<=template andalso
              SmtReplayResourcePolicy.allows metadata_template(#raw p)andalso
              SmtReplayResourcePolicy.allows metadata_template(#inc p)
              andalso #ann p<=ceiling then ()else
            fail "actual compact native template exceeds caller cap"
        val input_shape=shape
        val output_shape=shape
        fun add amount=
          (portfolio:= !portfolio+amount;
           if !portfolio<=ceiling then ()else
             fail "actual repeated native Type portfolio exceeded")
        fun port ty=
          let val amount=type_weight ty
          in add amount;type_ports:=ty:: !type_ports end
        fun same a b=
          (tick();if Portable.pointer_eq(a,b)then true else
           let val x=profile a val y=profile b
               val _=pay(1+weight x+weight y)
           in Term.aconv a b end)
        fun member term=List.exists(fn other=>same term other)
        fun union left right=List.foldl(fn(term,held)=>
          if member term held then held else term::held)left right
        (* Term publication is binder-free DATA, but its exact repeated
           Type/geometry portfolio is also admitted before constructing it.
           It cannot authorize any later native proof operation. *)
        fun application f x=
          let val a=profile f val b=profile x
              val(dom,rng)=Type.dom_rng(Term.type_of f)
              val _=if Type.compare(dom,Term.type_of x)=EQUAL then ()else
                fail "actual compact application Type mismatch"
              val own=type_weight rng
              val p={raw=1+ #raw a+ #raw b,inc=1+ #inc a+ #inc b,
                ann=own+ #ann a+ #ann b,ty=own}:profile
              val _=output_shape p
              val _=add(weight p) val _=port rng
              val _=future(1+weight p)
          in Term.mk_comb(f,x)end
        fun binary constant a b=application(application constant a)b
        fun equation a b=
          let val x=profile a val y=profile b
              val ty=Term.type_of a
              val _=if Type.compare(ty,Term.type_of b)=EQUAL then ()else
                fail "actual compact equality Type mismatch"
              val p={raw=3+ #raw x+ #raw y,inc=3+ #inc x+ #inc y,
                ann=6+3* #ty x+ #ann x+ #ann y,ty=1}:profile
              val _=output_shape p val _=add(weight p)
              (* Both actual equality operator Type ports are bounded
                 before their public Type constructors are called. *)
              val partial_weight=2+ #ty x
              val whole_weight=3+2* #ty x
              val _=add(partial_weight+whole_weight+1)
              val _=future(2+partial_weight+whole_weight)
              val partial=Type.-->(ty,Type.bool)
              val whole=Type.-->(ty,partial)
              fun retain wanted actual=
                if type_weight actual=wanted then
                  type_ports:=actual:: !type_ports
                else fail "actual equality Type port changed"
              val _=retain partial_weight partial
              val _=retain whole_weight whole
              val _=retain 1 Type.bool
              val _=future(1+weight p)
          in boolSyntax.mk_eq(a,b)end
        fun implication a b=binary boolSyntax.implication a b
        fun disjunction a b=binary boolSyntax.disjunction a b
        fun conjunction a b=binary boolSyntax.conjunction a b
        fun negation a=application boolSyntax.negation a
        fun root tree=case tree_view tree of ClauseFalse node=>node
          | ClauseLiteral{node,...}=>node | ClauseOr{node,...}=>node
        fun boolean node=
          let val term=named node
          in if Type.compare(Term.type_of term,Type.bool)=EQUAL then term
            else fail "actual clause node is not Boolean"end
        val observed_terms=ref([]:Term.term list)
        val verification=ref(0:IntInf.int)
        val operations=ref([]:
          (operation * model)list)
        val count=ref 0
        val dependencies=ref([]:'dependency list)
        fun expr(_,model:model)= #conclusion model
        fun hyps(_,model:model)= #hypotheses model
        fun index(i,_)=i
        fun emit operation conclusion hypotheses operands arguments=
          let val _=tick()val result=profile conclusion
              val native_rule=case operation of PRInput _=>false|_=>true
              val _=if native_rule then output_shape result
                else input_shape result
              val incoming=List.concat(List.map hyps operands)
              val introduced=List.filter(fn term=>not(member term incoming))
                hypotheses
              val measured=incoming @ introduced
              fun term_weight term=
                let val p=profile term val _=input_shape p
                in weight p end
              val operands_total=List.foldl(fn(value,total)=>
                total+term_weight(expr value))0 operands
              val arguments_total=List.foldl(fn(term,total)=>
                total+term_weight term)0 arguments
              val hypotheses_total=List.foldl(fn(term,total)=>
                total+term_weight term)0 measured
              val amount=1+weight result+operands_total+
                arguments_total+hypotheses_total
              val _=observed_terms:=conclusion::
                (measured @ arguments @ !observed_terms)
              val _=if native_rule then
                let val number=IntInf.fromInt(List.length measured)
                    val _=add amount
                    val largest=List.foldl(fn(term,total)=>
                      IntInf.max(total,weight(profile term)))0 measured
                    val comparisons=List.foldl(fn(term,total)=>
                      total+2+largest+weight(profile term))0 hypotheses
                    (* Actual fixed-rule Hyp comes only from incoming /
                       introduced Hyp, even on a model-check failure. *)
                    val _=verification:= !verification+2+2*weight result+
                      number*comparisons
                in future(amount+number*(number+2)+20)end
                else input_shape result
              val _=port(Term.type_of conclusion)
              val model={conclusion=conclusion,
                hypotheses=hypotheses}:model
              val slot= !count val _=count:=slot+1
              val _=operations:=(operation,model):: !operations
          in(slot,model)end
        fun borrowed edge=
          let val proof=theorem edge
              val conclusion=Native.concl proof
              val _=input_shape(profile conclusion)
              val _=if clean_using Native.tag proof andalso List.all(fn held=>
                  hypothesis held)(Native.hyp proof)then ()
                else fail "foreign compact input hypothesis"
              val dependency=dependency edge
              val _=dependencies:=dependency:: !dependencies
          in emit(PRInput proof)conclusion(Native.hyp proof)[][]end
        fun assume term=emit(PRAssume term)term[term][][term]
        fun reflexive term=emit(PRReflexive term)(equation term term)
          [][][term]
        fun reverse value=
          let val(a,b)=boolSyntax.dest_eq(expr value)
          in emit(PRReverse(index value))(equation b a)(hyps value)
            [value][]end
        fun compose a b=
          let val(x,middle)=boolSyntax.dest_eq(expr a)
              val(join,y)=boolSyntax.dest_eq(expr b)
              val _=if same middle join then ()else
                fail "compact equality middle changed"
          in emit(PRCompose(index a,index b))(equation x y)
            (union(hyps a)(hyps b))[a,b][]end
        fun apply_operator f value=
          let val(a,b)=boolSyntax.dest_eq(expr value)
          in emit(PRApplyOperator(f,index value))
            (equation(application f a)(application f b))(hyps value)
            [value][f]end
        fun apply_argument value x=
          let val(a,b)=boolSyntax.dest_eq(expr value)
          in emit(PRApplyArgument(index value,x))
            (equation(application a x)(application b x))(hyps value)
            [value][x]end
        fun combine a b=
          let val(f,g)=boolSyntax.dest_eq(expr a)
              val(x,y)=boolSyntax.dest_eq(expr b)
          in emit(PRCombine(index a,index b))
            (equation(application f x)(application g y))
            (union(hyps a)(hyps b))[a,b][]end
        fun equality_mp equality value=
          let val(a,b)=boolSyntax.dest_eq(expr equality)
              val _=if same a(expr value)then ()else
                fail "compact equality premise changed"
          in emit(PREqualityMP(index equality,index value))b
            (union(hyps equality)(hyps value))[equality,value][]end
        fun discharge term value=
          emit(PRDischarge(term,index value))(implication term(expr value))
            (List.filter(fn held=>not(same term held))(hyps value))
            [value][term]
        fun modus a b=
          let val(antecedent,result)=boolSyntax.dest_imp(expr a)
              val _=if same antecedent(expr b)then ()else
                fail "compact MP premise changed"
          in emit(PRModus(index a,index b))result
            (union(hyps a)(hyps b))[a,b][]end
        fun left value other=emit(PRLeft(index value,other))
          (disjunction(expr value)other)(hyps value)[value][other]
        fun right other value=emit(PRRight(other,index value))
          (disjunction other(expr value))(hyps value)[value][other]
        fun cases choice a b=
          let val(x,y)=boolSyntax.dest_disj(expr choice)
              val _=if same(expr a)(expr b)then ()else
                fail "compact case conclusions differ"
              val first=List.filter(fn term=>not(same term x))(hyps a)
              val second=List.filter(fn term=>not(same term y))(hyps b)
          in emit(PRCases(index choice,index a,index b))(expr a)
            (union(hyps choice)(union first second))[choice,a,b][]end
        fun not_elim value=
          let val term=boolSyntax.dest_neg(expr value)
          in emit(PRNotElim(index value))(implication term boolSyntax.F)
            (hyps value)[value][]end
        fun contradiction target value=
          let val _=if same(expr value)boolSyntax.F then ()else
                fail "compact contradiction is not F"
              val denied=negation target
          in emit(PRContradiction(target,index value))target
            (List.filter(fn held=>not(same held denied))(hyps value))
            [value][target,denied]end
        val constructor_memo=ref([]:('node*(int*model))list)
        fun constructor node=
          (tick();case List.find(fn(saved,_)=>
             (tick();same_node(saved,node)))(!constructor_memo)of
             SOME(_,value)=>value
           | NONE=>
             let val value=if Request.constructor_mode andalso
                     (case node_view node of NodeAtom=>true|_=>false)then
                       reflexive(named node)
                   else constructor_value node borrowed definition same
                     named node_view constant_term application compose
                     apply_argument constructor expr error
                 val _=constructor_memo:=(node,value):: !constructor_memo
             in value end)
        (* Only the opt-in raw path has aliases. The actual compact
           constructor equations prove the bridge; the alias table is DATA.
           Opaque leaves must retain their exact authentic identity. *)
        fun canonical node=
          let fun find []=(tick();node)
                | find((source,target)::rest)=
                    (tick();if same_node(source,node)then target
                     else find rest)
          in find aliases end
        val congruences=case aliases of []=>NONE | _=>
          (tick();tick();SOME(ref([]:
            ('node * 'node * (int*model))list)))
        fun congruent source target=
          let
            val _=tick()
            fun find []=NONE
              | find((left,right,value)::rest)=
                  (tick();if same_node(left,source) andalso
                       same_node(right,target) then SOME value
                   else find rest)
            val cache=case congruences of SOME cache=>cache | NONE=>
              fail "missing raw congruence cache"
          in case find(!cache)of SOME value=>value | NONE=>
            let
              val value=if same_node(source,target)then
                  reflexive(named source)
                else case(node_view source,node_view target)of
                    (NodeApplication(f,x),NodeApplication(g,y))=>
                      let val direct=borrowed(definition source)
                          val other=borrowed(definition target)
                          val middle=combine(congruent f g)(congruent x y)
                      in compose direct(compose middle(reverse other))end
                  | (NodeConstant,NodeConstant)=>
                      let val a=constant_term source
                          val b=constant_term target
                          val _=if same a b then ()else
                            fail "raw aliases have different constants"
                      in compose(borrowed(definition source))
                          (reverse(borrowed(definition target)))end
                  | _=>fail "raw aliases have different actual leaves"
              val(left,right)=boolSyntax.dest_eq(expr value)
              val _=if same left(named source) andalso
                  same right(named target)then ()else
                fail "raw congruence changed actual endpoints"
              val _=tick()val _=tick()val _=tick()
              val _=cache:=(source,target,value):: !cache
            in value end
          end
    in if Request.clause_mode then
          let val {premises,target,target_expanded,fallbacks}=
                Request.clause_input request
        fun atom node=
          if constant boolSyntax.T node orelse constant boolSyntax.F node
            then constructor node else case aliases of []=>
              reflexive(boolean node)
            | _=>congruent node(canonical node)
        fun bridge tree=
          (ignore(boolean(root tree));case tree_view tree of ClauseFalse node=>
              if constant boolSyntax.F node then constructor node else
                fail "false tree is not the actual F constructor"
            | ClauseLiteral{node,atom=actual,negative=false}=>
                if same_node(node,actual) then atom actual else
                  fail "positive occurrence has another actual node"
            | ClauseLiteral{node,atom=actual,negative=true}=>
                (case operator boolSyntax.negation 1 node of [held]=>
                   if same_node(held,actual) then compose(constructor node)
                     (apply_operator boolSyntax.negation(atom actual))
                   else fail "negative occurrence changed actual atom"
                 | _=>fail "negative occurrence arity changed")
            | ClauseOr{node,left=a,right=b}=>
                (case operator boolSyntax.disjunction 2 node of [x,y]=>
                   if same_node(x,root a) andalso same_node(y,root b) then
                     compose(constructor node)
                       (combine(apply_operator boolSyntax.disjunction
                         (bridge a))(bridge b))else
                       fail "recorded OR children changed"
                 | _=>fail "recorded OR arity changed"))
        val _=if null premises then fail "empty ordered resolution"else()
        fun input_clause{tree,edge}=
          let val value=borrowed edge
              val _=if Portable.pointer_eq(expr value,boolean(root tree))
                then ()else fail "edge is not this actual clause root"
              val equality=bridge tree
          in(tree,equality_mp equality value)end
        val inputs=List.map input_clause premises
        val target_bridge=bridge target
        val target_name=boolean(root target)
        val expanded=case target_expanded of NONE=>target|SOME tree=>
          if same_node(root tree,root target) then tree else
            fail "expanded target has another actual root"
        val expanded_bridge=bridge expanded
        val(_,wanted)=boolSyntax.dest_eq(expr expanded_bridge)
        val dictionary=ref([]:(Term.term*(int*model))list)
        fun put term value=
          dictionary:=(term,value)::List.filter(fn(saved,_)=>
            not(same term saved))(!dictionary)
        fun lookup term=case List.find(fn(saved,_)=>same term saved)
            (!dictionary)of NONE=>NONE|SOME(_,value)=>SOME value
        (* Target expansion never reclassifies a Source atom. The alias
           entry has an actual constructor proof at that exact target node. *)
        fun target_entries tree value=
          let val equality=bridge tree
              val(a,b)=boolSyntax.dest_eq(expr equality)
              val _=put b value
              val _=if same a b then ()else
                put a(modus(discharge b value)
                  (equality_mp equality(assume a)))
              val _=case aliases of []=>() | _=>
                let val node=root tree val canonical=canonical node
                in if same_node(node,canonical)then ()else
                  let val equality_to_actual=reverse(congruent node canonical)
                      val held=boolean canonical
                      val actual=equality_mp equality_to_actual(assume held)
                  in put held(modus(discharge b value)
                      (equality_mp equality actual))end
                end
          in case tree_view tree of ClauseOr{left=a,right=b,...}=>
               let val(_,l)=boolSyntax.dest_eq(expr(bridge a))
                   val(_,r)=boolSyntax.dest_eq(expr(bridge b))
                   val law=discharge(disjunction l r)value
               in target_entries a(modus law(left(assume l)r));
                  target_entries b(modus law(right l(assume r)))end
             | _=>()end
        val _=target_entries expanded(assume wanted)
        fun unit(tree,value)=
          let val _=case tree_view tree of ClauseOr _=>
                fail "non-unit ordered resolution premise"|_=>()
              val literal=expr value
              val negative=boolSyntax.is_neg literal
              val complement=if negative then boolSyntax.dest_neg literal
                else negation literal
              val counter=assume complement
              val impossible=if negative then
                  modus(not_elim value)counter
                else modus(not_elim counter)value
          in put complement(contradiction wanted impossible)end
        val _=List.app unit(List.tl inputs)
        val _=put boolSyntax.F(contradiction wanted(assume boolSyntax.F))
        fun selected_fallback node []=(tick();NONE)
          | selected_fallback node(tree::rest)=
              (tick();if same_node(root tree,node) then SOME tree
               else selected_fallback node rest)
        fun alias_lookup tree alias=
          case lookup alias of SOME value=>SOME value | NONE=>
            (case aliases of []=>NONE | _=>
              let val node=root tree val canonical=canonical node
              in if same_node(node,canonical)then NONE else
                case lookup(boolean canonical)of NONE=>NONE
                | SOME value=>
                    let val equality=congruent node canonical
                        val from_actual=equality_mp equality(assume alias)
                    in SOME(modus(discharge(boolean canonical)value)
                        from_actual)end
              end)
        fun solve tree=
          let val equality=bridge tree
              val(alias,expression)=boolSyntax.dest_eq(expr equality)
          in case lookup expression of SOME value=>value|NONE=>
            case alias_lookup tree alias of SOME value=>
              modus(discharge alias value)
                (equality_mp(reverse equality)(assume expression))
            | NONE=>case tree_view tree of ClauseOr{left=a,right=b,...}=>
                cases(assume expression)(solve a)(solve b)
              | ClauseLiteral{node,negative=false,...}=>
                if null fallbacks then
                  fail "ordered resolution leaves an unmatched literal"
                else(case selected_fallback node fallbacks of NONE=>
                    fail "ordered resolution leaves an unmatched literal"
                  | SOME expanded=>
                    (case tree_view expanded of ClauseOr _=>
                      let
                        (* Actual constructor association/Scope/Type is
                           checked by bridge, not inferred from key equality.
                           A shallow expansion is transported only on miss. *)
                        val constructor=bridge expanded
                        val(source,opened)=boolSyntax.dest_eq(expr constructor)
                        val _=if same source alias then ()else
                          fail "fallback names another actual source"
                        val actual=solve expanded
                      in modus(discharge opened actual)
                        (equality_mp constructor(assume expression))end
                    | _=>fail "fallback is not an actual OR tree"))
              | _=>fail "ordered resolution leaves an unmatched literal"end
        val(head,head_value)=List.hd inputs
        val raw_result=modus(discharge(expr head_value)(solve head))head_value
        val result=equality_mp(reverse expanded_bridge)raw_result
        (* Retain even absent-pivot inputs as real native Hyp operands and
           in the dependency DAG. Repeated Source occurrences stay ordered. *)
        fun retain((_,incoming),value)=
          let val joined=emit(PRJoin(index value,index incoming))
                (conjunction(expr value)(expr incoming))
                (union(hyps value)(hyps incoming))[value,incoming][]
          in emit(PRFirst(index joined))(expr value)(hyps joined)[joined][]end
        val final=List.foldl retain result inputs
        val _=if same(expr final)target_name andalso
            List.all(hypothesis)(hyps final)
          then ()else fail "final compact result or hypotheses changed"
        val _=ignore target_bridge
        val _=valid()
          in finish_preparation
                valid tick pay future profile weight port fail
                observed_terms verification operations
                dependencies type_ports index target_name final end
        else if Request.constructor_mode then
          let
              val node=Request.node_input request
              val final=constructor node
              val target_name=expr final
              val result_profile=profile target_name
              (* The extra final comparison is a fully bounded compact
                 comparison, included in the SAME naming/geometry quote.
                 No expanded query operand is reconstructed or matched. *)
              val _=verification:= !verification+2+2*weight result_profile
              val _=if List.all(hypothesis)(hyps final)then ()else
                fail "final constructor hypotheses changed"
              val _=valid()
          in finish_preparation
                valid tick pay future profile weight port fail
                observed_terms verification operations
                dependencies type_ports index target_name final end
        else
          let val(source,target)=Request.pair_input request
              val final=congruent source target
              val target_name=expr final
              val _=if List.all(hypothesis)(hyps final)then ()else
                fail "final compact equality hypotheses changed"
              val _=valid()
          in finish_preparation
                valid tick pay future profile weight port fail
                observed_terms verification operations
                dependencies type_ports index target_name final end
    end
  fun execute {guard=valid,check_type,error}
      (Plan {programme,final,target,dependencies,types}) =
    let
          val _=List.app(fn ty=>(valid();check_type ty;valid()))types
          val values=Array.array(Vector.length programme,NONE:Thm.thm option)
          fun proof index=case Array.sub(values,index)of SOME value=>value
            | NONE=>raise error "forward proof input"
          fun execute(index,(operation,model:model))=
            let val _=valid()
                val value=case operation of PRInput held=>Native.read held
                  | PRAssume term=>SmtReplayRuleObservation.ASSUME term
                  | PRReflexive term=>SmtReplayRuleObservation.REFL term
                  | PRReverse a=>SmtReplayRuleObservation.SYM(proof a)
                  | PRCompose(a,b)=>SmtReplayRuleObservation.TRANS
                      (proof a)(proof b)
                  | PRApplyOperator(term,a)=>SmtReplayRuleObservation.AP_TERM
                      term(proof a)
                  | PRApplyArgument(a,term)=>SmtReplayRuleObservation.AP_THM
                      (proof a)term
                  | PRCombine(a,b)=>SmtReplayRuleObservation.MK_COMB
                      (proof a,proof b)
                  | PREqualityMP(a,b)=>SmtReplayRuleObservation.EQ_MP
                      (proof a)(proof b)
                  | PRDischarge(term,a)=>SmtReplayRuleObservation.DISCH
                      term(proof a)
                  | PRModus(a,b)=>SmtReplayRuleObservation.MP
                      (proof a)(proof b)
                  | PRLeft(a,term)=>SmtReplayRuleObservation.DISJ1
                      (proof a)term
                  | PRRight(term,a)=>SmtReplayRuleObservation.DISJ2
                      term(proof a)
                  | PRCases(a,b,c)=>SmtReplayRuleObservation.DISJ_CASES
                      (proof a)(proof b)(proof c)
                  | PRNotElim a=>SmtReplayRuleObservation.NOT_ELIM(proof a)
                  | PRContradiction(term,a)=>SmtReplayRuleObservation.CCONTR
                      term(proof a)
                  | PRJoin(a,b)=>SmtReplayRuleObservation.CONJ
                      (proof a)(proof b)
                  | PRFirst a=>SmtReplayRuleObservation.CONJUNCT1(proof a)
                val _=valid()
                fun same a b=Portable.pointer_eq(a,b)orelse Term.aconv a b
                val _=if clean value andalso
                    same(Thm.concl value)(#conclusion model)andalso
                    List.all(fn term=>List.exists(fn held=>same term held)
                      (#hypotheses model))(Thm.hyp value)then ()else
                  raise error
                    "actual fixed rule result or hypotheses changed"
            in Array.update(values,index,SOME value)end
          val _=Vector.appi execute programme
          val result=proof final
          val _=if Request.same_final(Thm.concl result,target)then ()else
            raise error "named final pointer changed"
          val _=valid()
    in {theorem=result,dependencies=dependencies} end
end

functor SmtReplayClauseRequestFn(Native:SmtReplayNamedClauseInput) =
struct
  type input=Native.input
  type ('node,'tree,'edge,'dependency) operations =
    ('node,'tree,'edge,'dependency,input)
      SmtReplayNamedClauseSyntax.operations
  type ('node,'tree,'edge) request =
    {premises:{tree:'tree,edge:'edge} list,target:'tree,
     target_expanded:'tree option,fallbacks:'tree list}
  val clause_mode=true
  val constructor_mode=false
  val same_final=Portable.pointer_eq
  fun guard (ports:('node,'tree,'edge,'dependency) operations)=
    #guard ports
  fun tick (ports:('node,'tree,'edge,'dependency) operations)=
    #tick ports
  fun pay (ports:('node,'tree,'edge,'dependency) operations)=
    #pay ports
  fun future (ports:('node,'tree,'edge,'dependency) operations)=
    #future ports
  fun profile (ports:('node,'tree,'edge,'dependency) operations)=
    #profile ports
  fun type_weight (ports:('node,'tree,'edge,'dependency) operations)=
    #type_weight ports
  fun template (ports:('node,'tree,'edge,'dependency) operations)=
    #template ports
  fun metadata_template (ports:('node,'tree,'edge,'dependency) operations)=
    #metadata_template ports
  fun ceiling (ports:('node,'tree,'edge,'dependency) operations)=
    #ceiling ports
  fun hypothesis (ports:('node,'tree,'edge,'dependency) operations)=
    #hypothesis ports
  fun error (ports:('node,'tree,'edge,'dependency) operations)=
    #error ports
  fun tree_view (ports:('node,'tree,'edge,'dependency) operations)=
    #tree_view ports
  fun node_view (ports:('node,'tree,'edge,'dependency) operations)=
    #node_view ports
  fun same_node (ports:('node,'tree,'edge,'dependency) operations)=
    #same_node ports
  fun named (ports:('node,'tree,'edge,'dependency) operations)=
    #named ports
  fun constant (ports:('node,'tree,'edge,'dependency) operations)=
    #constant ports
  fun constant_term (ports:('node,'tree,'edge,'dependency) operations)=
    #constant_term ports
  fun operator (ports:('node,'tree,'edge,'dependency) operations)=
    #operator ports
  fun theorem (ports:('node,'tree,'edge,'dependency) operations)=
    #theorem ports
  fun definition (ports:('node,'tree,'edge,'dependency) operations)=
    #definition ports
  fun dependency (ports:('node,'tree,'edge,'dependency) operations)=
    #dependency ports
  fun clause_input value=value
  fun pair_input _=raise Fail "non-congruence request"
  fun node_input _=raise Fail "non-constructor request"
end

functor SmtReplayAtomCongruenceRequestFn(Native:SmtReplayNamedClauseInput) =
struct
  type input=Native.input
  type ('node,'tree,'edge,'dependency) operations =
    ('node,'edge,'dependency,input)
      SmtReplayNamedClauseSyntax.congruence_operations
  type ('node,'tree,'edge) request = 'node * 'node
  val clause_mode=false
  val constructor_mode=false
  fun same_final(actual,expected)=
    let val(a,b)=boolSyntax.dest_eq actual
        val(x,y)=boolSyntax.dest_eq expected
    in Portable.pointer_eq(a,x) andalso Portable.pointer_eq(b,y)end
  fun guard (ports:('node,'tree,'edge,'dependency) operations)=
    #guard ports
  fun tick (ports:('node,'tree,'edge,'dependency) operations)=
    #tick ports
  fun pay (ports:('node,'tree,'edge,'dependency) operations)=
    #pay ports
  fun future (ports:('node,'tree,'edge,'dependency) operations)=
    #future ports
  fun profile (ports:('node,'tree,'edge,'dependency) operations)=
    #profile ports
  fun type_weight (ports:('node,'tree,'edge,'dependency) operations)=
    #type_weight ports
  fun template (ports:('node,'tree,'edge,'dependency) operations)=
    #template ports
  fun metadata_template (ports:('node,'tree,'edge,'dependency) operations)=
    #metadata_template ports
  fun ceiling (ports:('node,'tree,'edge,'dependency) operations)=
    #ceiling ports
  fun hypothesis (ports:('node,'tree,'edge,'dependency) operations)=
    #hypothesis ports
  fun error (ports:('node,'tree,'edge,'dependency) operations)=
    #error ports
  fun tree_view _ _=raise Fail "non-clause request"
  fun node_view (ports:('node,'tree,'edge,'dependency) operations)=
    #node_view ports
  fun same_node (ports:('node,'tree,'edge,'dependency) operations)=
    #same_node ports
  fun named (ports:('node,'tree,'edge,'dependency) operations)=
    #named ports
  fun constant _ _ _=raise Fail "non-clause request"
  fun constant_term (ports:('node,'tree,'edge,'dependency) operations)=
    #constant_term ports
  fun operator _ _ _ _=raise Fail "non-clause request"
  fun theorem (ports:('node,'tree,'edge,'dependency) operations)=
    #theorem ports
  fun definition (ports:('node,'tree,'edge,'dependency) operations)=
    #definition ports
  fun dependency (ports:('node,'tree,'edge,'dependency) operations)=
    #dependency ports
  fun clause_input _=raise Fail "non-clause request"
  fun pair_input value=value
  fun node_input _=raise Fail "non-constructor request"
end

functor SmtReplayConstructorRequestFn(Native:SmtReplayNamedClauseInput) =
struct
  type input=Native.input
  type ('node,'tree,'edge,'dependency) operations =
    ('node,'edge,'dependency,input)
      SmtReplayNamedClauseSyntax.congruence_operations
  type ('node,'tree,'edge) request = 'node
  val clause_mode=false
  val constructor_mode=true
  fun same_final(actual,expected)=
    Portable.pointer_eq(actual,expected)orelse Term.aconv actual expected
  fun guard (ports:('node,'tree,'edge,'dependency) operations)=
    #guard ports
  fun tick (ports:('node,'tree,'edge,'dependency) operations)=
    #tick ports
  fun pay (ports:('node,'tree,'edge,'dependency) operations)=
    #pay ports
  fun future (ports:('node,'tree,'edge,'dependency) operations)=
    #future ports
  fun profile (ports:('node,'tree,'edge,'dependency) operations)=
    #profile ports
  fun type_weight (ports:('node,'tree,'edge,'dependency) operations)=
    #type_weight ports
  fun template (ports:('node,'tree,'edge,'dependency) operations)=
    #template ports
  fun metadata_template (ports:('node,'tree,'edge,'dependency) operations)=
    #metadata_template ports
  fun ceiling (ports:('node,'tree,'edge,'dependency) operations)=
    #ceiling ports
  fun hypothesis (ports:('node,'tree,'edge,'dependency) operations)=
    #hypothesis ports
  fun error (ports:('node,'tree,'edge,'dependency) operations)=
    #error ports
  fun tree_view _ _=raise Fail "non-clause request"
  fun node_view (ports:('node,'tree,'edge,'dependency) operations)=
    #node_view ports
  fun same_node (ports:('node,'tree,'edge,'dependency) operations)=
    #same_node ports
  fun named (ports:('node,'tree,'edge,'dependency) operations)=
    #named ports
  fun constant _ _ _=raise Fail "non-clause request"
  fun constant_term (ports:('node,'tree,'edge,'dependency) operations)=
    #constant_term ports
  fun operator _ _ _ _=raise Fail "non-clause request"
  fun theorem (ports:('node,'tree,'edge,'dependency) operations)=
    #theorem ports
  fun definition (ports:('node,'tree,'edge,'dependency) operations)=
    #definition ports
  fun dependency (ports:('node,'tree,'edge,'dependency) operations)=
    #dependency ports
  fun clause_input _=raise Fail "non-clause request"
  fun pair_input _=raise Fail "non-congruence request"
  fun node_input value=value
end

functor SmtReplayNamedClauseFn(Native:SmtReplayNamedClauseInput) =
struct
  open SmtReplayNamedClauseSyntax
  type ('node,'tree,'edge,'dependency) operations =
    ('node,'tree,'edge,'dependency,Native.input)
      SmtReplayNamedClauseSyntax.operations
  type ('node,'edge,'dependency) congruence_operations =
    ('node,'edge,'dependency,Native.input)
      SmtReplayNamedClauseSyntax.congruence_operations
  structure ClauseRequest=SmtReplayClauseRequestFn(Native)
  structure AtomRequest=SmtReplayAtomCongruenceRequestFn(Native)
  structure ConstructorRequest=SmtReplayConstructorRequestFn(Native)
  structure Clause=SmtReplayNamedClausePlanFn
    (structure Native=Native structure Request=ClauseRequest)
  structure Congruence=SmtReplayNamedClausePlanFn
    (structure Native=Native structure Request=AtomRequest)
  structure Constructor=SmtReplayNamedClausePlanFn
    (structure Native=Native structure Request=ConstructorRequest)
  datatype plan = datatype Clause.plan
  type 'dependency congruence_plan = 'dependency Congruence.plan
  type 'dependency constructor_plan = 'dependency Constructor.plan
  fun prepare operations options=Clause.prepare_using [] operations options
  fun prepare_with_atom_aliases aliases operations options=
    Clause.prepare_using aliases operations options
  val execute=Clause.execute
  (* The request is an authentic node pair, never a synthetic clause tree.
     Its nonempty alias list enables the SAME genuine congruence memo. *)
  fun prepare_atom_congruence operations pair=
    Congruence.prepare_using [pair] operations pair
  val execute_atom_congruence=Congruence.execute
  fun atom_congruence_dependencies
      (Congruence.Plan{dependencies,...})=dependencies
  fun prepare_constructor operations node=
    Constructor.prepare_using [] operations node
  val execute_constructor=Constructor.execute
  fun constructor_dependencies
      (Constructor.Plan{dependencies,...})=dependencies
  fun constructor_model(Constructor.Plan{programme,final,...})=
    #2(Vector.sub(programme,final))
  type 'node literal = {atom:'node,negative:bool}
  type ('node,'tree,'occurrence) discovery_operations =
    {node:'node -> unit,is_constant:Term.term -> 'node -> bool,
     operands:Term.term -> int -> 'node -> 'node list option,
     need_constructor:'node -> unit,same_node:'node * 'node -> bool,
     occurrence_node:'occurrence -> 'node,root:'tree -> 'node,
     clause_false:'node -> 'tree,
     clause_literal:{node:'node,atom:'node,negative:bool} -> 'tree,
     clause_or:{node:'node,left:'tree,right:'tree} -> 'tree,
     memo_semantic:'node -> (unit -> 'tree) -> 'tree,error:string -> exn}
  (* The recorded alias grammar and target-only expansion are shared.
     Observations retain the authentic caller's cursor/owner discipline. *)
  fun discover
      ({node,is_constant,operands,need_constructor,same_node,
        occurrence_node,root,clause_false,clause_literal,clause_or,
        memo_semantic,error}:('node,'tree,'occurrence) discovery_operations)=
    let
        fun literal_node value=
          let
              val _=node value
              val entry:'node literal=
                case operands boolSyntax.negation 1 value of
                  SOME[atom]=>
                    (node atom;need_constructor value;
                     {atom=atom,negative=true})
                | _=>{atom=value,negative=false}
              val _=if is_constant boolSyntax.T(#atom entry)orelse
                  is_constant boolSyntax.F(#atom entry)then
                    need_constructor(#atom entry)else()
          in(clause_literal{node=value,atom= #atom entry,
               negative= #negative entry},entry)end
        fun literal occurrence=
          literal_node(occurrence_node occurrence)
        fun recorded [] current=
              (node current;
               if is_constant boolSyntax.F current then
                 (need_constructor current;
                  (clause_false current,[]))else
                 raise error
                   "empty occurrence list is not the actual F node")
          | recorded [entry] current=
              let val(tree,value)=literal entry
              in if same_node(root tree,current) then(tree,[value])else
                raise error
                  "single occurrence has another actual root"end
          | recorded(entry::rest)current=
              let val _=node current
                  val(left,right)=case operands boolSyntax.disjunction 2
                      current of SOME[a,b]=>(a,b)
                    | _=>raise error
                        "recorded OR has no actual binary constructor"
                  val _=need_constructor current
                  val(a,value)=literal entry
                  val _=if same_node(root a,left) then ()else
                    raise error
                      "recorded literal differs from actual OR child"
                  val(b,values)=recorded rest right
              in(clause_or{node=current,left=a,right=b},
                 value::values)end
        fun semantic current=
          (node current;memo_semantic current(fn()=>
            case operands boolSyntax.disjunction 2 current of
                SOME[a,b]=>
                  (need_constructor current;clause_or
                    {node=current,left=semantic a,right=semantic b})
              | _=>if is_constant boolSyntax.F current then
                  (need_constructor current;clause_false current)
                else #1(literal_node current)))
    in {literal_node=literal_node,recorded=recorded,semantic=semantic} end
end
