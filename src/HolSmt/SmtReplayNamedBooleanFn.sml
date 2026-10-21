(* The actual checked Boolean programme, specialized by static proof
   observations and circuit workers. Abstract tokens alone confer no
   theorem, scoped closure, Source or native admission authority. *)
signature SmtReplayNamedBooleanNative =
sig
  type context
  type proof
  val default_context : context
  val concl : proof -> Term.term
  val hyp : proof -> Term.term list
  val tag : proof -> Tag.tag
  val truth : context -> proof
  val definition_cnf : context -> Term.term -> proof
  val balanced_equivalences : context -> proof list -> proof
  val refl : context -> Term.term -> proof
  val prove_cnf : context -> Term.term * Term.term -> proof
end

functor SmtReplayNamedBooleanFn (Native:SmtReplayNamedBooleanNative) =
struct
  datatype 'node view = Atom | Constant | Application of 'node * 'node
  (* Only authentic private edges enter the ordinary Upper adapter.
     Equation inputs need checked CNF conversion; clause inputs already
     carry the fixed producer's checked, properly clausified conclusion. *)
  datatype 'edge additional = Equation of 'edge | Clause of 'edge
  fun additional_edge(Equation edge)=edge
    | additional_edge(Clause edge)=edge
  type ('node,'edge) operations =
    {native:SmtReplayNativeContract.limits,
     spend:int -> unit,pay:IntInf.int -> unit,guard:unit -> unit,
     profile:Term.term -> SmtReplayNamedContext.profile,
     type_weight:Type.hol_type -> IntInf.int,
     type_of:'node -> Type.hol_type,view:'node -> 'node view,
     constant:'node -> Term.term,same:'node * 'node -> bool,
     name:'node -> Term.term,theorem:'edge -> Native.proof,
     constructor:'node -> 'edge,closed:Native.proof -> 'edge,
     equality_mp:'edge list -> 'edge,conjunction:'edge list -> 'edge,
     implication_mp:'edge list -> 'edge,error:string -> exn}
  (* Fully applied helpers create no per-call adapter/context box.
     Every new list visit and retained cons is observed by the SAME pay. *)
  fun equations_append pay [] tail=tail
    | equations_append pay(value::rest)tail=
        (pay 2;value::equations_append pay rest tail)
  fun equations_map pay action []=[]
    | equations_map pay action(value::rest)=
        (pay 2;action value::equations_map pay action rest)
  fun equations_quote pay amount []=pay 1
    | equations_quote pay amount(_::rest)=
        (pay(amount+1);equations_quote pay amount rest)

  (* The helper payer is int-valued. Each new wrapper helper invocation
     converts its amount through the existing same-Work spend adapter.
     Quote actual list visits and those future conversions with IntInf pay;
     no adapter closure or temporary list is constructed by this walk. *)
  fun wrapper_conversion_quote (pay:IntInf.int -> unit) amount []=pay 1
    | wrapper_conversion_quote pay amount(_::rest)=
        (pay amount;wrapper_conversion_quote pay amount rest)

  fun assemble_with_context_and_equations equations context
      (operations:('node,'edge) operations) {root,premises} =
    let val native= #native operations
    fun clean proof=null(Tag.axioms_of(Native.tag proof)) andalso
      List.all(fn oracle=>oracle="DISK_THM")
        (#1(Tag.dest_tag(Native.tag proof)))
    type primitive_profile=SmtReplayNamedContext.profile
    fun pp_spend n=
      (#spend operations) n
    fun pp_future n=(#pay operations) n
    fun pp_type_weight _ ty=
      (#type_weight operations) ty
    val inspect={profile=(#profile operations),
      cap=IntInf.fromInt(#template_limit(#semantic_limits native)),
      ceiling=IntInf.fromInt(#type_work_limit native)}
    val cap= #cap inspect val ceiling= #ceiling inspect
    fun valid ()=(#guard operations) ()
    fun invoke action=
      (valid ();let val value=action () val _=valid () in value end)
    fun pay n=pp_spend n
    val held_hyp_weight=ref(0:IntInf.int)
    fun admit(value:primitive_profile)=
      if #raw value<=cap andalso #inc value<=cap andalso
          #raw value+ #inc value+ #ann value+
            !held_hyp_weight+1<=ceiling then
        pp_future (#raw value+ #inc value+ #ann value+1)
      else raise (#error operations) "actual compact native operand cap"
    fun binary(a:primitive_profile)(b:primitive_profile)
          :primitive_profile=
      {raw=3+ #raw a+ #raw b,inc=3+ #inc a+ #inc b,
       ann=9+ #ann a+ #ann b,ty=1}
    val truth:primitive_profile={raw=1,inc=1,ann=1,ty=1}
    fun negative(a:primitive_profile):primitive_profile=
      {raw=2+ #raw a,inc=2+ #inc a,ann=4+ #ann a,ty=1}
    fun balanced []=truth | balanced [a]=a
      | balanced values=
          let val _=pay 1 val half=length values div 2
          in binary(balanced(List.take(values,half)))
               (balanced(List.drop(values,half))) end
    (* Borrow immutable public syntax; memoize physical nodes while
       retaining repeated-edge incidence. Schema variables are DATA. *)
    fun syntax require_owned replacements root =
      let val memo=ref([]:(Term.term*primitive_profile)list)
          fun lookup _ []=NONE
            | lookup term ((old,value)::rest)=
                (pay 1;if Portable.pointer_eq(term,old) then SOME value
                 else lookup term rest)
          fun replacement variable []=NONE
            | replacement variable ({redex,residue}::rest)=
                let val(a,t)=Term.dest_var variable
                    val(b,u)=Term.dest_var redex
                    val _=pay(String.size a+String.size b+1)
                    val x=pp_type_weight ceiling t
                    val y=pp_type_weight ceiling u
                    val _=pp_future (1+x+y)
                in if a=b andalso Type.compare(t,u)=EQUAL then
                  SOME residue else replacement variable rest end
          fun visit term=case lookup term (!memo) of SOME p=>p | NONE=>
            let val _=pay 1
                val own=pp_type_weight ceiling(Term.type_of term)
                val p:primitive_profile=if Term.is_var term then
                    (case replacement term replacements of
                        SOME value=> #profile inspect value
                      | NONE=>if require_owned then #profile inspect term
                        else {raw=1,inc=1,ann=own,ty=own})
                  else if Term.is_comb term then
                    let val(a,b)=Term.dest_comb term
                        val x=visit a val y=visit b
                    in {raw=1+ #raw x+ #raw y,
                        inc=1+ #inc x+ #inc y,
                        ann=own+ #ann x+ #ann y,ty=own} end
                  else if Term.is_const term then
                    {raw=1,inc=1,ann=own,ty=own}
                  else raise (#error operations) "noncompact binder schema"
                val _=if #raw p<=cap andalso #inc p<=cap andalso
                    #ann p<=ceiling then () else
                  raise (#error operations) "compact schema cap exceeded"
                val _=memo:=(term,p):: !memo
            in p end
      in visit root end
    fun boolean node=
      let val ty=(#type_of operations) node
          val _=pp_future (1+pp_type_weight ceiling ty)
      in Type.compare(ty,Type.bool)=EQUAL end
    fun endpoint(node,edge)=
      let val _=pay 2 val proof=(#theorem operations) edge
          val named=(#name operations) node
      in if Portable.pointer_eq(Native.concl proof,named) andalso
          boolean node then () else
        raise (#error operations) "incorrect named Boolean premise" end
    val target=(#name operations) root
    val _=if boolean root then () else
      raise (#error operations) "non-Boolean target"
    val _=List.app endpoint premises
    fun spine node arguments=
      (pay 1;case (#view operations) node of Application(f,x)=>
          spine f (x::arguments)
        | Constant=>SOME(node,arguments) | _=>NONE)
    fun gate node=case spine node [] of NONE=>NONE
      | SOME(head,args)=>
        let val term=(#constant operations) head
            fun constant wanted=Term.same_const term wanted
            val arity=length args
            val supported=(arity=0 andalso
                (constant boolSyntax.T orelse constant boolSyntax.F))
              orelse (arity=1 andalso constant boolSyntax.negation)
              orelse (arity=2 andalso
                (constant boolSyntax.conjunction orelse
                 constant boolSyntax.disjunction orelse
                 constant boolSyntax.implication orelse
                 constant boolSyntax.equality))
              orelse (arity=3 andalso constant boolSyntax.conditional)
        in if supported andalso List.all boolean args then SOME args
           else NONE end
    fun member _ []=false | member node (old::rest)=
      (pay 1;(#same operations) (node,old) orelse member node rest)
    fun discover [] _ result=List.rev result
      | discover(node::rest) seen result=
          (pay 1;if member node seen then discover rest seen result
           else case gate node of NONE=>discover rest(node::seen) result
             | SOME args=>discover(args@rest)(node::seen)(node::result))
    val gates=discover(root::List.map #1 premises) [] []
    val definitions=List.map ((#constructor operations)) gates
    val definition_proofs=List.map((#theorem operations)) definitions
    val facts=case equations of []=>
      List.map(fn(_,edge)=>(#theorem operations) edge) premises
    | _=>
      let
        (* Fresh observed reader and original-premise mapping lambda. *)
        val _=pay 2
        fun read edge=
          let
            val _=valid() val _=pay 2
            val proof=(#theorem operations)(additional_edge edge)
            val _=pay 2 val term=Native.concl proof
            val _=admit(#profile inspect term)
            val _=case edge of Equation _=>
              let
                (* Actual equation destructor and Boolean endpoint Types. *)
                val _=pay 5 val(a,b)=boolSyntax.dest_eq term
                val _=pay 6
                val ty_a=Term.type_of a val ty_b=Term.type_of b
                val own_a=pp_type_weight ceiling ty_a
                val own_b=pp_type_weight ceiling ty_b
                val _=pp_future(2+own_a+own_b)
              in if Type.compare(ty_a,Type.bool)=EQUAL andalso
                  Type.compare(ty_b,Type.bool)=EQUAL then ()else
                raise (#error operations) "non-Boolean atom equation"end
            | Clause _=>
              let val _=pay 3 val ty=Term.type_of term
                  val own=pp_type_weight ceiling ty
                  val _=pp_future(1+own)
              in if Type.compare(ty,Type.bool)=EQUAL then ()else
                raise (#error operations) "non-Boolean checked clause"end
            val _=valid()
          in proof end
        val original=equations_map pay(fn(_,edge)=>
          (pay 1;(#theorem operations)edge))premises
        val additional=equations_map pay read equations
      in equations_append pay original additional end
    fun law_for definition=
      let val body=boolSyntax.rhs definition
      in if boolSyntax.is_neg body then satTheory.dc_neg
         else if boolSyntax.is_conj body then satTheory.dc_conj
         else if boolSyntax.is_disj body then satTheory.dc_disj
         else if boolSyntax.is_imp body then satTheory.dc_imp
         else if boolSyntax.is_eq body andalso
             Type.compare(Term.type_of(boolSyntax.lhs body),Type.bool)
               =EQUAL then satTheory.dc_eq
         else if boolSyntax.is_cond body then satTheory.dc_cond
         else if Term.aconv body boolSyntax.T then SmtCircuitSat.true_cnf
         else if Term.aconv body boolSyntax.F then SmtCircuitSat.false_cnf
         else SmtCircuitSat.atom_cnf end
    fun forecast proof=
      let val definition=Native.concl proof
          val _=admit(#profile inspect definition)
          val source=Thm.concl(law_for definition)
          val _=admit(syntax false [] source)
          val(terms,types)=Term.match_term
            (boolSyntax.lhs source) definition
          val _=if null types then () else
            raise (#error operations) "non-Boolean CNF schema types"
          val full=syntax true terms source
          val cnf=syntax true terms (boolSyntax.rhs source)
          val _=admit full
      in cnf end
    val cnf_profiles=List.map forecast definition_proofs
    val def_profiles=List.map(#profile inspect o Native.concl)
      definition_proofs
    val named_profiles=case equations of []=>
      List.map(fn(node,_)=>
        #profile inspect((#name operations) node)) premises
    | _=>
      let
        (* Two new mapping closures; all actual visits/copies below. *)
        val _=pay 2
        val original=equations_map pay(fn(node,_)=>
          (pay 2;#profile inspect((#name operations)node)))premises
        val additional=equations_map pay
          (fn extra=>
            (pay 4;case extra of
                Equation edge=>forecast((#theorem operations)edge)
              | Clause edge=> #profile inspect
                  (Native.concl((#theorem operations)edge))))equations
      in equations_append pay original additional end
    val operands=definition_proofs@facts
    val hypotheses=List.concat(List.map Native.hyp operands)
    val incoming=List.map (#profile inspect) hypotheses
    val _=held_hyp_weight:=List.foldl
      (fn(p,total)=> #raw p+ #inc p+ #ann p+total) 0 incoming
    val _=List.app admit incoming
    (* The first MK_COMB yields a FUNCTION-typed equality. Its Type
       annotations need not be dominated by the final Bool equality. *)
    fun equivalences []=(admit(binary truth truth);(truth,truth))
      | equivalences [(a,b)]=(admit(binary a b);(a,b))
      | equivalences pairs=
          let val _=pay 1 val half=length pairs div 2
              val(a,c)=equivalences(List.take(pairs,half))
              val(b,d)=equivalences(List.drop(pairs,half))
              val partial:primitive_profile=
                {raw=7+ #raw a+ #raw c,inc=7+ #inc a+ #inc c,
                 ann=31+ #ann a+ #ann c,ty=1}
              val reflexive:primitive_profile=
                {raw=5,inc=5,ann=31,ty=1}
              val _=admit reflexive val _=admit partial
              val left=binary a b val right=binary c d
              val _=admit(binary left right)
          in (left,right) end
    val _=equivalences(ListPair.zip(def_profiles,cnf_profiles))
    val _=case equations of []=>
      equivalences(List.map(fn p=>(p,p))named_profiles)
    | _=>
      let
        (* Two actual mapping closures; field/tuple visits below. *)
        val _=pay 2
        val original=equations_map pay
          (fn(node,_)=>
            let val _=pay 3
                val p= #profile inspect((#name operations)node)
            in (p,p)end)premises
        val additional=equations_map pay
          (fn extra=>
            let val _=pay 6
                val proof=(#theorem operations)(additional_edge extra)
                val left= #profile inspect(Native.concl proof)
                val right=case extra of Equation _=>forecast proof
                  | Clause _=>left
            in pay 1;(left,right)end)equations
      in equivalences(equations_append pay original additional)end
    val annotation_portfolio=List.foldl
      (fn(p,total)=> #ann p+total)
      (#ann(balanced cnf_profiles)+ #ann(#profile inspect target))
      incoming
    val _=if annotation_portfolio<=ceiling then () else
      raise (#error operations) "native input/Hyp Type portfolio exceeded"
    val count=IntInf.fromInt(length hypotheses)
    val _=pp_future (count*(count+2)+20)
    (* Prepare the extra input-edge list before the circuit/native
       assembly. Empty specialization retains no list or new closure. *)
    val equation_antecedent=case equations of []=>[]
      | _=>
        let val _=pay 1
            val original=equations_map pay #2 premises
            val _=pay 1
            val extra=equations_map pay additional_edge equations
        in equations_append pay original extra end
    val equivalence=invoke(fn()=>(Native.balanced_equivalences context)
      (List.map((Native.definition_cnf context) o Native.concl)
        definition_proofs))
    val definition_cnf=boolSyntax.rhs(Native.concl equivalence)
    val fact_equivalence=case equations of []=>invoke(fn()=>
      (Native.balanced_equivalences context)(List.map
        (fn(node,_)=>(Native.refl context)((#name operations) node))
        premises))
    | _=>
      let
        (* Native future was admitted above by the SAME equivalences
           forecast, including each additional real equation profile. *)
        val _=pay 3
        (* Actual quotation visits plus prospective map/append cons and
           the extra edge/conclusion reads. No new pay follows a REFL. *)
        val _=equations_quote pay 4 premises
        val _=equations_quote pay 5 equations
      in invoke(fn()=>
          let val original=List.map
                (fn(node,_)=>Native.refl context
                  ((#name operations)node))premises
              val additional=List.map
                (fn extra=>case extra of
                    Equation edge=>Native.definition_cnf context
                      (Native.concl((#theorem operations)edge))
                  | Clause edge=>Native.refl context
                      (Native.concl((#theorem operations)edge)))equations
          in Native.balanced_equivalences context
            (original @ additional)end)end
    val fact_conjunction=case equations of []=>
      boolSyntax.lhs(Native.concl fact_equivalence)
    | _=>boolSyntax.rhs(Native.concl fact_equivalence)
    val future=if null facts then balanced cnf_profiles else
      binary(balanced cnf_profiles)(balanced named_profiles)
    val _=admit future
    val cnf=if null facts then definition_cnf else
      invoke(fn()=>boolSyntax.mk_conj(definition_cnf,fact_conjunction))
    val actual=syntax true [] cnf
    val _=if #raw actual= #raw future andalso
        #ann actual= #ann future then () else
      raise (#error operations) "actual CNF grammar differs"
    (* These are EXACT public prove_cnf wrapper constructors: flatten
       its actual CNF, add T/~F and ~target, then close implication.
       No bound on HolSat's private proof count/runtime is asserted. *)
    fun clauses [] result=List.rev result
      | clauses(term::rest) result=
        (pay 1;case Lib.total boolSyntax.dest_conj term of
            SOME(a,b)=>clauses(a::b::rest) result
          | NONE=>clauses rest(syntax true [] term::result))
    val clause_profiles=clauses [cnf] []
    val base_hyp_weight= !held_hyp_weight
    val denied_profile=negative(#profile inspect target)
    fun weight(p:primitive_profile)= #raw p+ #inc p+ #ann p
    (* ASSUME cnf / ASSUME denied create these exact additional H
       ports in the PUBLIC wrapper, before CCONTR/DISCH remove them. *)
    val _=held_hyp_weight:=weight actual+weight denied_profile
    val _=admit actual val _=admit denied_profile
    val _=List.app admit clause_profiles
    val refutation=List.foldr (fn(a,b)=>binary a b)
      denied_profile
      (clause_profiles@[truth,negative truth])
    val _=admit refutation
    val _=admit(negative refutation)
    val _=admit(binary refutation truth)
    val _=admit(binary actual (#profile inspect target))
    val implication=invoke(fn()=>(Native.prove_cnf context)(cnf,target))
    val _=held_hyp_weight:=base_hyp_weight
    val _=admit(#profile inspect target)
    val _=if null(Native.hyp implication) andalso clean implication then ()
      else raise (#error operations) "SAT implication is not closed"
    fun closed proof=(#closed operations) proof
    fun conjunction []=closed (Native.truth context)
      | conjunction [edge]=edge
      | conjunction edges=
          let val half=length edges div 2
          in (#conjunction operations)
            [conjunction(List.take(edges,half)),
             conjunction(List.drop(edges,half))] end
    val equivalence_edge=closed equivalence
    val implication_edge=closed implication
    val defined=conjunction definitions
    val def_proof=(#equality_mp operations) [equivalence_edge,defined]
    val antecedent=if null facts then def_proof else
      (#conjunction operations)
        [def_proof,case equations of []=>conjunction(List.map #2 premises)
          | _=> (#equality_mp operations)
              [closed fact_equivalence,conjunction equation_antecedent]]
    val result=(#implication_mp operations) [implication_edge,antecedent]
    val result_proof=(#theorem operations) result
    val _=if Portable.pointer_eq(Native.concl result_proof,target) andalso
        clean result_proof andalso
        List.all(fn term=>List.exists(fn held=>
          Portable.pointer_eq(term,held)) hypotheses)
          (Native.hyp result_proof)
      then () else raise (#error operations) "checked Boolean result changed"
    val _=valid ()
    in result end
  fun assemble_with_context context operations inputs =
    assemble_with_context_and_equations [] context operations inputs
  fun assemble operations inputs =
    assemble_with_context Native.default_context operations inputs
  fun assemble_with_equations [] operations inputs =
        assemble_with_context_and_equations [] Native.default_context
          operations inputs
    | assemble_with_equations equations
      (operations:('node,'edge) operations) inputs =
    let
      val _=(#guard operations)()
      (* Map callback, each variant/cons and actual traversal. *)
      val _=(#pay operations)1
      (* New payer selector1; each visit+one future conversion2. *)
      val _=(#pay operations)1
      val _=wrapper_conversion_quote (#pay operations)2 equations
      val additional=equations_map (#spend operations)
        (fn edge=>((#pay operations)1;Equation edge))equations
    in assemble_with_context_and_equations additional Native.default_context
      operations inputs end
  fun assemble_with_equations_and_clauses [] [] operations inputs =
        assemble_with_context_and_equations [] Native.default_context
          operations inputs
    | assemble_with_equations_and_clauses equations clauses
      (operations:('node,'edge) operations) inputs =
    let
      val _=(#guard operations)()
      val _=(#pay operations)2
      (* Payer selectors2. Each equality participates in map+append;
         each checked clause only in its map. Visits are additional work. *)
      val _=(#pay operations)2
      val _=wrapper_conversion_quote (#pay operations)3 equations
      val _=wrapper_conversion_quote (#pay operations)2 clauses
      val equalities=equations_map (#spend operations)
        (fn edge=>((#pay operations)1;Equation edge))equations
      val checked=equations_map (#spend operations)
        (fn edge=>((#pay operations)1;Clause edge))clauses
      val additional=equations_append (#spend operations)equalities checked
    in assemble_with_context_and_equations additional Native.default_context
      operations inputs end
end
