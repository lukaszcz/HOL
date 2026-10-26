(* Static metadata miss policy; no proof, Source or caller guard. *)
functor CPC_EqualityResolveMetadataFn(Choice:sig
  val retry_aliases:bool
  exception Correspondence of string
end) =
struct
  fun equality_resolve_using equality_provenance relation
      {node,pair,provenance,same,current,retry,error}
      premises =
    case premises of [first,second] =>
      let fun resolve final proposition equality =
            let
                (* Same original pair observation. In the alias-only
                   final attempt, inspect its genuine optional relation
                   directly so a missing pair has a private miss origin. *)
                val(left,right)=if Choice.retry_aliases andalso final then
                    (case relation(node equality)of SOME(_,pair)=>pair
                      | NONE=>raise Choice.Correspondence
                          "final premise is not a relation")
                  else pair(node equality)
                val (lp,rp)=equality_provenance(provenance equality)
            in if same(node proposition,left)then current right rp
              else if same(node proposition,right)then current left lp
              else if Choice.retry_aliases andalso final then
                raise Choice.Correspondence "ordered endpoints differ"
              else raise error "wrong equality side"end
      in resolve false first second
         handle primary as Feedback.HOL_ERR detail=>
           if retry detail then resolve true second first else
             raise primary end
    | _ => raise error "expected two premises"
end

(* SAME native CPC route and immediate indexed operand programme. *)
structure CPC_SharedReplayPlan :> CPC_SharedReplayPlan =
struct
  structure Q=CPC_ProofParser
  datatype route = Scoped | Resolved | Converted | Aligned | Simple | Bounded
  val boolean_handlers =
        ["bool","cnf","eq_resolve","contra","false_intro","false_elim",
         "true_intro","true_elim","and_intro","and_elim","not_or_elim",
         "not_not_elim","not_implies_elim1","not_implies_elim2",
         "implies_elim","not_and","equiv_elim1","equiv_elim2",
         "not_equiv_elim1","not_equiv_elim2","xor_elim1","xor_elim2",
         "not_xor_elim1","not_xor_elim2","ite_elim1","ite_elim2",
         "not_ite_elim1","not_ite_elim2","process_scope"]
  fun route {equal,visit,copies} {pop,handler} =
    let fun any []=false
          | any (allowed::rest)=
              (visit();equal(allowed,handler) orelse any rest)
    in if pop then Scoped
      else if equal(handler,"resolution") then Resolved
      else if equal(handler,"cnf") then Converted
      else if equal(handler,"factoring") orelse equal(handler,"reordering")
        then Aligned
      else if (copies 5;
          any (["refl","symm","trans","cong","ho_cong"] @
            boolean_handlers)) then Simple
      else Bounded
    end
  val native_route=route {equal=op =,visit=fn()=>(),copies=fn _=>()}
  datatype simple_boolean = SimpleAndIntro | SimpleAndElim
    | SimpleNotNotElim
    | SimpleNotOrElim
    | SimpleNotImpliesElim1
    | SimpleNotImpliesElim2
    | SimpleImpliesElim
    | SimpleEquivElim1
    | SimpleEquivElim2
    | SimpleNotEquivElim1
    | SimpleNotEquivElim2
    | SimpleIteElim1
    | SimpleIteElim2
    | SimpleNotAnd
  fun simple_boolean equal handler =
    if equal(handler,"and_intro") then SOME SimpleAndIntro
    else if equal(handler,"and_elim") then SOME SimpleAndElim
    else if equal(handler,"not_not_elim") then SOME SimpleNotNotElim
    else if equal(handler,"not_or_elim")then SOME SimpleNotOrElim
    else if equal(handler,"not_implies_elim1")then SOME SimpleNotImpliesElim1
    else if equal(handler,"not_implies_elim2")then SOME SimpleNotImpliesElim2
    else if equal(handler,"implies_elim")then SOME SimpleImpliesElim
    else if equal(handler,"equiv_elim1")then SOME SimpleEquivElim1
    else if equal(handler,"equiv_elim2")then SOME SimpleEquivElim2
    else if equal(handler,"not_equiv_elim1")then SOME SimpleNotEquivElim1
    else if equal(handler,"not_equiv_elim2")then SOME SimpleNotEquivElim2
    else if equal(handler,"ite_elim1")then SOME SimpleIteElim1
    else if equal(handler,"ite_elim2")then SOME SimpleIteElim2
    else if equal(handler,"not_and")then SOME SimpleNotAnd
    else NONE
  datatype simple_equality = SimpleRefl | SimpleSymm | SimpleTrans
    | SimpleCong | SimpleHoCong | SimpleEqResolve | SimpleContra
  fun simple_equality equal handler =
    if equal(handler,"refl")then SOME SimpleRefl
    else if equal(handler,"symm")then SOME SimpleSymm
    else if equal(handler,"trans")then SOME SimpleTrans
    else if equal(handler,"cong")then SOME SimpleCong
    else if equal(handler,"ho_cong")then SOME SimpleHoCong
    else if equal(handler,"eq_resolve")then SOME SimpleEqResolve
    else if equal(handler,"contra")then SOME SimpleContra
    else NONE
  fun equality_provenance (CPC_Proof.EqualityProvenance pair) = pair
    | equality_provenance
        (CPC_Proof.ApplicationProvenance("=",[left,right])) = (left,right)
    | equality_provenance _ =
        (CPC_Proof.AtomicProvenance,CPC_Proof.AtomicProvenance)
  fun reflexive {require_one,relation} arguments =
    let val node=require_one "refl" arguments in relation node node end
  fun positive_symmetry
      {pair,one,one_provenance,relation_kind,relation_with_kind} =
    let val (left,right)=pair(one())
        val (left_prov,right_prov)=equality_provenance(one_provenance())
    in relation_with_kind(relation_kind(one()))right left
      (right_prov,left_prov)end
  fun higher_congruence {map,pair,application,relation,error} premises =
    case map pair premises of
      [(left,right),(operand,replacement)] => relation
        (application(left,operand))(application(right,replacement))
    | _ => raise error "expected operator and operand equalities"
  exception AliasCorrespondence of string
  structure StrictEqualityResolve=CPC_EqualityResolveMetadataFn(struct
    val retry_aliases=false
    exception Correspondence of string
  end)
  structure AliasEqualityResolve=CPC_EqualityResolveMetadataFn(struct
    val retry_aliases=true
    exception Correspondence=AliasCorrespondence
  end)
  fun no_relation _=NONE
  fun equality_resolve operations premises=
    StrictEqualityResolve.equality_resolve_using equality_provenance
      no_relation operations premises
  fun equality_resolve_with_aliases relation operations premises=
    AliasEqualityResolve.equality_resolve_using equality_provenance
      relation operations premises
  (* Same native declared-target graph search. Keys are supplied only as
     local visited DATA; endpoint equality is always supplied separately. *)
  fun relation_path {visit,relation,map_partial,same_kind,same,key,
      empty,member,add,push,fold,error} target premises =
    let val _=visit()
        val (kind,(left,right))=case relation target of SOME pair=>pair
          | NONE=>raise error "declared target is not a relation"
        val edges=map_partial(fn incoming=>
          (visit();case relation incoming of SOME(actual,pair)=>
             if same_kind(actual,kind)then SOME pair else NONE
           | NONE=>NONE))premises
        fun search [] _=false
          | search(current::pending)seen=
              (visit();if same(current,right)then true
               else if member(seen,key current)then search pending seen
               else let val seen=add(seen,key current)
                        val next=fold(fn((a,b),rest)=>
                          (visit();if same(a,current)then push(b,rest)
                           else if same(b,current)then push(a,rest)else rest))
                          pending edges
                    in search next seen end)
    in search(push(left,[]))(empty())end
  (* This is the original replacement-first, then memo, App-only rewrite.
     The Value specialization returns constructor DATA instead of syntax;
     it must match that DATA against its authentic declared target. *)
  fun congruence_rewrite {replacement,lookup,publish,view,retained,same,
      application} =
    let fun rewrite source=case replacement source of SOME target=>target
          | NONE=>case lookup source of SOME target=>target
            | NONE=>let val target=case view source of
                  SOME(operator,operand)=>
                    let val operator'=rewrite operator
                        val operand'=rewrite operand
                    in if same(operator,operator') andalso
                        same(operand,operand')then retained source
                      else application(operator',operand')end
                | NONE=>retained source
                val _=publish(source,target)
              in target end
    in rewrite end
  open CPC_Proof
  fun conjunction {visit,truth,binary} nodes =
    let fun build [] = (visit();truth())
          | build [node] = (visit();node)
          | build (node::rest) = (visit();binary(node,build rest))
    in build nodes end
  fun child_provenance {equal,length,tabulate} token count provenance =
    case provenance of
      ApplicationProvenance(head,children) =>
        if equal(head,token) andalso length children=count then children
        else tabulate(count,fn _=>AtomicProvenance)
    | _ => tabulate(count,fn _=>AtomicProvenance)
  fun disjoin {visit,falsity,atom,current,binary,provenances} entries =
    case entries of [] => (visit();atom(falsity()))
      | [(node,provenance)] => (visit();current node provenance)
      | entries =>
          let fun build [(node,_)] = (visit();node)
                | build ((node,_)::rest) = (visit();binary(node,build rest))
                | build [] = raise Fail "empty recorded disjunction"
          in current (build entries)
            (ApplicationProvenance("or",provenances entries))end
  (* SAME recorded aggregate and produced-AND programmes. Callers supply
     actual owned syntax and observation/copy tariffs, never proof flags. *)
  fun aggregate_entries
      {children,recorded,length,push,reverse,start,initial,check,error}
      node provenance =
    let
      val _ = case children provenance of SOME _ => ()
        | NONE => raise error "aggregate lacks recorded operand boundaries"
      fun walk [] _ result = reverse result
        | walk ((node,provenance)::pending) count result =
            (check count;
             case children provenance of
                 NONE => walk pending (count+1)
                   (push {node=node,provenance=provenance} result)
               | SOME entries =>
                   (case recorded (length entries) node of
                      SOME nodes => walk
                        (start (nodes,entries,pending)) (count+1) result
                    | NONE => raise error
                        "recorded aggregate constructor differs"))
    in walk (initial (node,provenance)) 0 [] end
  fun produced_conjunction
      {run,observe,input,recorded,same,children,validate,check,
       pending,leaf,reverse,initial} body = run (fn () =>
    let
      val _ = observe ()
      val input = input ()
      val signed = case input of NONE => false
        | SOME layout =>
            (observe ();
             case recorded layout of
               [{atom,negative}] => negative andalso same (atom,body)
             | _ => false)
      val _ = observe ()
      val root_children = children body
      fun walk [] _ result = reverse result
        | walk (current::rest) count result =
            let
              val _ = observe ()
              val _ = validate current
              val _ = check count
              val nested = children current
            in case nested of SOME [left,right] =>
                 walk (pending (left,right,rest)) (count+1) result
               | _ => walk rest (count+1)
                   (leaf (current,AtomicProvenance,result)) end
    in if signed andalso Option.isSome root_children then
         SOME (walk (initial body) 0 []) else NONE end)
  fun not_and
      {negated,one,one_provenance,negation_provenance,operands,is_false,
       child_provenance,recorded_entries,owned,produced_entries,
       map,negative,disjoin,error} =
    let
      val (body,provenance) = case negated (one ()) of
          SOME body => (body,negation_provenance (one_provenance ()))
        | NONE =>
            let val [body,result] = operands boolSyntax.implication 2 (one ())
                val _ = if is_false result then () else
                  raise error "implication consequent differs from F"
                val [body_prov,_] = child_provenance "=>" 2
                  (one_provenance ())
            in (body,body_prov) end
      fun recorded () = recorded_entries body provenance
      val entries = case provenance of
          ConjunctionProvenance _ => recorded ()
        | ApplicationProvenance ("and",_) => recorded ()
        | _ => (case owned of NONE => recorded ()
            | SOME owner => case produced_entries owner body of
                SOME entries => entries | NONE => recorded ())
    in disjoin (map (fn (node,provenance) =>
      negative node provenance) entries) end
  (* Exact native registered-CNF signed occurrence programme. The
     callbacks keep actual constructor/provenance validation and, for XOR,
     the genuine checked definition proof. This function grants no Source. *)
  fun cnf_literals binary_nodes indexed aggregate xor_nodes ite_nodes
      positive negative map error rule whole =
    case rule of
      "cnf_implies_neg1" =>
        let val (a,_) = binary_nodes boolSyntax.implication
        in [positive a,positive whole] end
    | "cnf_implies_neg2" =>
        let val (_,b) = binary_nodes boolSyntax.implication
        in [negative b,positive whole] end
    | "cnf_implies_pos" =>
        let val (a,b) = binary_nodes boolSyntax.implication
        in [negative a,positive b,negative whole] end
    | "cnf_and_pos" => [positive
        (indexed boolSyntax.conjunction "and"),negative whole]
    | "cnf_and_neg" => positive whole :: map negative
        (aggregate boolSyntax.conjunction "and")
    | "cnf_or_neg" => [positive whole,negative
        (indexed boolSyntax.disjunction "or")]
    | "cnf_or_pos" => negative whole :: map positive
        (aggregate boolSyntax.disjunction "or")
    | "cnf_equiv_neg1" =>
        let val (a,b) = binary_nodes boolSyntax.equality
        in [positive a,positive b,positive whole] end
    | "cnf_equiv_neg2" =>
        let val (a,b) = binary_nodes boolSyntax.equality
        in [negative a,negative b,positive whole] end
    | "cnf_equiv_pos1" =>
        let val (a,b) = binary_nodes boolSyntax.equality
        in [negative a,positive b,negative whole] end
    | "cnf_equiv_pos2" =>
        let val (a,b) = binary_nodes boolSyntax.equality
        in [positive a,negative b,negative whole] end
    | "cnf_xor_pos1" => let val (a,b) = xor_nodes ()
        in [negative whole,positive a,positive b] end
    | "cnf_xor_pos2" => let val (a,b) = xor_nodes ()
        in [negative whole,negative a,negative b] end
    | "cnf_xor_neg1" => let val (a,b) = xor_nodes ()
        in [positive whole,negative a,positive b] end
    | "cnf_xor_neg2" => let val (a,b) = xor_nodes ()
        in [positive whole,positive a,negative b] end
    | "cnf_ite_pos1" => let val (c,a,_) = ite_nodes ()
        in [negative whole,negative c,positive a] end
    | "cnf_ite_pos2" => let val (c,_,b) = ite_nodes ()
        in [negative whole,positive c,positive b] end
    | "cnf_ite_pos3" => let val (_,a,b) = ite_nodes ()
        in [negative whole,positive a,positive b] end
    | "cnf_ite_neg1" => let val (c,a,_) = ite_nodes ()
        in [positive whole,negative c,negative a] end
    | "cnf_ite_neg2" => let val (c,_,b) = ite_nodes ()
        in [positive whole,positive c,negative b] end
    | "cnf_ite_neg3" => let val (_,a,b) = ite_nodes ()
        in [positive whole,negative a,negative b] end
    | _ => raise error "cnf" "unsupported registered CNF producer"
  (* These are the actual native four truth-family decisions. All
     callbacks are fully applied: no native per-call adapter is allocated.
     'retain' is static identity in the native instance; Value uses Held. *)
  fun false_intro negated observed one retain constant graph scope
      negation_provenance one_provenance relation_with error =
    relation_with
      (retain(case negated observed(one())of SOME body=>body
        | NONE=>raise error "false_intro" "expected negated premise"))
      (constant graph scope boolSyntax.F)
      (negation_provenance(one_provenance()),CPC_Proof.AtomicProvenance)
  fun false_elim pair one equality_provenance one_provenance
      same_constant graph negative current error =
    let val(left,right)=pair(one())
        val(left_prov,right_prov)=equality_provenance(one_provenance())
    in if same_constant graph right boolSyntax.F then
        let val(node,provenance)=negative left left_prov
        in current node provenance end
      else if same_constant graph left boolSyntax.F then
        let val(node,provenance)=negative right right_prov
        in current node provenance end
      else raise error "false_elim" "expected false equality"end
  fun true_intro one retain constant graph scope one_provenance
      relation_with =
    relation_with(retain(one()))(constant graph scope boolSyntax.T)
      (one_provenance(),CPC_Proof.AtomicProvenance)
  fun true_elim pair one equality_provenance one_provenance
      same_constant graph retain current error =
    let val(left,right)=pair(one())
        val(left_prov,right_prov)=equality_provenance(one_provenance())
    in if same_constant graph right boolSyntax.T then
        current(retain left)left_prov
      else if same_constant graph left boolSyntax.T then
        current(retain right)right_prov
      else raise error "true_elim" "expected true equality"end

  (* Static native no-op; Value observes the actual tuple/cons copies.
     Passing this existing global function allocates no native thunk. *)
  fun no_metadata_copy _=()
  fun process_scope_entries visible same operands graph reverse copies
      target node provenance entries =
    (visible node;
     if same(node,target)then SOME(reverse entries)else
       case(operands graph boolSyntax.implication 2 node,provenance)of
         (SOME[antecedent,consequent],
          CPC_Proof.ApplicationProvenance("=>",[left,right]))=>
           (visible antecedent;copies 3;
            process_scope_entries visible same operands graph reverse copies
              target consequent right((antecedent,left)::entries))
       | _=>NONE)

  fun and_intro {conjunction,provenances,current} nodes =
    current (conjunction nodes)
      (ConjunctionProvenance(AndIntroConjunction,provenances()))
  fun not_not_elim
      {negated,one,one_provenance,negation_provenance,current,error} =
    case negated(one())of SOME inner =>
      (case negated inner of SOME body => current body
         (negation_provenance(negation_provenance(one_provenance())))
       | NONE => raise error "expected double negation")
    | NONE => raise error "expected double negation"
  structure S=SmtLib_Parser
  fun occurrence_provenance_observed observe root =
    let
      val current = ref root
      val saved = ref (Redblackmap.mkDict
        (fn (a,b) => (observe (!current);Int.compare (a,b))))
      fun visit (whole as S.ConstructionOccurrence
          {role,token,children,...}) =
        let
          val _ = observe whole
          fun nested () = List.map visit children
          fun reference stamp =
            let
              (* Charge dictionary comparisons through the same observer;
                 a shared proof let must not expand its occurrence DAG. *)
              val _ = current := whole
            in case Redblackmap.peek (!saved,stamp) of
                SOME provenance => provenance
              | NONE =>
                  let val provenance = case nested () of
                          [body] => body
                        | _ => UnavailableProvenance
                            "invalid occurrence reference"
                      val _ = current := whole
                      val _ = saved := Redblackmap.insert
                        (!saved,stamp,provenance)
                  in provenance end
            end
        in case role of
            S.ConstructionReference stamp => reference stamp
          | S.ConstructionApplication =>
              let val nested = nested () in
                if token = "and" then ConjunctionProvenance
                  (ParsedConjunction,nested)
                else if token = "=" andalso List.length nested = 2 then
                  EqualityProvenance (hd nested,List.last nested)
                else ApplicationProvenance (token,nested)
              end
          | S.ConstructionBinder {kind,variables} =>
              BinderBlockProvenance (kind,List.length variables,
                case List.rev (nested ()) of body::_ => body
                  | [] => UnavailableProvenance "missing binder body")
          | S.ConstructionLet _ =>
              (case List.rev (nested ()) of body::_ => body
                | [] => UnavailableProvenance "missing let body")
          | S.ConstructionAnnotation =>
              (case nested () of [body] => body
                | _ => UnavailableProvenance "invalid annotation boundary")
          | _ => AtomicProvenance
        end
    in visit root end
  fun occurrence_provenance occurrence=
    occurrence_provenance_observed(fn _=>())occurrence
  fun recorded_observed observe operands operator count root =
    (observe();if count < 1 then NONE else
    let fun walk 1 node = (observe();SOME [node])
          | walk count node =
              (observe();case operands operator 2 node of
                SOME [left,right] => Option.map
                  (fn rest => (observe();left::rest))
                  (walk (count-1) right)
              | _ => NONE)
    in walk count root end)
  fun recorded operands operator count root=
    recorded_observed(fn()=>())operands operator count root
  fun selected {children,recorded,length,node_at,provenance_at,error}
      operator source provenance index =
    let val provenance_children=children provenance
        val count=length provenance_children
        val nodes=case recorded operator count source of SOME nodes=>nodes
          | NONE=>raise error "invalid operand boundary"
    in (node_at(nodes,index),provenance_at(provenance_children,index))
      handle Subscript=>raise error "operand index out of range"
    end
  fun not_or_elim
      {require_one,node,negated,provenance,selected,index,negate,current,
       error} premises =
    let val premise = require_one "not_or_elim" premises
        val body = case negated (node premise) of
            SOME body => body
          | NONE => raise error "not_or_elim" "expected negation"
        val provenance = case provenance premise of
            ApplicationProvenance ("not",[body]) => body
          | _ =>
            raise error "not_or_elim" "missing negated OR boundary"
        val (selected,provenance) = selected
          boolSyntax.disjunction body provenance (index ())
    in current (negate selected)
      (ApplicationProvenance ("not",[provenance])) end
  fun not_implies_elim1
      {negated,one,operands,child_provenance,negation_provenance,
       one_provenance,current,error} handler =
    let val implication = case negated (one ()) of
            SOME body => body
          | NONE => raise error handler "expected negation"
        val [left,_] = operands boolSyntax.implication
          2 implication
        val [left_prov,_] = child_provenance "=>" 2
          (negation_provenance (one_provenance ()))
    in current left left_prov end
  fun not_implies_elim2
      {negated,one,operands,child_provenance,negation_provenance,
       one_provenance,negative,finish,error} handler =
    let val implication = case negated (one ()) of
            SOME body => body
          | NONE => raise error handler "expected negation"
        val [_,right] = operands boolSyntax.implication
          2 implication
        val [_,right_prov] = child_provenance "=>" 2
          (negation_provenance (one_provenance ()))
        val (node,provenance) = negative right right_prov
    in finish (node,provenance) end
  fun implies_elim
      {operands,one,child_provenance,one_provenance,negative,positive,
       disjoin} =
    let val [left,right] = operands
          boolSyntax.implication 2 (one ())
        val [left_prov,right_prov] =
          child_provenance "=>" 2 (one_provenance ())
    in disjoin [negative left left_prov,
                positive right right_prov] end
  fun equiv_elim1
      {one,pair,one_provenance,negative,positive,disjoin} =
    let val (left,right) = pair (one ())
        val (left_prov,right_prov) =
          equality_provenance (one_provenance ())
    in disjoin [negative left left_prov,
                positive right right_prov] end
  fun equiv_elim2
      {one,pair,one_provenance,negative,positive,disjoin} =
    let val (left,right) = pair (one ())
        val (left_prov,right_prov) =
          equality_provenance (one_provenance ())
    in disjoin [positive left left_prov,
                negative right right_prov] end
  fun not_equiv_elim1
      {negated,one,pair,one_provenance,negation_provenance,negative,positive,
       disjoin,error} handler =
    let val equation = case negated (one ()) of
            SOME body => body
          | NONE => raise error handler "expected negation"
        val (left,right) = pair equation
        val (left_prov,right_prov) = equality_provenance
          (negation_provenance (one_provenance ()))
    in disjoin [positive left left_prov,
                positive right right_prov] end
  fun not_equiv_elim2
      {negated,one,pair,one_provenance,negation_provenance,negative,positive,
       disjoin,error} handler =
    let val equation = case negated (one ()) of
            SOME body => body
          | NONE => raise error handler "expected negation"
        val (left,right) = pair equation
        val (left_prov,right_prov) = equality_provenance
          (negation_provenance (one_provenance ()))
    in disjoin [negative left left_prov,
                negative right right_prov] end
  fun ite_elim1
      {same_constant,one,atom,operands,child_provenance,one_provenance,
       negative,positive,disjoin} =
    if same_constant (one ()) boolSyntax.T then
      atom (one ()) else
    let val [condition,yes,_] = operands
          boolSyntax.conditional 3 (one ())
        val [condition_prov,yes_prov,_] =
          child_provenance "ite" 3 (one_provenance ())
    in disjoin [negative condition condition_prov,
                positive yes yes_prov] end
  fun ite_elim2
      {same_constant,one,atom,operands,child_provenance,one_provenance,
       negative,positive,disjoin} =
    if same_constant (one ()) boolSyntax.T then
      atom (one ()) else
    let val [condition,_,no] = operands
          boolSyntax.conditional 3 (one ())
        val [condition_prov,_,no_prov] =
          child_provenance "ite" 3 (one_provenance ())
    in disjoin [positive condition condition_prov,
                positive no no_prov] end
  fun and_elim {require_one,node,provenance,selected,current,error}
      premises arguments =
    let val premise=require_one "and_elim" premises
        fun index()=case arguments of [Q.GraphIndex index]=>index
          | _=>raise error "expected one recorded index"
        val(result,origin)=selected boolSyntax.conjunction
          (node premise)(provenance premise)(index())
    in current result origin end

  (* Signed occurrence algorithms only. No equality, theorem or Source is
     inferred from the supplied syntax/provenance observations. *)
  fun erase_present same option_map recurse literal head rest =
    if same literal head then SOME rest
    else option_map(fn tail=>head::tail)(recurse literal rest)
  fun resolution_join erase opposite append error where_ left right pivot =
    case(erase pivot left,erase(opposite pivot)right)of
        (SOME left,SOME right)=>append(left,right)
      | _=>raise error where_ "pivot is absent from recorded clauses"
  fun resolution_dynamic find exists same opposite error left right =
    case find(fn literal=>exists(same(opposite literal))right)left of
        SOME pivot=>pivot
      | NONE=>raise error "resolution" "no complementary recorded pivot"
  fun resolution_chain join dynamic reverse recurse error
      current remaining annotations pivots =
    case(remaining,annotations)of
        ([],[]) =>(current,reverse pivots)
      | (next::rest,[])=>
          let val pivot=dynamic current next
          in recurse(join current next pivot)rest[](pivot::pivots)end
      | (next::rest,pivot::pending)=>
          recurse(join current next pivot)rest pending(pivot::pivots)
      | _=>raise error "resolution" "wrong pivot count"
  fun recorded_resolution_chain observe join recurse error
      current remaining annotations =
    case(remaining,annotations)of
        ([],[])=>current
      | (next::rest,pivot::pending)=>
          (observe();recurse(join current next pivot)rest pending)
      | _=>raise error "chain_m_resolution" "recorded chain length differs"

  fun pivot_arguments length map_eq same_constant environment convert error
      (arguments:'syntax Q.constructed_graph_argument list) =
    case arguments of
        [Q.GraphList polarities,Q.GraphList atoms]=>
          if length polarities=length atoms then
            map_eq(fn(polarity,atom)=>case(polarity,atom)of
                (Q.GraphTerm polarity,Q.GraphTerm atom)=>
                  if same_constant environment(#node polarity)boolSyntax.T
                  then {atom=convert(#node atom),negative=false}
                  else if same_constant environment(#node polarity)
                      boolSyntax.F then
                    {atom=convert(#node atom),negative=true}
                  else raise error "resolution" "non-Boolean pivot polarity"
              | _=>raise error "resolution" "non-term pivot annotation")
              (polarities,atoms)
          else raise error "resolution" "pivot annotation lengths differ"
      | Q.GraphTerm polarity::Q.GraphTerm atom::_=>
          if same_constant environment(#node polarity)boolSyntax.T then
            [{atom=convert(#node atom),negative=false}]
          else if same_constant environment(#node polarity)boolSyntax.F then
            [{atom=convert(#node atom),negative=true}]
          else raise error "resolution" "non-Boolean pivot polarity"
      | []=>[]
      | _=>raise error "resolution" "unsupported recorded pivot annotation"
  fun recorded_pivot observe same_constant type_of environment convert
      negated error (polarity,pivot) =
    case(polarity,pivot)of
        (Q.GraphTerm polarity,Q.GraphTerm pivot)=>
          let
            val _=observe()
            val positive=if same_constant environment(#node polarity)
                boolSyntax.T then true
              else if same_constant environment(#node polarity)boolSyntax.F
                then false
              else raise error "chain_m_resolution"
                "non-Boolean recorded polarity"
            val _=if Type.compare(type_of environment(#node pivot),
                Type.bool)=EQUAL then ()else
              raise error "chain_m_resolution" "non-Boolean recorded pivot"
          in case negated environment(convert(#node pivot))of SOME atom=>
               {atom=atom,negative=positive}
             | NONE=>{atom=convert(#node pivot),negative=not positive}end
      | _=>raise error "chain_m_resolution" "non-term recorded pivot entry"
end
