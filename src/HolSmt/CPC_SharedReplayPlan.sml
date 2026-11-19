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
  val ERR = Feedback.mk_HOL_ERR "CPC_SharedReplayPlan"
  (* Recorded operand and provenance lists have the requested arity. *)
  fun pair_of _ [a,b] = (a,b)
    | pair_of rule _ = raise ERR rule "unexpected operand arity"
  fun triple_of _ [a,b,c] = (a,b,c)
    | triple_of rule _ = raise ERR rule "unexpected operand arity"
  structure Q=CPC_ProofParser
  structure P=CPC_Proof
  datatype route = Scoped | Resolved | Converted | Aligned | Simple | Bounded
  datatype clausal_rule = NotImpliesElim1 | NotImpliesElim2 | ImpliesElim
    | EquivElim1 | EquivElim2 | NotEquivElim1 | NotEquivElim2
    | IteElim1 | IteElim2 | NotIteElim1 | NotIteElim2
  datatype simple_boolean = SimpleAndIntro | SimpleAndElim
    | SimpleNotNotElim
    | SimpleNotOrElim
    | SimpleClausal of clausal_rule
    | SimpleNotAnd
  datatype simple_equality = SimpleRefl | SimpleSymm | SimpleTrans
    | SimpleCong | SimpleHoCong | SimpleEqResolve | SimpleContra
  (* Every registered handler is classified exactly once below, so a
     new constructor must pick its family. *)
  datatype truth_family = DeclaredBoolean | FalseIntro | FalseElim
    | TrueIntro | TrueElim | ProcessScope
  datatype simple_class = SimpleBoolean of simple_boolean
    | SimpleEquality of simple_equality | SimpleTruth of truth_family
    | NotSimple
  fun simple_class handler =
    case handler of
      P.HAndIntro => SimpleBoolean SimpleAndIntro
    | P.HAndElim => SimpleBoolean SimpleAndElim
    | P.HNotNotElim => SimpleBoolean SimpleNotNotElim
    | P.HNotOrElim => SimpleBoolean SimpleNotOrElim
    | P.HNotImpliesElim1 => SimpleBoolean (SimpleClausal NotImpliesElim1)
    | P.HNotImpliesElim2 => SimpleBoolean (SimpleClausal NotImpliesElim2)
    | P.HImpliesElim => SimpleBoolean (SimpleClausal ImpliesElim)
    | P.HEquivElim1 => SimpleBoolean (SimpleClausal EquivElim1)
    | P.HEquivElim2 => SimpleBoolean (SimpleClausal EquivElim2)
    | P.HNotEquivElim1 => SimpleBoolean (SimpleClausal NotEquivElim1)
    | P.HNotEquivElim2 => SimpleBoolean (SimpleClausal NotEquivElim2)
    | P.HIteElim1 => SimpleBoolean (SimpleClausal IteElim1)
    | P.HIteElim2 => SimpleBoolean (SimpleClausal IteElim2)
    | P.HNotIteElim1 => SimpleBoolean (SimpleClausal NotIteElim1)
    | P.HNotIteElim2 => SimpleBoolean (SimpleClausal NotIteElim2)
    | P.HNotAnd => SimpleBoolean SimpleNotAnd
    | P.HRefl => SimpleEquality SimpleRefl
    | P.HSymm => SimpleEquality SimpleSymm
    | P.HTrans => SimpleEquality SimpleTrans
    | P.HCong => SimpleEquality SimpleCong
    | P.HHoCong => SimpleEquality SimpleHoCong
    | P.HEqResolve => SimpleEquality SimpleEqResolve
    | P.HContra => SimpleEquality SimpleContra
    | P.HBool => SimpleTruth DeclaredBoolean
    | P.HFalseIntro => SimpleTruth FalseIntro
    | P.HFalseElim => SimpleTruth FalseElim
    | P.HTrueIntro => SimpleTruth TrueIntro
    | P.HTrueElim => SimpleTruth TrueElim
    | P.HProcessScope => SimpleTruth ProcessScope
    | P.HResolution => NotSimple
    | P.HCnf => NotSimple (* matched before this by [route_of] *)
    | P.HFactoring => NotSimple
    | P.HReordering => NotSimple
    | P.HAciNorm => NotSimple
    | P.HAlphaEquiv => NotSimple
    | P.HArith => NotSimple
    | P.HArithAbsEq => NotSimple
    | P.HArithAbsIntGt => NotSimple
    | P.HArithMaxGeq1 => NotSimple
    | P.HArithMaxGeq2 => NotSimple
    | P.HArithMinLt2 => NotSimple
    | P.HArithMultAbsComparison => NotSimple
    | P.HArithMultNeg => NotSimple
    | P.HArithMultPos => NotSimple
    | P.HArithMultSign => NotSimple
    | P.HArithReduction => NotSimple
    | P.HArithRel => NotSimple
    | P.HArithRule => NotSimple
    | P.HArithSumUb => NotSimple
    | P.HArithTrichotomy => NotSimple
    | P.HArray => NotSimple
    | P.HArraysExt => NotSimple
    | P.HArraysReadOverWrite => NotSimple
    | P.HArraysSelectConst => NotSimple
    | P.HBetaReduce => NotSimple
    | P.HBvAshrByConst0 => NotSimple
    | P.HBvBitwiseSlicing => NotSimple
    | P.HBvLshrByConst0 => NotSimple
    | P.HBvNotIdemp => NotSimple
    | P.HBvPolyNorm => NotSimple
    | P.HBvPolyNormEq => NotSimple
    | P.HBvShlByConst0 => NotSimple
    | P.HBvShlByConst2 => NotSimple
    | P.HBvWordRewrite => NotSimple
    | P.HBvXorDuplicate => NotSimple
    | P.HBvZeroExtendEliminate0 => NotSimple
    | P.HDatatype => NotSimple
    | P.HDatatypeEq => NotSimple
    | P.HDtSplit => NotSimple
    | P.HEqRefl => NotSimple
    | P.HEvaluate => NotSimple
    | P.HExistsElim => NotSimple
    | P.HInstantiate => NotSimple
    | P.HIntTightLb => NotSimple
    | P.HIntTightUb => NotSimple
    | P.HIteEq => NotSimple
    | P.HIteFalseCond => NotSimple
    | P.HIteNegBranch => NotSimple
    | P.HIteNotCond => NotSimple
    | P.HIteThenFalse => NotSimple
    | P.HIteThenTrue => NotSimple
    | P.HIteTrueCond => NotSimple
    | P.HLambdaElim => NotSimple
    | P.HModusPonens => NotSimple
    | P.HQuantDtSplit => NotSimple
    | P.HQuantRewrite => NotSimple
    | P.HQuantUnusedVars => NotSimple
    | P.HRareInventory => NotSimple
    | P.HRewrite => NotSimple
    | P.HScope => NotSimple
    | P.HSeqRewrite => NotSimple
    | P.HSets => NotSimple
    | P.HSetsExt => NotSimple
    | P.HSetsRewrite => NotSimple
    | P.HSkolemize => NotSimple
    | P.HString => NotSimple
    | P.HTrust => NotSimple
  fun route_of {pop,handler} =
    if pop then Scoped else
    case handler of
      P.HResolution => Resolved
    | P.HCnf => Converted
    | P.HFactoring => Aligned
    | P.HReordering => Aligned
    | _ => (case simple_class handler of NotSimple => Bounded
              | _ => Simple)
  fun simple_boolean_of handler =
    case simple_class handler of SimpleBoolean family => SOME family
      | _ => NONE
  fun simple_equality_of handler =
    case simple_class handler of SimpleEquality family => SOME family
      | _ => NONE
  fun truth_family_of handler =
    case simple_class handler of SimpleTruth family => SOME family
      | _ => NONE
  (* The handlers whose name starts with "arith" or "int_tight_". *)
  fun arithmetic_handler handler =
    case handler of
      P.HAciNorm => false
    | P.HAlphaEquiv => false
    | P.HAndElim => false
    | P.HAndIntro => false
    | P.HArith => true
    | P.HArithAbsEq => true
    | P.HArithAbsIntGt => true
    | P.HArithMaxGeq1 => true
    | P.HArithMaxGeq2 => true
    | P.HArithMinLt2 => true
    | P.HArithMultAbsComparison => true
    | P.HArithMultNeg => true
    | P.HArithMultPos => true
    | P.HArithMultSign => true
    | P.HArithReduction => true
    | P.HArithRel => true
    | P.HArithRule => true
    | P.HArithSumUb => true
    | P.HArithTrichotomy => true
    | P.HArray => false
    | P.HArraysExt => false
    | P.HArraysReadOverWrite => false
    | P.HArraysSelectConst => false
    | P.HBetaReduce => false
    | P.HBool => false
    | P.HBvAshrByConst0 => false
    | P.HBvBitwiseSlicing => false
    | P.HBvLshrByConst0 => false
    | P.HBvNotIdemp => false
    | P.HBvPolyNorm => false
    | P.HBvPolyNormEq => false
    | P.HBvShlByConst0 => false
    | P.HBvShlByConst2 => false
    | P.HBvWordRewrite => false
    | P.HBvXorDuplicate => false
    | P.HBvZeroExtendEliminate0 => false
    | P.HCnf => false
    | P.HCong => false
    | P.HContra => false
    | P.HDatatype => false
    | P.HDatatypeEq => false
    | P.HDtSplit => false
    | P.HEqRefl => false
    | P.HEqResolve => false
    | P.HEquivElim1 => false
    | P.HEquivElim2 => false
    | P.HEvaluate => false
    | P.HExistsElim => false
    | P.HFactoring => false
    | P.HFalseElim => false
    | P.HFalseIntro => false
    | P.HHoCong => false
    | P.HImpliesElim => false
    | P.HInstantiate => false
    | P.HIntTightLb => true
    | P.HIntTightUb => true
    | P.HIteElim1 => false
    | P.HIteElim2 => false
    | P.HIteEq => false
    | P.HIteFalseCond => false
    | P.HIteNegBranch => false
    | P.HIteNotCond => false
    | P.HIteThenFalse => false
    | P.HIteThenTrue => false
    | P.HIteTrueCond => false
    | P.HLambdaElim => false
    | P.HModusPonens => false
    | P.HNotAnd => false
    | P.HNotEquivElim1 => false
    | P.HNotEquivElim2 => false
    | P.HNotImpliesElim1 => false
    | P.HNotImpliesElim2 => false
    | P.HNotIteElim1 => false
    | P.HNotIteElim2 => false
    | P.HNotNotElim => false
    | P.HNotOrElim => false
    | P.HProcessScope => false
    | P.HQuantDtSplit => false
    | P.HQuantRewrite => false
    | P.HQuantUnusedVars => false
    | P.HRareInventory => false
    | P.HRefl => false
    | P.HReordering => false
    | P.HResolution => false
    | P.HRewrite => false
    | P.HScope => false
    | P.HSeqRewrite => false
    | P.HSets => false
    | P.HSetsExt => false
    | P.HSetsRewrite => false
    | P.HSkolemize => false
    | P.HString => false
    | P.HSymm => false
    | P.HTrans => false
    | P.HTrueElim => false
    | P.HTrueIntro => false
    | P.HTrust => false
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
  (* Clause occurrences keep OR aliases opaque. An explicit constructor
     rule may inspect the referenced definition at its root only; aliases
     among its operands remain atoms with their original boundaries. *)
  fun constructor_provenance (ApplicationProvenance ("<alias>",[body])) =
        body
    | constructor_provenance provenance = provenance
  (* SAME recorded aggregate and produced-AND programmes. Callers supply
     actual owned syntax and observation/copy tariffs, never proof flags. *)
  fun aggregate_entries
      {children,recorded,length,push,reverse,start,initial,check,error}
      node provenance =
    let
      val provenance = constructor_provenance provenance
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
            let val (body,result) = pair_of "not_and"
                  (operands boolSyntax.implication 2 (one ()))
                val _ = if is_false result then () else
                  raise error "implication consequent differs from F"
                val (body_prov,_) = pair_of "not_and"
                  (child_provenance "=>" 2 (one_provenance ()))
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
            S.ConstructionReference stamp =>
              (* Keep the definition's metadata, but do not turn a lexical
                 use of an OR-valued alias into an immediate OR occurrence.
                 NOT remains visible: its actual signed atom can itself be
                 an entire aliased OR, rather than that OR's operands. *)
              (case reference stamp of
                 body as ApplicationProvenance ("or",_) =>
                   ApplicationProvenance ("<alias>",[body])
               | body => body)
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
          boolSyntax.disjunction body (constructor_provenance provenance)
          (index ())
    in current (negate selected)
      (ApplicationProvenance ("not",[provenance])) end
  datatype clausal_polarity = ClausalPositive | ClausalNegative
  datatype binary_operand = ClausalLeft | ClausalRight
  datatype ternary_operand = ClausalCondition | ClausalThen | ClausalElse
  type 'operand clausal_literal = 'operand * clausal_polarity
  datatype implication_result = ClausalCurrent of binary_operand
    | ClausalFinished of binary_operand
    | ClausalImplied of binary_operand clausal_literal *
        binary_operand clausal_literal
  datatype clausal_descriptor =
      ClausalImplication of {negated:bool,result:implication_result}
    | ClausalEquivalence of {negated:bool,
        literals:binary_operand clausal_literal *
                 binary_operand clausal_literal}
    | ClausalConditional of {negated:bool,
        literals:ternary_operand clausal_literal *
                 ternary_operand clausal_literal}
  datatype 'item clausal_selection = SelectedCurrent of 'item
    | SelectedFinished of 'item
    | SelectedClause of ('item * clausal_polarity) * ('item * clausal_polarity)
  local
    val left_negative = (ClausalLeft,ClausalNegative)
    val left_positive = (ClausalLeft,ClausalPositive)
    val right_negative = (ClausalRight,ClausalNegative)
    val right_positive = (ClausalRight,ClausalPositive)
    val condition_negative = (ClausalCondition,ClausalNegative)
    val condition_positive = (ClausalCondition,ClausalPositive)
    val then_positive = (ClausalThen,ClausalPositive)
    val then_negative = (ClausalThen,ClausalNegative)
    val else_positive = (ClausalElse,ClausalPositive)
    val else_negative = (ClausalElse,ClausalNegative)
    fun implication negated result =
      ClausalImplication {negated=negated,result=result}
    fun equivalence negated literals =
      ClausalEquivalence {negated=negated,literals=literals}
    fun conditional negated literals =
      ClausalConditional {negated=negated,literals=literals}
  in
    fun clausal_descriptor rule =
      case rule of
        NotImpliesElim1 => implication true (ClausalCurrent ClausalLeft)
      | NotImpliesElim2 => implication true (ClausalFinished ClausalRight)
      | ImpliesElim => implication false
          (ClausalImplied (left_negative,right_positive))
      | EquivElim1 => equivalence false (left_negative,right_positive)
      | EquivElim2 => equivalence false (left_positive,right_negative)
      | NotEquivElim1 => equivalence true (left_positive,right_positive)
      | NotEquivElim2 => equivalence true (left_negative,right_negative)
      | IteElim1 => conditional false (condition_negative,then_positive)
      | IteElim2 => conditional false (condition_positive,else_positive)
      | NotIteElim1 => conditional true (condition_negative,then_negative)
      | NotIteElim2 => conditional true (condition_positive,else_negative)
  end
  fun clausal_negated (ClausalImplication {negated,...}) = negated
    | clausal_negated (ClausalEquivalence {negated,...}) = negated
    | clausal_negated (ClausalConditional {negated,...}) = negated
  (* The one selection of a descriptor's literals.  Each reader reads its
     operands, below a negation when its argument says so; the descriptor
     picks the literals out of what its own reader returned. *)
  fun clausal_select descriptor {implication,equivalence,conditional} =
    let
      fun binary (left,_) ClausalLeft = left
        | binary (_,right) ClausalRight = right
      fun ternary (condition,_,_) ClausalCondition = condition
        | ternary (_,then_item,_) ClausalThen = then_item
        | ternary (_,_,else_item) ClausalElse = else_item
      fun pick lookup (operand,polarity) = (lookup operand,polarity)
    in
      case descriptor of
        ClausalImplication {negated,result} =>
          let val lookup = binary (implication negated)
          in case result of
              ClausalCurrent operand => SelectedCurrent (lookup operand)
            | ClausalFinished operand => SelectedFinished (lookup operand)
            | ClausalImplied (first,second) =>
                SelectedClause (pick lookup first,pick lookup second)
          end
      | ClausalEquivalence {negated,literals=(first,second)} =>
          let val lookup = binary (equivalence negated)
          in SelectedClause (pick lookup first,pick lookup second) end
      | ClausalConditional {negated,literals=(first,second)} =>
          let val lookup = ternary (conditional negated)
          in SelectedClause (pick lookup first,pick lookup second) end
    end
  fun clausal_literals descriptor {positive,negative} readers =
    let
      fun literal (item,ClausalPositive) = positive item
        | literal (item,ClausalNegative) = negative item
    in
      case clausal_select descriptor readers of
        SelectedCurrent item => [positive item]
      | SelectedFinished item => [negative item]
      | SelectedClause (first,second) =>
          let val first_literal = literal first
              val second_literal = literal second
          in [first_literal,second_literal] end
    end
  fun clausal_elim
      {negated,one,operands,child_provenance,negation_provenance,
       one_provenance,pair,same_constant,atom,current,negative,positive,
       finish,disjoin,error}
      descriptor handler =
    let
      val conditional_rule = case descriptor of
          ClausalConditional _ => true
        | _ => false
      (* Premise node (below a negation when [strip]), then its
         provenance, each read by the reader's own operand functions and
         zipped into (node,provenance) pairs. *)
      fun read nodes_of provenances_of zip strip =
        let
          val source = if strip then
              (case negated (one ()) of
                 SOME body => body
               | NONE => raise error handler "expected negation")
            else one ()
          val nodes = nodes_of source
          val premise_provenance = one_provenance ()
          val provenance = if strip then
              negation_provenance premise_provenance else premise_provenance
        in zip nodes (provenances_of provenance) end
      fun zip_pairs (a,b) (c,d) = ((a,c),(b,d))
      fun zip_triples (a,b,c) (d,e,f) = ((a,d),(b,e),(c,f))
      val readers =
        {implication = read
           (fn source => pair_of handler
              (operands boolSyntax.implication 2 source))
           (fn provenance => pair_of handler
              (child_provenance "=>" 2 provenance)) zip_pairs,
         equivalence = read pair equality_provenance zip_pairs,
         conditional = read
           (fn source => triple_of handler
              (operands boolSyntax.conditional 3 source))
           (fn provenance => triple_of handler
              (child_provenance "ite" 3 provenance)) zip_triples}
      fun literal ((node,provenance),ClausalPositive) =
            positive node provenance
        | literal ((node,provenance),ClausalNegative) =
            negative node provenance
    in
      if conditional_rule andalso same_constant (one ()) boolSyntax.T then
        atom (one ())
      else
        case clausal_select descriptor readers of
          SelectedCurrent (node,provenance) => current node provenance
        | SelectedFinished (node,provenance) =>
            finish (negative node provenance)
        | SelectedClause (first,second) =>
            let val first_literal = literal first
                val second_literal = literal second
            in disjoin [first_literal,second_literal] end
    end
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
