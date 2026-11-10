(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayRules =
struct
  open SmtReplayGraph SmtReplayProof SmtBooleanGraph SmtReplayRegLanRules
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  val ERR = Feedback.mk_HOL_ERR "SmtReplayRules"
  type fact = G.node * P.edge

  fun spine graph node =
    let fun walk node arguments = case G.view graph node of
          G.Application (operator,operand) =>
            walk operator (operand :: arguments)
        | G.Constant _ => SOME (G.representative graph node,arguments)
        | _ => NONE
    in walk node [] end

  fun operands graph constant arity node =
    case spine graph node of
      SOME (head,arguments) =>
        if Term.same_const head constant andalso List.length arguments = arity
        then SOME arguments else NONE
    | NONE => NONE
  fun equality graph node =
    case operands graph boolSyntax.equality 2 node of
      SOME [left,right] => SOME (left,right) | _ => NONE

  datatype relation_kind = HolEquality | RegLanEquivalence
  fun relation graph node = case equality graph node of
      SOME pair => SOME (HolEquality,pair)
    | NONE => Option.map (fn pair => (RegLanEquivalence,pair))
        (SmtReplayRegLanRules.relation graph node)

  fun endpoint block (node,edge) =
    if Term.aconv (Thm.concl (P.theorem block edge)) (P.name block node)
    then () else raise ERR "assemble" "incorrect named premise endpoint"

  (* All equality operations see compact operand variables. Applications
     are exposed by recorded constructor equations, one owned node at a
     time. A binder is usable only as an identical node or a proved leaf. *)
  fun equality_rule graph block rule target (premises : fact list) =
    let
      val (left,right) = case equality graph target of SOME pair => pair
        | NONE => raise ERR "equality_rule" "non-equality conclusion"
      val relations = List.map (fn (node,edge) =>
        case equality graph node of
          SOME pair => (pair,P.constructor block node,edge)
        | NONE => raise ERR "equality_rule" "non-equality premise") premises
      val target_bridge = P.constructor block target
      val extra = ref ([] : P.edge list)
      fun definition node =
        let val edge = P.definition block node in
          extra := edge :: !extra;P.theorem block edge end
      fun expose ((pair,bridge,edge),proofs) =
        (pair,Thm.EQ_MP (P.theorem block bridge) (P.theorem block edge))
        :: proofs
      val compact = List.foldl expose [] relations
      val proof=SmtReplayNamedContext.equality_programme
        {key=G.node_id,same=op =,
         application=fn node=>case G.view graph node of
           G.Application pair=>SOME pair | _=>NONE,
         reflexive=fn node=>Thm.REFL (P.name block node),
         symmetry=Thm.SYM,transitivity=Thm.TRANS,congruence=Thm.MK_COMB,
         definition=definition,error=ERR "equality_rule"}
        {rule=rule,left=left,right=right,premises=compact}
      val named = Thm.EQ_MP (Thm.SYM (P.theorem block target_bridge)) proof
      val dependencies = target_bridge :: List.concat
        (List.map (fn (_,bridge,edge) => [bridge,edge]) relations) @ !extra
    in P.compose block (fn _ => named) dependencies end

  fun boolean_rule graph block target premises =
    SmtBooleanGraph.assemble_graph_using
      (fn _ => fn action => action ())
      {graph = graph,block = block,root = target,premises = premises}

  fun implication graph scope premises target =
    let val operator = G.constant graph scope boolSyntax.implication in
      List.foldr (fn (premise,result) => G.application graph scope
        (G.application graph scope (operator,premise),result)) target premises
    end

  (* A bounded ordinary adapter proves this conditional law closed before
     assembly. The law is an explicitly witnessed Source leaf; operand and
     premise DAGs are inserted only at the final closed realization. *)
  fun apply_law graph block {law,target,premises} =
    boolean_rule graph block target (law :: premises)

  fun assemble graph block {rule,target,premises} =
    let
      val _ = List.app (endpoint block) premises
      fun relation_rule rule =
        if Option.isSome (SmtReplayRegLanRules.relation graph target) orelse
           (rule = "cong" andalso
            SmtReplayRegLanRules.consumer graph target andalso
            List.exists (fn (node,_) => Option.isSome
              (SmtReplayRegLanRules.relation graph node)) premises)
        then SmtReplayRegLanRules.assemble graph block
          {rule = rule,target = target,premises = premises}
        else equality_rule graph block rule target premises
    in case rule of
        "refl" => relation_rule "refl"
      | "symm" => relation_rule "symm"
      | "symmetry" => relation_rule "symm"
      | "trans" => relation_rule "trans"
      | "trans-star" => relation_rule "trans-star"
      | "transitivity" => relation_rule "trans"
      | "monotonicity" => relation_rule "cong"
      | "cong" => relation_rule "cong"
      | "ho-cong" => relation_rule "cong"
      | "and-intro" => boolean_rule graph block target premises
      | "and-elim" => boolean_rule graph block target premises
      | "iff-false" => boolean_rule graph block target premises
      | "iff-true" => boolean_rule graph block target premises
      | "mp" => boolean_rule graph block target premises
      | "mp-eq" => boolean_rule graph block target premises
      | "not-or-elim" => boolean_rule graph block target premises
      | "true-axiom" => boolean_rule graph block target premises
      | "def-axiom" => boolean_rule graph block target premises
      | "commutativity" => boolean_rule graph block target premises
      | "rewrite" => boolean_rule graph block target premises
      | _ => raise ERR "assemble" ("unknown checked rule handler: " ^ rule)
    end
  (* The existing checked CNF/SAT engine sees only authentic compact names.
     This is its public operand/result admission, not a private SAT tariff. *)
  fun boolean_graph_with_policy work block request =
    ((let val owned=P.policy_native_block_owner_for work block
          val native=SmtReplayNativeContract.for_work work (#contract owned)
          val graph= #graph owned
          val _=SmtReplayInvocationWork.spend_policy work 0
      in SmtReplayNamedBoolean.assemble
        {native=native,
         spend=fn n=>SmtReplayInvocationWork.spend_policy work
           (IntInf.fromInt n),
         pay=SmtReplayInvocationWork.spend_policy work,
         guard=fn()=>ignore (P.policy_native_block_owner_for work block),
         profile=P.compact_profile_with_policy work block,
         type_weight=P.native_type_weight_with_policy work block,
         type_of=G.type_of graph,
         view=fn node=>case G.view graph node of
             G.Application pair=>SmtReplayNamedBoolean.Application pair
           | G.Constant _=>SmtReplayNamedBoolean.Constant
           | _=>SmtReplayNamedBoolean.Atom,
         constant=G.representative graph,same=op =,
         name=P.name block,theorem=P.theorem block,
         constructor=P.constructor_with_policy work block,
         closed=fn proof=>P.execute_closed_named_inst_with_policy work
           (P.prepare_closed_named_inst_with_policy work block
             {theorem=proof,substitution=[]}),
         equality_mp=fn edges=>P.execute_primitive_with_policy work
           (P.prepare_primitive_with_policy work block P.EqualityMP edges),
         conjunction=fn edges=>P.execute_boolean_primitive_with_policy work
           (P.prepare_boolean_primitive_with_policy work block
             P.PolicyConjunction edges),
         implication_mp=fn edges=>P.execute_boolean_primitive_with_policy work
           (P.prepare_boolean_primitive_with_policy work block
             P.PolicyImplicationMP edges),error=ERR "policy_sat"} request
      end)
     handle primary=>(SmtReplayInvocationWork.close work;raise primary))

  (* The genuine witnessed conditional law already carries its implication
     chain. Expose only its recorded constructor; arguments stay named. *)
  (* Static ordinary-P specialization of the SAME implication programme.
     No caller operations record or partial callback is made per call. *)
  structure ImplicationLaw = SmtReplayImplicationLawFn
    (struct
       type block=P.block
       type edge=P.edge
       val owner_for=P.policy_native_block_owner_for
       fun theorem _ block edge=P.theorem block edge
       fun name _ block node=P.name block node
       val constructor=P.constructor_with_policy
       fun derive work block opcode inputs=
         P.execute_primitive_with_policy work
           (P.prepare_primitive_with_policy work block opcode inputs)
       fun implication_mp work block law premise=
         P.execute_boolean_primitive_with_policy work
           (P.prepare_boolean_primitive_with_policy work block
             P.PolicyImplicationMP [law,premise])
       val error=ERR
     end)
  val apply_implication_law_with_policy=
    ImplicationLaw.apply_implication_law_with_policy

  (* The ordinary propositional fallback retains the existing SAT engine.
     Its genuine target/premise edges, not a callback theorem, enter P. *)
  fun apply_law_with_policy work graph block request =
    let val owner=P.policy_native_block_owner_for work block
        val _=if Portable.pointer_eq(graph,#graph owner) then () else
          raise ERR "policy_apply_law" "different graph"
        val {law=(law_node,law_edge),target,premises}=request
        fun implication node=case G.view graph node of
            G.Application(part,tail)=>
              (case G.view graph part of G.Application(head,antecedent)=>
                  (case G.view graph head of G.Constant _=>
                     if Term.same_const(G.representative graph head)
                         boolSyntax.implication then SOME(antecedent,tail)
                     else NONE
                   | _=>NONE)
                | _=>NONE)
          | _=>NONE
        fun chain node []=node=target
          | chain node ((wanted,_)::rest)=
              (SmtReplayInvocationWork.spend_policy work 1;
               case implication node of SOME(antecedent,tail)=>
                 antecedent=wanted andalso chain tail rest | NONE=>false)
        val _=ignore(P.name block law_node)
        val _=ignore(P.name block target)
    in if chain law_node premises then
         apply_implication_law_with_policy work graph block request
       else boolean_graph_with_policy work block
         {root=target,premises=(law_node,law_edge)::premises}
    end handle primary=>(SmtReplayInvocationWork.close work;raise primary)

  (* Actual compact equality assembly for the CPC/Z3 policy receivers.
     No raw proof callback, replacement NC or expanded operand is accepted.
     The authentic Block owns every name, definition and incoming edge. *)
  fun equality_rule_with_policy work graph block rule target premises =
    ((let val owner=P.policy_native_block_owner_for work block
          val _=if Portable.pointer_eq (graph,#graph owner) then () else
            raise ERR "policy_equality" "different graph"
          val _=SmtReplayInvocationWork.spend_policy work 0
          fun fixed opcode edges=P.execute_primitive_with_policy work
            (P.prepare_primitive_with_policy work block opcode edges)
          fun boolean opcode edges=P.execute_boolean_primitive_with_policy
            work (P.prepare_boolean_primitive_with_policy
              work block opcode edges)
      in SmtReplayNamedEquality.assemble
        {guard=fn()=>ignore (P.policy_native_block_owner_for work block),
         tick=fn()=>SmtReplayInvocationWork.spend_policy work 1,
         key=G.node_id,compare_keys=Int.compare,
         same=op =,name=P.name block,
         equality=equality graph,
         application=fn node=>case G.view graph node of
             G.Application pair=>SOME pair | _=>NONE,
         theorem=P.theorem block,
         constructor=P.constructor_with_policy work block,
         definition=P.definition block,
         reflexive=fn node=>fixed (P.ReflexiveName node) [],
         symmetry=fixed P.Symmetry,transitivity=fixed P.Transitivity,
         congruence=fixed P.Congruence,equality_mp=fixed P.EqualityMP,
         conjunction=boolean P.PolicyConjunction,
         conjunct_left=boolean P.PolicyConjunctLeft,
         error=ERR "policy_equality"}
        {rule=rule,target=target,premises=premises}
      end)
     handle primary=>(SmtReplayInvocationWork.close work;raise primary))

end
