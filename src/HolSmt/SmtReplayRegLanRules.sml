(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayRegLanRules =
struct
  open SmtReplayGraph SmtReplayProof SmtRegLanProve
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  val ERR = Feedback.mk_HOL_ERR "SmtReplayRegLanRules"
  type fact = G.node * P.edge
  fun spine graph node =
    let fun walk node operands = case G.view graph node of
          G.Application (operator,operand) => walk operator (operand::operands)
        | G.Constant _ => SOME (G.representative graph node,operands)
        | _ => NONE
    in walk node [] end
  fun operands graph head node = case spine graph node of
      SOME (operator,[left,right]) =>
        if Term.same_const operator head then SOME (left,right) else NONE
    | _ => NONE
  fun relation graph node = operands graph SmtRegLanProve.equiv_tm node
  fun hol_equality graph node = operands graph boolSyntax.equality node
  fun consumer graph node = case hol_equality graph node of
      SOME (left,right) =>
        let fun head node = case spine graph node of
                SOME (head,_) => SOME head | NONE => NONE
            val membership = Term.prim_mk_const
              {Thy = "smtstring",Name = "smt_in_re"}
        in case (head left,head right) of
             (SOME a,SOME b) => Term.same_const a b andalso
               (Term.same_const a membership orelse
                Term.same_const a SmtRegLanProve.equiv_tm)
           | _ => false end
    | NONE => false
  fun applicable graph target premises =
    Option.isSome (relation graph target) orelse
    (consumer graph target andalso
     List.exists (Option.isSome o relation graph) premises)

  (* Binder syntax needs the existing variable-only conditional-law adapter
     before freeze; constructor equations deliberately keep binders opaque. *)
  fun has_binder graph {inputs,observe} =
    let
      fun compare pair = (observe ();Int.compare pair)
      val seen = ref (Redblackset.empty compare)
      fun visit node =
        (observe ();
         if Redblackset.member (!seen,G.node_id node) then false else
           (seen := Redblackset.add (!seen,G.node_id node);
            case G.view graph node of
              G.Application (f,x) => visit f orelse visit x
            | G.AdmittedBinder _ => true
            | G.OpaqueRetained => true
            | _ => false))
    in List.exists visit inputs end

  val congruence_schemas =
    [smtstringTheory.reglan_concat_equiv,
     smtstringTheory.reglan_union_equiv,
     smtstringTheory.reglan_inter_equiv,
     smtstringTheory.reglan_diff_equiv,
     smtstringTheory.reglan_comp_equiv,
     smtstringTheory.reglan_star_equiv,
     smtstringTheory.reglan_plus_equiv,
     smtstringTheory.reglan_opt_equiv,
     smtstringTheory.reglan_power_equiv,
     smtstringTheory.reglan_loop_equiv,
     smtstringTheory.reglan_cond_equiv,
     smtstringTheory.reglan_equiv_equiv_eq,
     smtstringTheory.smt_in_re_equiv_eq]
  fun pair_compare ((a,b),(c,d)) = case Int.compare (a,c) of
      EQUAL => Int.compare (b,d) | order => order

  fun assemble graph block {rule,target,premises : fact list} =
    let
      val semantic = Option.isSome (relation graph target)
      val (left,right) = if semantic then valOf (relation graph target)
        else case hol_equality graph target of SOME pair => pair
          | NONE => raise ERR "assemble" "unsupported relation endpoint"
      val _ = if semantic orelse consumer graph target then () else
        raise ERR "assemble" "intensional equality is a different relation"
      val dependencies = ref ([] : P.edge list)
      fun constructor node =
        let val edge = P.constructor block node in
          dependencies := edge :: !dependencies;P.theorem block edge end
      val target_bridge = constructor target
      fun expose (node,edge) =
        let val _ = if Term.aconv (Thm.concl (P.theorem block edge))
                (P.name block node) then () else raise ERR "assemble"
                  "wrong named premise endpoint"
            val theorem = Thm.EQ_MP (constructor node) (P.theorem block edge)
            val _ = dependencies := edge :: !dependencies
        in (node,theorem) end
      val exposed = List.map expose premises
      val relations = List.mapPartial (fn (node,theorem) =>
        Option.map (fn pair => (pair,theorem)) (relation graph node)) exposed
      val equalities = List.mapPartial (fn (node,theorem) =>
        Option.map (fn pair => (pair,theorem))
          (hol_equality graph node)) exposed
      fun name node = P.name block node
      fun refl node = SmtRegLanProve.refl (name node)
      fun sym theorem = SmtRegLanProve.sym theorem
      fun trans first second = SmtRegLanProve.trans first second
      fun exact_relation (left,right) =
        case List.find (fn ((a,b),_) => a = left andalso b = right) relations of
          SOME (_,theorem) => SOME theorem
        | NONE => case List.find
            (fn ((a,b),_) => a = right andalso b = left) relations of
              SOME (_,theorem) => SOME (sym theorem)
            | NONE =>
                let
                  val equality = case List.find
                      (fn ((a,b),_) => a = left andalso b = right) equalities of
                        SOME (_,theorem) => SOME theorem
                      | NONE => Option.map (Thm.SYM o #2) (List.find
                          (fn ((a,b),_) => a = right andalso b = left)
                          equalities)
                in Option.map (fn theorem => Drule.MATCH_MP
                  smtstringTheory.reglan_eq_imp_equiv theorem) equality end
      fun exact_equality (left,right) =
        if left = right then Thm.REFL (name left) else
          case List.find
              (fn ((a,b),_) => a = left andalso b = right) equalities of
            SOME (_,theorem) => theorem
          | NONE => case List.find
              (fn ((a,b),_) => a = right andalso b = left) equalities of
                SOME (_,theorem) => Thm.SYM theorem
              | NONE => raise ERR "congruence"
                  "missing intensional operand equality"
      val names = List.foldl (fn (node,table) =>
        Redblackmap.insert (table,name node,node))
        (Redblackmap.mkDict Term.compare)
        (G.block_reachable graph (target :: List.map #1 premises))
      fun named term = case Redblackmap.peek (names,term) of SOME node => node
        | NONE => raise ERR "congruence" "schema operand is not an owned name"
      val memo = ref (Redblackmap.mkDict pair_compare)
      fun congruent fallback (left,right) =
        if left = right then refl left else
          case exact_relation (left,right) of SOME theorem => theorem
          | NONE => case Redblackmap.peek
              (!memo,(G.node_id left,G.node_id right)) of
                SOME theorem => theorem
              | NONE =>
                  let val theorem = constructor_congruence fallback true
                        (left,right)
                      val _ = memo := Redblackmap.insert
                        (!memo,(G.node_id left,G.node_id right),theorem)
                  in theorem end
      and antecedent fallback proposition =
        case Lib.total boolSyntax.dest_conj proposition of
          SOME (left,right) => Thm.CONJ
            (antecedent fallback left) (antecedent fallback right)
        | NONE => case Lib.total SmtRegLanProve.dest_equiv proposition of
            SOME (left,right) => congruent fallback (named left,named right)
          | NONE => case Lib.total boolSyntax.dest_eq proposition of
              SOME (left,right) => exact_equality (named left,named right)
            | NONE => raise ERR "congruence" "unsupported schema antecedent"
      and constructor_congruence fallback semantic (left,right) =
        let
          val lhs = constructor left
          val rhs = constructor right
          val expanded_left = boolSyntax.rhs (Thm.concl lhs)
          val expanded_right = boolSyntax.rhs (Thm.concl rhs)
          val target = if semantic then
              SmtRegLanProve.mk_equiv (expanded_left,expanded_right)
            else boolSyntax.mk_eq (expanded_left,expanded_right)
          fun instantiate schema =
            let val generic = Drule.SPEC_ALL schema
                val (_,conclusion) = boolSyntax.strip_imp (Thm.concl generic)
                val instance = Drule.INST_TY_TERM
                  (Term.match_term conclusion target) generic
                val (antecedents,_) = boolSyntax.strip_imp (Thm.concl instance)
            in Drule.LIST_MP (List.map (antecedent fallback) antecedents)
              instance end
          val theorem = Lib.tryfind instantiate congruence_schemas
            handle Feedback.HOL_ERR primary =>
              if not fallback orelse SmtResource.is_resource_gate primary
              then raise Feedback.HOL_ERR primary
              else
                let
                  (* Connect names in premises (including compound
                     intermediates) to compact constructor spines. Recording
                     equations as dependencies alone does not make them
                     worker facts. No realized operand is exposed. *)
                  fun prove facts =
                    let
                      val admit = SmtReplayArithmetic.new_term_check
                        {limit=P.template_limit block,observe=fn () => ()}
                      val _ = List.app admit (target ::
                        List.concat (List.map (fn theorem =>
                          Thm.concl theorem :: Thm.hyp theorem)
                          (facts @ SmtRegLanProve.congruence_theorems)))
                      val theorem = SmtRegLanProve.congruence facts target
                      val _ = List.app admit
                        (Thm.concl theorem :: Thm.hyp theorem)
                    in theorem end
                  val facts = List.map #2 exposed
                  val saved_dependencies = !dependencies
                in
                    let
                      val seen = ref (Redblackset.empty Int.compare)
                      val visits = ref 0
                      fun visit () =
                        if !visits < P.template_limit block then
                          visits := !visits + 1
                        else raise ERR "congruence"
                          "regex constructor frontier exceeds local admission"
                      fun children node =
                        let fun walk node operands =
                              (visit ();
                               case G.view graph node of
                                 G.Application (f,x) => walk f (x::operands)
                               | G.Constant _ => operands
                               | _ => node::operands)
                        in walk node [] end
                      fun frontier node =
                        if Redblackset.member (!seen,G.node_id node) then []
                        else
                          (visit ();
                           seen := Redblackset.add (!seen,G.node_id node);
                           case G.view graph node of
                             G.Application _ =>
                               let val operands = children node
                               in constructor node ::
                                 List.concat (List.map frontier operands) end
                           | G.Constant _ => [constructor node]
                           | _ => [])
                      val roots = left :: right :: List.concat
                        (List.map (fn ((a,b),_) => [a,b])
                          (relations @ equalities))
                      val bridges = List.concat (List.map frontier roots)
                    in prove (facts @ bridges) end
                    handle Feedback.HOL_ERR primary =>
                      (dependencies := saved_dependencies;
                       if SmtResource.is_resource_gate primary then
                         raise Feedback.HOL_ERR primary
                       else prove facts)
                end
          val bridge = if semantic then
              Thm.MK_COMB (Thm.AP_TERM SmtRegLanProve.equiv_tm lhs,rhs)
            else
              let val equality = Term.rator (Term.rator
                    (boolSyntax.mk_eq (name left,name left)))
              in Thm.MK_COMB (Thm.AP_TERM equality lhs,rhs) end
        in Thm.EQ_MP (Thm.SYM bridge) theorem end
      fun symmetric_chain () =
        let val neighbors = ref (Redblackmap.mkDict Int.compare)
            fun add (from,to,theorem) =
              let val key = G.node_id from in
                neighbors := Redblackmap.insert (!neighbors,key,
                  (to,theorem) :: Option.getOpt
                    (Redblackmap.peek (!neighbors,key),[])) end
            val _ = List.app (fn ((a,b),theorem) =>
              (add (a,b,theorem);add (b,a,sym theorem))) relations
            fun search [] [] _ = raise ERR "assemble"
                  "no semantic transitivity path"
              | search [] back seen = search (List.rev back) [] seen
              | search ((node,path)::rest) back seen =
                  if node = right then path else
                    let fun enqueue ((next,theorem),(back,seen)) =
                          if Redblackset.member (seen,G.node_id next) then
                            (back,seen) else
                            ((next,trans path theorem)::back,
                             Redblackset.add (seen,G.node_id next))
                        val (back,seen) = List.foldl enqueue (back,seen)
                          (Option.getOpt (Redblackmap.peek
                            (!neighbors,G.node_id node),[]))
                    in search rest back seen end
        in search [(left,refl left)] []
          (Redblackset.singleton Int.compare (G.node_id left)) end
      (* Prefer the retained procedure on a bounded, checked syntax frame.
         In particular, Boolean premise patterns and competing proof chains
         must reach it together, in source order. Trying recursive workers
         or endpoint paths first changes its successful fallback and Hyp.
         These are local names, never realized source operands. On a frame
         miss the existing nodewise adapter remains available. *)
      fun bounded_congruence () =
        let
          val limit = P.template_limit block
          val sizes = ref (Redblackmap.mkDict Int.compare)
          val check_type = SmtReplayArithmetic.new_type_check (fn () => ())
          val visits = ref 0
          fun size node = case Redblackmap.peek (!sizes,G.node_id node) of
              SOME n => n
            | NONE =>
                let val _ = if !visits < limit then () else
                      raise ERR "congruence"
                        "regex syntax frontier exceeds local admission"
                    val _ = visits := !visits + 1
                    val _ = check_type (G.type_of graph node)
                    val n = case G.view graph node of
                        G.Application (f,x) =>
                          Int.min (limit,1 + size f + size x)
                      | _ => 1
                    val _ = sizes := Redblackmap.insert
                      (!sizes,G.node_id node,n)
                in n end
          (* Forecast syntax and Types before any native proof operation.
             Keep relation/Boolean patterns and the target's schema heads;
             cut large DATA operands consistently across the whole frame.
             Cutting entire propositions (or their constructor operands only
             at some occurrences) changes native schema priority and Hyp. *)
          val _ = List.app (ignore o size) (target :: map #1 premises)
          val forced = ref (Redblackset.empty Int.compare)
          fun force node =
            if Redblackset.member (!forced,G.node_id node) then () else
              (forced := Redblackset.add (!forced,G.node_id node);
               case G.view graph node of
                 G.Application (f,_) => force f
               | _ => ())
          val patterns = ref (Redblackmap.mkDict Int.compare)
          fun pattern node =
            case Redblackmap.peek (!patterns,G.node_id node) of
              SOME relevant => relevant
            | NONE =>
                let val children = case spine graph node of
                        SOME (_,args) => args | NONE => []
                    val nested = List.map pattern (List.filter (fn child =>
                      Type.compare (G.type_of graph child,Type.bool)=EQUAL)
                      children)
                    val relevant = Option.isSome (relation graph node) orelse
                      Option.isSome (hol_equality graph node) orelse
                      List.exists Lib.I nested
                    val _ = if relevant then force node else ()
                    val _ = patterns := Redblackmap.insert
                      (!patterns,G.node_id node,relevant)
                in relevant end
          val _ = ignore (pattern target)
          val _ = List.app force [target,left,right]
          val essential = !forced
          val _ = List.app (ignore o pattern o #1) premises
          val allowance = ref (limit - 6)
          fun opaque node = size node > !allowance andalso
            not (Redblackset.member (!forced,G.node_id node))
          (* A shared operand can fit individually but not at all of its
             occurrences in a wrapper. Tighten ONLY the local data frontier,
             consistently for every occurrence, until the whole frame fits.
             No native operation precedes this prospective calculation. *)
          fun fit () =
            let val projected = ref (Redblackmap.mkDict Int.compare)
                fun forecast node =
                  case Redblackmap.peek (!projected,G.node_id node) of
                    SOME n => n
                  | NONE =>
                      let val n = if opaque node then 1 else
                            case G.view graph node of G.Application (f,x) =>
                              Int.min (limit,1 + forecast f + forecast x)
                            | _ => 1
                          val _ = projected := Redblackmap.insert
                            (!projected,G.node_id node,n)
                      in n end
            in if List.all (fn node => forecast node <= limit - 6)
                (target :: map #1 premises) then ()
               else if !allowance > 1 then
                 (allowance := !allowance div 2;fit ())
               else
                 let
                   (* A huge advertised Boolean pattern must not veto a
                      small earlier schema. Keep its root opaque when even
                      its DATA-named pattern cannot fit, but never erase a
                      head/pattern demanded by the target itself. *)
                   val omitted = List.filter (fn (node,_) =>
                     forecast node > limit - 6 andalso
                     Redblackset.member (!forced,G.node_id node) andalso
                     not (Redblackset.member (essential,G.node_id node)))
                     premises
                   val _ = List.app (fn (node,_) =>
                     if Redblackset.member (!forced,G.node_id node) then
                       forced := Redblackset.delete (!forced,G.node_id node)
                     else ()) omitted
                 in if null omitted then raise ERR "congruence"
                      "regex syntax frame exceeds local admission"
                    else fit ()
                 end
            end
          (* Reserve six nodes for intermediate equation wrappers. A pure
             oversized unused Boolean premise can still stay a name. *)
          val _ = fit ()
          val equations = ref (Redblackmap.mkDict Int.compare)
          val source_names = ref (Redblackmap.mkDict Term.compare)
          val local_names = ref ([] : Term.term list)
          fun expand node =
            case Redblackmap.peek (!equations,G.node_id node) of
              SOME theorem => theorem
            | NONE =>
                let
                  val _ = local_names := name node :: !local_names
                  val _ = case G.view graph node of
                      G.Variable (G.RigidSource,variable) =>
                        source_names := Redblackmap.insert
                          (!source_names,variable,name node)
                    | _ => ()
                  val theorem = if opaque node then
                      Thm.REFL (name node)
                    else case G.view graph node of
                      G.Application (f,x) =>
                        let val children = Thm.MK_COMB (expand f,expand x)
                            val edge = P.definition block node
                            val _ = dependencies := edge :: !dependencies
                        in Thm.TRANS (P.theorem block edge) children end
                    | _ => constructor node
                  val _ = equations := Redblackmap.insert
                    (!equations,G.node_id node,theorem)
                in theorem end
          val bridge = expand target
          val proposition = boolSyntax.rhs (Thm.concl bridge)
          val facts = map (fn (node,edge) =>
            Thm.EQ_MP (expand node) (P.theorem block edge)) premises
          val admit = SmtReplayArithmetic.new_term_check
            {limit=limit,observe=fn () => ()}
          val _ = List.app admit (proposition :: List.concat
            (map (fn th => Thm.concl th :: Thm.hyp th)
              (facts @ SmtRegLanProve.congruence_theorems)))
          (* Native exact-antecedent lookup can select a residual law
             variable (the middle of transitivity, for example) by its
             source identity. Rename the LAWS through the same injective
             boundary as the frame, not just their matched consequences.
             Only rigid source leaves establish this correspondence: a
             generated/solver/bound namesake is a distinct declaration.
             Variables absent from the final projection get fresh locals,
             so they cannot accidentally select a graph placeholder. *)
          val schemas = map Drule.SPEC_ALL
            SmtRegLanProve.congruence_theorems
          val variables = Term.free_varsl (map Thm.concl schemas)
          val reserved = ref (!local_names)
          fun rename variable =
            let val local_name = case Redblackmap.peek
                    (!source_names,variable) of
                    SOME owned => owned
                  | NONE => Term.variant (!reserved)
                      (Term.mk_var ("smt_reglan_schema_" ^
                        #1 (Term.dest_var variable),Term.type_of variable))
                val _ = reserved := local_name :: !reserved
            in {redex=variable,residue=local_name} end
          val substitution = map rename variables
          val schemas = map (Thm.INST substitution) schemas
          val _ = List.app (admit o Thm.concl) schemas
          val theorem = SmtRegLanProve.congruence_with_theorems
            schemas facts proposition
          val _ = List.app admit (Thm.concl theorem :: Thm.hyp theorem)
        in Thm.EQ_MP target_bridge
             (Thm.EQ_MP (Thm.SYM bridge) theorem) end
      fun congruence () =
        let
          fun schema fallback = if semantic then
              congruent fallback (left,right)
            else constructor_congruence fallback false (left,right)
          fun retry action next = action () handle Feedback.HOL_ERR primary =>
            if SmtResource.is_resource_gate primary then
              raise Feedback.HOL_ERR primary else next ()
          fun chain () = if semantic then symmetric_chain () else
            raise ERR "congruence" "not a semantic chain"
          val saved_dependencies = !dependencies
          fun legacy () =
            (dependencies := saved_dependencies;
             retry (fn () => schema false)
               (fn () => retry chain (fn () => schema true)))
        in retry bounded_congruence legacy end
      val theorem = case rule of
          "refl" => if semantic andalso left = right andalso
              List.null premises then refl left else
                raise ERR "assemble" "invalid semantic reflexivity"
        | "symm" => (case relations of [((a,b),theorem)] =>
              if a = right andalso b = left andalso List.length premises = 1
              then sym theorem else raise ERR "assemble"
                "invalid semantic symmetry endpoints"
            | _ => raise ERR "assemble" "symmetry expects one semantic premise")
        | "trans" =>
            let fun chain [] _ = raise ERR "assemble"
                      "empty semantic transitivity"
                  | chain [((a,b),theorem)] expected =
                      if a = expected andalso b = right then theorem else
                        raise ERR "assemble"
                          "semantic transitivity endpoints differ"
                  | chain (((a,b),theorem)::rest) expected =
                      if a = expected then trans theorem (chain rest b) else
                        raise ERR "assemble"
                          "semantic transitivity order differs"
            in if List.length premises = List.length relations then
                chain relations left else raise ERR "assemble"
                  "transitivity includes a different relation" end
        | "trans-star" => symmetric_chain ()
        | "cong" => congruence ()
        | _ => raise ERR "assemble" "unknown semantic relation procedure"
      val named = Thm.EQ_MP (Thm.SYM target_bridge) theorem
    in P.compose block (fn _ => named) (!dependencies) end
end
