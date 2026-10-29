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
        (* Keep successful schemas first. A checked path between endpoint
           names avoids speculative worker calls on unrelated children.
           The original worker receives checked bridges on misses, with its
           former named-only input retained if bridge admission/proving fails.
           No String/regex prover rung or schema priority is changed. *)
        in retry (fn () => schema false)
          (fn () => retry chain (fn () => schema true)) end
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
