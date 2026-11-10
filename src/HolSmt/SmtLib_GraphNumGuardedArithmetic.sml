(* Total natural operation transfers and explicitly guarded Num cancellation.
   The zero-divisor and truncated subtraction cases stay in the checked law. *)
structure SmtLib_GraphNumGuardedArithmetic :>
    SmtLib_GraphNumGuardedArithmetic =
struct
  open SmtReplayGraph SmtReplayCanonGraph SmtReplayRules SmtReplayImport
    SmtLib_GraphPreprocessDerived integerTheory int_arithTheory HolSmtTheory
  structure G = SmtReplayGraph
  structure C = SmtReplayCanonGraph
  structure D = SmtLib_GraphPreprocessDerived
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphNumGuardedArithmetic"
  type producer =
    {propose : G.node -> C.graph_schema option,
     cancel : G.node -> {rule : D.rule,premise : G.node,target : G.node}}
  fun create graph scope {template_limit,check_type} : producer =
    let
      val _ = G.validate_scope graph scope
      val _ = if template_limit > 4 then () else
        raise ERR "create" "insufficient whole arithmetic schema bound"
      fun bounded limit term =
        case SmtReplayImport.bounded_raw_size limit term of SOME _ => ()
        | NONE => raise ERR "schema" "expanded arithmetic schema"
      fun types [] = ()
        | types (term :: rest) =
            (check_type (Term.type_of term);
             if Term.is_abs term then
               let val (variable,body) = Term.dest_abs term in
                 types (variable :: body :: rest) end
             else if Term.is_comb term then
               let val (operator,operand) = Term.dest_comb term in
                 types (operator :: operand :: rest) end
             else types rest)
      val originals = [int_arithTheory.INT_NUM_SUB,HolSmtTheory.INT_NUM_EDIV,
        HolSmtTheory.INT_NUM_EMOD,HolSmtTheory.NUM_TO_INT_GUARDED]
      (* Admit all fixed laws before even type inspection or specialization.
         Cancellation's equality-to-true template needs four extra nodes. *)
      val _ = List.app (bounded (template_limit-4) o Thm.concl) originals
      val _ = List.app (types o (fn theorem => [Thm.concl theorem])) originals
      val laws = List.map Drule.SPEC_ALL originals
      val _ = List.app (bounded (template_limit-4) o Thm.concl) laws
      val _ = List.app (types o (fn theorem => [Thm.concl theorem])) laws
      fun operation theorem =
        let val (left,_) = boolSyntax.dest_eq (Thm.concl theorem)
            val (_,holes) = HolKernel.strip_comb (intSyntax.dest_injected left)
        in if List.length holes = 2 andalso List.all Term.is_var holes then
          (theorem,holes) else raise ERR "schema" "changed operation law" end
      val operations = List.map operation (List.take (laws,3))
      val cancel_law = List.nth (laws,3)
      val (guard,_) = boolSyntax.dest_imp (Thm.concl cancel_law)
      val (_,cancel_hole) = intSyntax.dest_leq guard
      val _ = if Term.is_var cancel_hole then () else
        raise ERR "schema" "changed cancellation law"
      fun visible node =
        let val ty = G.type_of graph node
            val _ = G.validate_scope graph scope
            val _ = if G.scope_visible graph scope (G.node_scope graph node)
              then () else raise ERR "operand" "operand escapes active scope"
            val _ = check_type ty
        in ty end
      fun natural node = if Type.compare (visible node,numSyntax.num) = EQUAL
        then () else raise ERR "operand" "expected natural operand"
      fun propose node =
        (ignore (visible node);
         case SmtReplayRules.spine graph node of
           SOME (injection,[operation]) =>
             if not (Term.same_const injection intSyntax.int_injection)
             then NONE else
             (case SmtReplayRules.spine graph operation of
                SOME (operator,[left,right]) =>
                  let val index =
                    if Term.same_const operator numSyntax.minus_tm then SOME 0
                    else if Term.same_const operator numSyntax.div_tm then SOME 1
                    else if Term.same_const operator numSyntax.mod_tm then SOME 2
                    else NONE
                  in case index of NONE => NONE | SOME index =>
                    let val _ = List.app natural [left,right]
                        val (theorem,holes) = List.nth (operations,index)
                        val schema = C.checked_graph_schema graph scope
                          {theorem = theorem,holes = holes,
                           operands = [left,right],
                           template_limit = template_limit}
                        val _ = if C.graph_schema_source schema = node then ()
                          else raise ERR "propose" "source endpoint changed"
                    in SOME schema end
                  end
              | _ => NONE)
         | _ => NONE)
      fun cancel operand =
        let val _ = if Type.compare (visible operand,intSyntax.int_ty) = EQUAL
              then () else raise ERR "cancel" "expected integer operand"
            val schema = C.checked_graph_schema graph scope
              {theorem = Drule.EQT_INTRO cancel_law,holes = [cancel_hole],
               operands = [operand],template_limit = template_limit}
            val implication = C.graph_schema_source schema
            val (premise,target) = case G.view graph implication of
                G.Application (left,target) => (case G.view graph left of
                    G.Application (operator,premise) =>
                      if Term.same_const (G.representative graph operator)
                        boolSyntax.implication then (premise,target) else
                          raise ERR "cancel" "changed implication operator"
                  | _ => raise ERR "cancel" "changed implication shape")
              | _ => raise ERR "cancel" "changed implication shape"
            val rule = D.checked_rule graph scope
              {theorem = cancel_law,holes = [cancel_hole],operands = [operand],
               premises = [premise],target = target,
               template_limit = template_limit}
        in {rule = rule,premise = premise,target = target} end
    in {propose = propose,cancel = cancel} end
end
