(* Checked arithmetic transfer over graph-owned natural operands. *)
structure SmtLib_GraphNumArithmetic :> SmtLib_GraphNumArithmetic =
struct
  open SmtReplayGraph SmtReplayCanonGraph SmtLib_GraphPreprocessFacts
  structure G = SmtReplayGraph
  structure C = SmtReplayCanonGraph
  structure F = SmtLib_GraphPreprocessFacts
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphNumArithmetic"
  fun bounded_types limit check_type term =
    let
      val _ = case SmtReplayImport.bounded_raw_size limit term of
          SOME _ => () | NONE => raise ERR "law" "expanded numeric law"
      fun visit [] = ()
        | visit (term :: rest) =
            (check_type (Term.type_of term);
             if Term.is_comb term then
               let val (operator,operand) = Term.dest_comb term in
                 visit (operator :: operand :: rest) end
             else if Term.is_abs term then
               let val (variable,body) = Term.dest_abs term in
                 visit (variable :: body :: rest) end
             else visit rest)
    in visit [term] end
  fun specialize limit check_type theorem =
    let
      val _ = if limit > 0 then () else
        raise ERR "law" "nonpositive numeric template bound"
      val _ = bounded_types limit check_type (Thm.concl theorem)
      val theorem = Drule.SPEC_ALL theorem
      val _ = bounded_types limit check_type (Thm.concl theorem)
    in theorem end
  fun natural graph scope check_type operand =
    (if G.scope_visible graph scope (G.node_scope graph operand) andalso
        Type.compare (G.type_of graph operand,numSyntax.num) = EQUAL then ()
     else raise ERR "operand" "expected visible owned natural operand";
     check_type (G.type_of graph operand))
  fun propose graph scope {template_limit,check_type} =
    let
      val _ = G.validate_scope graph scope
      fun law theorem =
        let val theorem = Thm.SYM
              (specialize template_limit check_type theorem)
            val (left,_) = boolSyntax.dest_eq (Thm.concl theorem)
            val operation = intSyntax.dest_injected left
            val (_,holes) = HolKernel.strip_comb operation
            val _ = if List.length holes = 2 andalso
                List.all Term.is_var holes then () else
              raise ERR "propose" "unexpected arithmetic theorem shape"
        in (theorem,holes) end
      val addition = law integerTheory.INT_ADD
      val multiplication = law integerTheory.INT_MUL
      val exponentiation = law integerTheory.INT_EXP
      fun build node =
        (G.validate_scope graph scope;
         case SmtReplayRules.spine graph node of
           SOME (injection,[operation]) =>
             if not (Term.same_const injection intSyntax.int_injection) then
               NONE
             else (case SmtReplayRules.spine graph operation of
               SOME (operator,[left,right]) =>
                 let
                   val selected =
                     if Term.same_const operator numSyntax.plus_tm then
                       SOME addition
                     else if Term.same_const operator numSyntax.mult_tm then
                       SOME multiplication
                     else if Term.same_const operator numSyntax.exp_tm then
                       SOME exponentiation else NONE
                 in case selected of NONE => NONE
                   | SOME (theorem,holes) =>
                       let
                         val _ = List.app
                           (natural graph scope check_type) [left,right]
                         val schema = C.checked_graph_schema graph scope
                           {theorem = theorem,holes = holes,
                            operands = [left,right],
                            template_limit = template_limit}
                         val _ = if C.graph_schema_source schema = node then
                             () else raise ERR "propose"
                               "arithmetic source endpoint differs"
                       in SOME schema end
                 end
             | _ => NONE)
         | _ => NONE)
    in build end
  fun nonnegative graph scope {template_limit,check_type} operand =
    let
      val _ = G.validate_scope graph scope
      val theorem = specialize template_limit check_type integerTheory.INT_POS
      val (_,right) = intSyntax.dest_leq (Thm.concl theorem)
      val hole = intSyntax.dest_injected right
      val _ = if Term.is_var hole then () else
        raise ERR "nonnegative" "unexpected positivity theorem shape"
      val _ = natural graph scope check_type operand
    in F.checked_fact graph scope
      {theorem = theorem,holes = [hole],operands = [operand],
       template_limit = template_limit} end
end
