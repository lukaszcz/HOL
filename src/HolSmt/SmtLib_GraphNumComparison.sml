(* Copyright (c) 2026 The HOL4 contributors. *)

structure SmtLib_GraphNumComparison :> SmtLib_GraphNumComparison =
struct
  open SmtReplayGraph SmtReplayCanonGraph
  structure G = SmtReplayGraph
  structure C = SmtReplayCanonGraph
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphNumComparison"
  fun bounded_types limit check_type term =
    let
      val _ = case SmtReplayImport.bounded_raw_size limit term of
          SOME _ => () | NONE => raise ERR "propose" "expanded numeric law"
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
  fun propose graph scope {template_limit,check_type} =
    let
      val _ = G.validate_scope graph scope
      val _ = if template_limit > 0 then () else
        raise ERR "propose" "nonpositive numeric template bound"
      fun specialize theorem =
        let
          val _ = bounded_types template_limit check_type (Thm.concl theorem)
          val theorem = Thm.SYM (Drule.SPEC_ALL theorem)
          val _ = bounded_types template_limit check_type (Thm.concl theorem)
          val (left,_) = boolSyntax.dest_eq (Thm.concl theorem)
          val (_,holes) = HolKernel.strip_comb left
          val _ = if List.length holes = 2 andalso
              List.all Term.is_var holes then () else
            raise ERR "propose" "unexpected fixed comparison law"
        in (theorem,holes) end
      val less = specialize integerTheory.INT_LT
      val leq = specialize integerTheory.INT_LE
      val equality = specialize integerTheory.INT_INJ
      fun build node =
        (G.validate_scope graph scope;
         case SmtReplayRules.spine graph node of
           SOME (head,[left,right]) =>
             if Type.compare (G.type_of graph left,numSyntax.num) <> EQUAL
                 orelse Type.compare (G.type_of graph right,numSyntax.num)
                   <> EQUAL then NONE
             else
               let
                 val law = if Term.same_const head numSyntax.less_tm then
                     SOME less
                   else if Term.same_const head numSyntax.leq_tm then SOME leq
                   else if Term.same_const head boolSyntax.equality then
                     SOME equality else NONE
               in case law of NONE => NONE
                 | SOME (theorem,holes) =>
                     let
                       val _ = List.app (check_type o G.type_of graph)
                         [left,right]
                       val schema = C.checked_graph_schema graph scope
                         {theorem = theorem,holes = holes,
                          operands = [left,right],
                          template_limit = template_limit}
                       val _ = if C.graph_schema_source schema = node then ()
                         else raise ERR "propose" "wrong comparison endpoint"
                     in SOME schema end end
         | _ => NONE)
    in build end
  fun injections graph roots =
    let val injection = intSyntax.int_injection
        fun included node = case G.view graph node of
            G.Application (head,operand) =>
              (case G.view graph head of G.Constant _ =>
                 Term.same_const (G.representative graph head) injection
                 andalso Type.compare (G.type_of graph operand,numSyntax.num)
                   = EQUAL
               | _ => false)
          | _ => false
    in List.filter included (G.block_reachable graph roots) end
end
