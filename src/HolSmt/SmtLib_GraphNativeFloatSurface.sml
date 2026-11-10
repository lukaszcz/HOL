structure SmtLib_GraphNativeFloatSurface :> SmtLib_GraphNativeFloatSurface =
struct
  open SmtLib_GraphNativeFloatTransfer SmtReplayGraph SmtReplayCanonGraph
    SmtReplayImport smtfloatTheory binary_ieeeTheory
  structure G = SmtReplayGraph
  structure C = SmtReplayCanonGraph
  structure N = SmtLib_GraphNativeFloatTransfer
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphNativeFloatSurface"
  fun create graph scope
      (options as {template_limit,prefix_depth,check_type}) =
    let
      val base = N.create graph scope options
      val wrapper = Term.prim_mk_const
        {Thy = "smtfloat",Name = "smtfp_rounding_of_binary"}
      fun bound term =
        case SmtReplayImport.bounded_raw_size template_limit term of
          SOME _ => () | NONE => raise ERR "create" "expanded rounding schema"
      val _ = bound (Thm.concl smtfloatTheory.smtfp_rounding_of_binary_def)
      val _ = bound (Thm.concl binary_ieeeTheory.rounding_case_def)
      fun equation name =
        let val mode = Term.prim_mk_const {Thy = "binary_ieee",Name = name}
            val term = Term.mk_comb (wrapper,mode)
            val _ = bound term
            val _ = check_type (Term.type_of wrapper)
            val _ = check_type (Term.type_of mode)
            val theorem = simpLib.SIMP_CONV pureSimps.pure_ss
              [smtfloatTheory.smtfp_rounding_of_binary_def,
               binary_ieeeTheory.rounding_case_def] term
            val _ = bound (Thm.concl theorem)
        in (mode,theorem) end
      val equations = List.map equation ["roundTiesToEven",
        "roundTowardPositive","roundTowardNegative","roundTowardZero"]
      fun lowered_sign theorem =
        let
          val term = Thm.concl theorem
          val size = case SmtReplayImport.bounded_raw_size template_limit
              term of SOME size => size | NONE =>
                raise ERR "create" "expanded sign schema"
          val _ = if size <= (template_limit-3) div 4 then () else
            raise ERR "create" "whole sign conversion exceeds schema limit"
          val conversion = Rewrite.PURE_REWRITE_CONV
            [smtfloatTheory.native_float_classification_transfer] term
          val _ = bound (Thm.concl conversion)
          val result = Thm.EQ_MP conversion theorem
          val _ = bound (Thm.concl result)
        in result end
      val signs = List.map lowered_sign
        (Drule.CONJUNCTS smtfloatTheory.native_float_sign_transfer)
      fun rounding node = case G.view graph node of
          G.Application (operator,operand) =>
            (case (G.view graph operator,G.view graph operand) of
               (G.Constant _,G.Constant _) =>
                 if Term.same_const (G.representative graph operator) wrapper
                 then case List.find (fn (mode,_) => Term.same_const mode
                     (G.representative graph operand)) equations of
                   SOME (_,theorem) => SOME (C.checked_graph_schema
                     graph scope {theorem = theorem,holes = [],operands = [],
                       template_limit = template_limit})
                 | NONE => NONE
                 else NONE
             | _ => NONE)
        | _ => NONE
      val integral = Term.prim_mk_const
        {Thy = "smtfloat",Name = "smtfp_is_integral"}
      val integral_law = smtfloatTheory.smtfp_is_integral_expansion
      val _ = bound (Thm.concl integral_law)
      val (_,generic_equation) = boolSyntax.dest_imp (Thm.concl integral_law)
      val (_,generic_operand) = Term.dest_comb
        (#1 (boolSyntax.dest_eq generic_equation))
      val dimension_ss = simpLib.++
        (simpLib.++ (pureSimps.pure_ss,wordsLib.SIZES_ss),numSimps.REDUCE_ss)
      fun typed_integral node = case G.view graph node of
          G.Application (operator,operand) =>
            (case G.view graph operator of G.Constant _ =>
               if Term.same_const (G.representative graph operator) integral
               then
                 let
                   val ty = G.type_of graph operand
                   val _ = check_type ty
                   val typed = Thm.INST_TYPE (Type.match_type
                     (Term.type_of generic_operand) ty) integral_law
                   val _ = bound (Thm.concl typed)
                   val (guard,_) = boolSyntax.dest_imp (Thm.concl typed)
                   val guard_proof = simpLib.SIMP_CONV dimension_ss [] guard
                   val _ = bound (Thm.concl guard_proof)
                   val (_,result) = boolSyntax.dest_eq (Thm.concl guard_proof)
                 in if Term.is_const result andalso
                     Term.same_const result boolSyntax.T then
                   let
                     val closed = Thm.MP typed (Drule.EQT_ELIM guard_proof)
                     val _ = bound (Thm.concl closed)
                   in C.graph_schema_conversion graph scope
                     {conversion = Rewrite.PURE_REWRITE_CONV [closed],
                      template_limit = template_limit,
                      prefix_depth = prefix_depth} node end
                 else NONE end
               else NONE
             | _ => NONE)
        | _ => NONE
      fun propose node =
        case (#propose base) node of SOME schema => SOME schema
        | NONE => (case G.view graph node of
            G.OpaqueRetained => NONE | G.AdmittedBinder _ => NONE
          | _ => (case typed_integral node of SOME schema => SOME schema
            | NONE => (case rounding node of SOME schema => SOME schema
              | NONE => C.graph_schema_conversion graph scope
                  {conversion = Rewrite.PURE_REWRITE_CONV signs,
                   template_limit = template_limit,prefix_depth = prefix_depth}
                  node)))
    in {propose = propose,aliases = #aliases base,
        install_aliases = #install_aliases base} end
end
