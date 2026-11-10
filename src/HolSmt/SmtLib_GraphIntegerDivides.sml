structure SmtLib_GraphIntegerDivides :> SmtLib_GraphIntegerDivides =
struct
  open SmtReplayGraph SmtReplayCanonGraph SmtReplayRules SmtReplayImport
    integerTheory SmtLib
  structure G = SmtReplayGraph
  structure C = SmtReplayCanonGraph
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphIntegerDivides"
  fun thm_rhs_is_true th =
  let
    val (_, rhs) = boolSyntax.dest_eq (Thm.concl th)
  in
    Term.aconv rhs boolSyntax.T
  end

  fun literal_conversion tm =
  let
    val (divisor, _) = intSyntax.dest_divides tm
    val zero = intSyntax.term_of_int Arbint.zero
    val _ =
      if intSyntax.is_int_literal divisor then ()
      else raise ERR "literal_conversion" "non-literal divisor"
    val pos_th =
      simpLib.SIMP_CONV intLib.int_ss []
        (intSyntax.mk_less (zero, divisor))
    val _ =
      if thm_rhs_is_true pos_th then ()
      else raise ERR "literal_conversion" "non-positive divisor"
    val nz_th =
      simpLib.SIMP_CONV intLib.int_ss []
        (boolSyntax.mk_neg (boolSyntax.mk_eq (divisor, zero)))
    val z_th =
      simpLib.SIMP_CONV intLib.int_ss []
        (boolSyntax.mk_eq (divisor, zero))
  in
    Conv.THENC
      (Conv.REWR_CONV integerTheory.INT_DIVIDES_MOD0,
       simpLib.SIMP_CONV pureSimps.pure_ss [
         pos_th, nz_th, z_th, integerTheory.INT_MOD_EMOD,
         boolTheory.COND_CLAUSES, boolTheory.AND_CLAUSES,
         boolTheory.OR_CLAUSES
       ]) tm
  end

  fun propose graph scope {template_limit,check_type} =
    let
      val _ = G.validate_scope graph scope
      val _ = if template_limit > 0 then () else
        raise ERR "propose" "nonpositive integer-divides template contract"
      fun size term = SmtReplayImport.bounded_raw_size template_limit term
      fun bounded term = case size term of SOME count => count
        | NONE => raise ERR "propose" "whole divides schema exceeds quota"
      fun types [] = ()
        | types (term :: pending) =
            (check_type (Term.type_of term);
             if Term.is_comb term then
               let val (operator,operand) = Term.dest_comb term in
                 types (operator :: operand :: pending) end
             else if Term.is_abs term then
               let val (variable,body) = Term.dest_abs term in
                 types (variable :: body :: pending) end
             else types pending)
      val fixed = [integerTheory.INT_DIVIDES_MOD0,integerTheory.INT_MOD_EMOD,
        boolTheory.COND_CLAUSES,boolTheory.AND_CLAUSES,boolTheory.OR_CLAUSES]
      val conclusions = List.map Thm.concl fixed
      val fixed_sizes = List.map bounded conclusions
      val _ = types conclusions
      val schematic_bound = List.foldl Int.max 1 fixed_sizes
      val memo = ref (Redblackmap.mkDict Int.compare)
      fun law divisor = case Redblackmap.peek (!memo,G.node_id divisor) of
          SOME result => result
        | NONE =>
            let
              val literal = G.representative graph divisor
              val result = case size literal of NONE => NONE
                | SOME literal_size =>
                    (* The actual literal can occur only within these fixed
                       small laws. Admit whole specialization
                       and arithmetic-side-law bound before type/proof work.
                       An optional overflow needs ordinary continuation. *)
                    if template_limit < 20 orelse literal_size >
                        (template_limit-20) div schematic_bound then NONE
                    else if not (intSyntax.is_int_literal literal) then NONE
                    else if not (Arbint.<
                        (Arbint.zero,intSyntax.int_of_term literal)) then NONE
                    else
                      let
                        val _ = types [literal]
                        val hole = Term.mk_var
                          ("integer_divides_dividend",intSyntax.int_ty)
                        val prefix = intSyntax.mk_divides (literal,hole)
                        val _ = ignore (bounded prefix)
                        val theorem = literal_conversion prefix
                        val _ = ignore (bounded (Thm.concl theorem))
                        val _ = types [Thm.concl theorem]
                      in SOME (hole,theorem) end
              val _ = memo := Redblackmap.insert
                (!memo,G.node_id divisor,result)
            in result end
      fun visible node =
        (G.validate_scope graph scope;
         ignore (G.type_of graph node);
         if G.scope_visible graph scope (G.node_scope graph node) then () else
           raise ERR "propose" "divides operand escapes active scope")
      fun proposal node =
        (visible node;
         case SmtReplayRules.spine graph node of
           SOME (operator,[divisor,dividend]) =>
             if not (Term.same_const operator intSyntax.divides_tm) then NONE
             else
               let
                 val _ = List.app visible [divisor,dividend]
               in case law divisor of NONE => NONE
                 | SOME (hole,theorem) =>
                     let
                       val schema = C.checked_graph_schema graph scope
                         {theorem = theorem,holes = [hole],
                          operands = [dividend],
                          template_limit = template_limit}
                       val _ = if C.graph_schema_source schema = node then ()
                         else raise ERR "propose"
                           "literal divides source endpoint differs"
                     in SOME schema end
               end
         | _ => NONE)
    in proposal end
end
