(* Optional parser-canonical constructor candidates. This is metadata, NOT
   equality evidence: retain_producer_conclusion must check the candidate.
   Only the bounded schema is traversed; its holes retain the exact source
   occurrences, even when those operands are not parser-canonical. *)
structure CPC_ProducerCandidate =
struct
local
  exception Declined
  datatype plan = Hole of Term.term
    | Atom of Term.term
    | App of Term.term * plan * plan

  val maximum = SmtResource.max_skeleton_replay_dag_nodes

  fun prepare template operands actual =
    let
      (* Use the original physical-DAG ceiling, but reject binders BEFORE
         the metric can open them. The subsequent raw-tree bound therefore
         also never opens a binder or observes an opaque operand. *)
      fun no_binder term =
        if Term.is_abs term then raise Declined else ()
      val _ =
        if SmtResource.dag_nodes_up_to_with_inspector no_binder
             maximum template <= maximum andalso
           Option.isSome
             (SmtReplayImport.bounded_raw_size maximum template) then ()
        else raise Declined
      val admission = SmtWordGraph.new_type_admission ()
      fun admit term =
        SmtWordGraph.admit_primitive_type admission (Term.type_of term)
      (* Bound even an ill-shaped or mostly unused operand association list.
         Neither lookup nor validation compares operands semantically. *)
      fun admit_operands _ [] = ()
        | admit_operands remaining ((variable,operand)::rest) =
            if remaining = 0 orelse not (Term.is_var variable) then
              raise Declined
            else
              (admit variable; admit operand;
               admit_operands (remaining - 1) rest)
      val _ = admit_operands maximum operands
      fun visit pattern source =
        case List.find (fn (variable,_) =>
            Portable.pointer_eq (pattern,variable)) operands of
          SOME (_,operand) =>
            if Portable.pointer_eq (source,operand) then Hole operand
            else raise Declined
        | NONE =>
            if Term.is_comb pattern andalso Term.is_comb source then
              let
                val (operator,operand) = Term.dest_comb pattern
                val (source_operator,source_operand) = Term.dest_comb source
                val operator_plan = visit operator source_operator
                val operand_plan = visit operand source_operand
                val _ = admit pattern
                val _ = admit source
              in App (source,operator_plan,operand_plan) end
            else if (Term.is_var pattern andalso Term.is_var source) orelse
                    (Term.is_const pattern andalso Term.is_const source) then
              (admit pattern; admit source;
               if Term.aconv pattern source then Atom source
               else raise Declined)
            else raise Declined
    in visit template actual end

  (* All topology and Type admission is complete before the first parser
     lookup. Shell lookup never recursively canonicalizes children. In
     particular, Hole must NOT pass through even the shell interner. *)
  fun realize (Hole operand) = operand
    | realize (Atom source) = CPC_ProofParser.intern_cpc_shell source
    | realize (App (source,operator_plan,operand_plan)) =
        let
          val operator = realize operator_plan
          val operand = realize operand_plan
          val (source_operator,source_operand) = Term.dest_comb source
          val rebuilt =
            if Portable.pointer_eq (operator,source_operator) andalso
               Portable.pointer_eq (operand,source_operand) then source
            else Term.mk_comb (operator,operand)
        in CPC_ProofParser.intern_cpc_shell rebuilt end
in
  (* Optional selection only: decline without a retry or an alternative
     semantic search. Unexpected exceptions retain their original identity. *)
  fun candidate template operands actual : Term.term =
    realize (prepare template operands actual)
    handle Declined => actual
         | Conv.UNCHANGED => actual
         | error as Feedback.HOL_ERR detail =>
             if SmtResource.is_resource_gate detail then actual
             else raise error
end
end
