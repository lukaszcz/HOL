structure SmtSkeletonProve =
struct

  open HolKernel

  val ERR = Feedback.mk_HOL_ERR "SmtSkeletonProve"

  type atom_procedure =
    {name : string, owns : term -> bool, expand : term -> thm}

  datatype context = Context of
    {procedures : atom_procedure list,
     atom_cache : (term, thm) Redblackmap.dict ref}

  type metrics =
    {target_tree_nodes : int,
     target_dag_nodes : int,
     skeleton_dag_nodes : int,
     normalized_tree_nodes : int,
     normalized_dag_nodes : int,
     sat_tree_nodes : int,
     sat_dag_nodes : int,
     distinct_atoms : int,
     atom_requests : int,
     atom_proofs : int,
     atom_cache_hits : int,
     node_cache_hits : int,
     residual_atoms : int,
     atom_seconds : Time.time,
     sat_seconds : Time.time,
     total_seconds : Time.time,
     procedure_calls : (string * int) list}

  fun new_context procedures = Context
    {procedures = procedures,
     atom_cache = ref (Redblackmap.mkDict Term.compare)}

  fun cache_size (Context {atom_cache, ...}) =
    Redblackmap.numItems (!atom_cache)

  fun term_children term =
    if Term.is_comb term then
      let val (operator, operand) = Term.dest_comb term
      in [operator, operand] end
    else if Term.is_abs term then
      let val (_, body) = Term.dest_abs term in [body] end
    else []

  fun term_measure term =
    let
      (* The count is the unfolded tree size, but each DAG node is visited
         once.  Metrics must not accidentally materialize the proof tree. *)
      val sizes = ref (Redblackmap.mkDict Term.compare)
      fun visit term =
        case Redblackmap.peek (!sizes, term) of
          SOME size => size
        | NONE =>
            let
              val size = List.foldl
                (fn (child, result) => result + visit child)
                1 (term_children term)
              val _ = sizes := Redblackmap.insert (!sizes, term, size)
            in
              size
            end
    in
      {tree_nodes = visit term, dag_nodes = Redblackmap.numItems (!sizes)}
    end

  fun tree_nodes term = #tree_nodes (term_measure term)

  fun dag_nodes term = #dag_nodes (term_measure term)

  fun skeleton_children term =
    if Term.aconv term boolSyntax.T orelse
       Term.aconv term boolSyntax.F then SOME []
    else if boolSyntax.is_neg term then
      SOME [boolSyntax.dest_neg term]
    else if boolSyntax.is_conj term then
      let val (left, right) = boolSyntax.dest_conj term
      in SOME [left, right] end
    else if boolSyntax.is_disj term then
      let val (left, right) = boolSyntax.dest_disj term
      in SOME [left, right] end
    else if boolSyntax.is_imp term then
      let val (left, right) = boolSyntax.dest_imp term
      in SOME [left, right] end
    else if boolSyntax.is_cond term andalso Term.type_of term = Type.bool then
      let val (test, yes, no) = boolSyntax.dest_cond term
      in SOME [test, yes, no] end
    else if boolSyntax.is_eq term then
      let val (left, right) = boolSyntax.dest_eq term
      in
        if Term.type_of left = Type.bool then SOME [left, right]
        else NONE
      end
    else NONE

  fun connective_congruence term child_theorems =
    let
      val (head, arguments) = boolSyntax.strip_comb term
      val _ =
        if List.length arguments = List.length child_theorems then ()
        else raise ERR "connective_congruence"
          "propositional connective arity changed"
    in
      List.foldl
        (fn (child_theorem, theorem) =>
          Thm.MK_COMB (theorem, child_theorem))
        (Thm.REFL head) child_theorems
    end

  fun validate_theorem procedure atom theorem =
    let
      val _ =
        if List.null (Thm.hyp theorem) then ()
        else raise ERR "validate_theorem"
          ("atom procedure " ^ procedure ^ " returned hypotheses")
      val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
        handle Feedback.HOL_ERR _ =>
          raise ERR "validate_theorem"
            ("atom procedure " ^ procedure ^
             " did not return an equality")
      val _ =
        if Term.aconv left atom then ()
        else raise ERR "validate_theorem"
          ("atom procedure " ^ procedure ^ " returned the wrong left side")
      val _ =
        if Term.type_of right = Type.bool then ()
        else raise ERR "validate_theorem"
          ("atom procedure " ^ procedure ^ " returned a non-Boolean residue")
      val _ =
        if Term.aconv left right then
          raise ERR "validate_theorem"
            ("atom procedure " ^ procedure ^ " made no progress")
        else ()
      val _ = Library.check_oracle_tags
        "SmtSkeletonProve" ("atom:" ^ procedure) theorem
    in
      theorem
    end

  fun choose_owner procedures atom =
    case List.filter (fn {owns, ...} => owns atom) procedures of
      [] => NONE
    | [procedure] => SOME procedure
    | owners =>
        raise ERR "choose_owner"
          ("ambiguous theory atom owners: " ^
           String.concatWith "," (List.map #name owners))

  (* Force HolSat's checked equality-to-T path; EQT_ELIM recovers the
     requested theorem by a kernel inference. *)
  fun checked_sat_prove sat_target =
    let
      val request = boolSyntax.mk_eq (sat_target, boolSyntax.T)
      val equality = HolSatLib.SAT_PROVE request
      val _ =
        if List.null (Thm.hyp equality) then ()
        else raise ERR "checked_sat_prove"
          "checked SAT equality has hypotheses"
      val _ =
        if Term.aconv (Thm.concl equality) request then ()
        else raise ERR "checked_sat_prove"
          "checked SAT equality does not match its request"
      val _ = Library.check_oracle_tags
        "SmtSkeletonProve" "checked-sat-equality" equality
      val theorem = Drule.EQT_ELIM equality
      val _ =
        if Term.aconv (Thm.concl theorem) sat_target then ()
        else raise ERR "checked_sat_prove"
          "EQT_ELIM did not recover the abstract skeleton"
    in
      theorem
    end

  val idempotent_variable = Term.mk_var ("p", Type.bool)
  val disj_idempotent = tautLib.TAUT_PROVE
    (boolSyntax.mk_eq
      (boolSyntax.mk_disj (idempotent_variable, idempotent_variable),
       idempotent_variable))
  val conj_idempotent = tautLib.TAUT_PROVE
    (boolSyntax.mk_eq
      (boolSyntax.mk_conj (idempotent_variable, idempotent_variable),
       idempotent_variable))

  fun normalize_idempotent_skeleton skeleton =
    let
      val nodes = ref (Redblackmap.mkDict Term.compare)
      fun visit term =
        case skeleton_children term of
          NONE => Thm.REFL term
        | SOME [] => Thm.REFL term
        | SOME children =>
            (case Redblackmap.peek (!nodes, term) of
               SOME theorem => theorem
             | NONE =>
                 let
                   val congruence = connective_congruence term
                     (List.map visit children)
                   val rebuilt = boolSyntax.rhs (Thm.concl congruence)
                   val theorem =
                     if boolSyntax.is_disj rebuilt then
                       let val (left, right) = boolSyntax.dest_disj rebuilt
                       in
                         if Term.aconv left right then
                           Thm.TRANS congruence
                             (Conv.REWR_CONV disj_idempotent rebuilt)
                         else congruence
                       end
                     else if boolSyntax.is_conj rebuilt then
                       let val (left, right) = boolSyntax.dest_conj rebuilt
                       in
                         if Term.aconv left right then
                           Thm.TRANS congruence
                             (Conv.REWR_CONV conj_idempotent rebuilt)
                         else congruence
                       end
                     else congruence
                   val _ = nodes :=
                     Redblackmap.insert (!nodes, term, theorem)
                 in
                   theorem
                 end)
    in
      visit skeleton
    end

  (* Turn the shared abstract skeleton into an explicitly linear
     definitional implication.  HolSat sees each connective node once.  Its
     checked theorem is instantiated back with the original DAG nodes, whose
     defining equations are then discharged by reflexivity. *)
  fun linear_sat_target skeleton =
    let
      val nodes = ref (Redblackmap.mkDict Term.compare)
      val definitions = ref []
      fun visit term =
        case skeleton_children term of
          NONE => term
        | SOME [] => term
        | SOME children =>
            (case Redblackmap.peek (!nodes, term) of
               SOME variable => variable
             | NONE =>
                 let
                   val (head, _) = boolSyntax.strip_comb term
                   val body = List.foldl
                     (fn (child, function) => Term.mk_comb (function, child))
                     head (List.map visit children)
                   val variable = Term.genvar Type.bool
                   val equation = boolSyntax.mk_eq (variable, body)
                   val _ = nodes :=
                     Redblackmap.insert (!nodes, term, variable)
                   val _ = definitions :=
                     (equation, variable, term) :: !definitions
                 in
                   variable
                 end)
      val root = visit skeleton
      val entries = List.rev (!definitions)
      val equations = List.map
        (fn (equation, _, _) => equation) entries
      val antecedent =
        case equations of
          [] => boolSyntax.T
        | _ => boolSyntax.list_mk_conj equations
      val target = boolSyntax.mk_imp
        (antecedent, root)
      val substitution = List.map
        (fn (_, variable, term) => variable |-> term) entries
      val definition_theorem =
        case entries of
          [] => boolTheory.TRUTH
        | _ => Drule.LIST_CONJ
            (List.map (fn (_, _, term) => Thm.REFL term) entries)
    in
      {target = target,
       substitution = substitution,
       definition_theorem = definition_theorem}
    end

  fun checked_sat_skeleton_prove skeleton =
    let
      val normalization = normalize_idempotent_skeleton skeleton
      val normalized = boolSyntax.rhs (Thm.concl normalization)
      val {target, substitution, definition_theorem} =
        linear_sat_target normalized
      val target_theorem = checked_sat_prove target
      val instantiated = Thm.INST substitution target_theorem
      val normalized_theorem = Thm.MP instantiated definition_theorem
      val _ =
        if Term.aconv (Thm.concl normalized_theorem) normalized then ()
        else raise ERR "checked_sat_skeleton_prove"
          "checked definitions did not return the normalized skeleton"
      val theorem = Thm.EQ_MP (Thm.SYM normalization) normalized_theorem
      val _ =
        if Term.aconv (Thm.concl theorem) skeleton then ()
        else raise ERR "checked_sat_skeleton_prove"
          "checked SAT reconstruction returned the wrong skeleton"
    in
      {theorem = theorem, sat_target = target}
    end

  fun abstract_skeleton skeleton =
    let
      (* HolSatLib accepts a purely propositional term.  Preserve every
         connective and replace only residual Boolean leaves; instantiating
         its checked theorem afterwards is a kernel operation. *)
      val nodes = ref (Redblackmap.mkDict Term.compare)
      val atoms = ref (Redblackmap.mkDict Term.compare)
      fun atom term =
        case Redblackmap.peek (!atoms, term) of
          SOME variable => variable
        | NONE =>
            let
              val variable = Term.genvar Type.bool
              val _ = atoms := Redblackmap.insert (!atoms, term, variable)
            in
              variable
            end
      fun visit term =
        case skeleton_children term of
          NONE => atom term
        | SOME [] => term
        | SOME children =>
            (case Redblackmap.peek (!nodes, term) of
               SOME result => result
             | NONE =>
                 let
                   val (head, _) = boolSyntax.strip_comb term
                   val result = List.foldl
                     (fn (child, function) =>
                       Term.mk_comb (function, child))
                     head (List.map visit children)
                   val _ =
                     nodes := Redblackmap.insert (!nodes, term, result)
                 in
                   result
                 end)
      val abstracted = visit skeleton
      val substitution = Redblackmap.foldl
        (fn (actual, variable, result) =>
          (variable |-> actual) :: result) [] (!atoms)
    in
      (abstracted, substitution, Redblackmap.numItems (!atoms))
    end

  fun prove (Context {procedures, atom_cache}) target =
    let
      val _ =
        if Term.type_of target = Type.bool then ()
        else raise ERR "prove" "target is not Boolean"
      val _ =
        case skeleton_children target of
          NONE => raise ERR "prove"
            "whole obligation is a theory atom; local solve is forbidden"
        | SOME _ => ()
      val total_timer = Timer.startRealTimer ()
      val target_measure = term_measure target
      val nodes = ref (Redblackmap.mkDict Term.compare)
      val skeleton_nodes = ref (HOLset.empty Term.compare)
      val distinct_atoms = ref (HOLset.empty Term.compare)
      val calls = ref (Redblackmap.mkDict String.compare)
      val node_hits = ref 0
      val atom_requests = ref 0
      val atom_proofs = ref 0
      val atom_hits = ref 0
      val atom_time = ref Time.zeroTime
      val owned_atoms = ref 0
      fun add_call name =
        let
          val count = Option.getOpt (Redblackmap.peek (!calls, name), 0)
        in
          calls := Redblackmap.insert (!calls, name, count + 1)
        end
      fun expand atom =
        case choose_owner procedures atom of
          NONE => Thm.REFL atom
        | SOME {name, expand, ...} =>
            let
              val _ = owned_atoms := !owned_atoms + 1
              val _ = atom_requests := !atom_requests + 1
              val _ = distinct_atoms := HOLset.add (!distinct_atoms, atom)
            in
              case Redblackmap.peek (!atom_cache, atom) of
                SOME theorem => (atom_hits := !atom_hits + 1; theorem)
              | NONE =>
                  let
                    val timer = Timer.startRealTimer ()
                    val _ = add_call name
                    val theorem = validate_theorem name atom (expand atom)
                    val elapsed = Timer.checkRealTimer timer
                    val _ = atom_time := Time.+ (!atom_time, elapsed)
                    val _ = atom_cache :=
                      Redblackmap.insert (!atom_cache, atom, theorem)
                    val _ = atom_proofs := !atom_proofs + 1
                  in
                    theorem
                  end
            end
      fun visit term =
        let
          val _ = skeleton_nodes := HOLset.add (!skeleton_nodes, term)
        in
          case skeleton_children term of
            NONE => expand term
          | SOME children =>
              (case Redblackmap.peek (!nodes, term) of
                 SOME theorem => (node_hits := !node_hits + 1; theorem)
               | NONE =>
                   let
                     val theorem = connective_congruence term
                       (List.map visit children)
                     val _ = nodes :=
                       Redblackmap.insert (!nodes, term, theorem)
                   in
                     theorem
                   end)
        end
      val normalization = visit target
      val normalized = boolSyntax.rhs (Thm.concl normalization)
      val _ =
        if !owned_atoms > 0 andalso Term.aconv normalized target then
          raise ERR "prove" "atom expansion made no progress"
        else ()
      val (abstracted, residual_substitution, residual_count) =
        abstract_skeleton normalized
      val sat_timer = Timer.startRealTimer ()
      val {theorem = abstract_theorem, sat_target} =
        checked_sat_skeleton_prove abstracted
      val _ =
        if List.null (Thm.hyp abstract_theorem) then ()
        else raise ERR "prove" "checked SAT theorem has hypotheses"
      val _ =
        if Term.aconv (Thm.concl abstract_theorem) abstracted then ()
        else raise ERR "prove"
          "checked SAT theorem does not match the abstract skeleton"
      val _ = Library.check_oracle_tags
        "SmtSkeletonProve" "checked-sat" abstract_theorem
      val normalized_theorem =
        Thm.INST residual_substitution abstract_theorem
      val _ =
        if Term.aconv (Thm.concl normalized_theorem) normalized then ()
        else raise ERR "prove"
          "checked SAT reconstruction did not return the normalized target"
      val sat_time = Timer.checkRealTimer sat_timer
      val theorem = Thm.EQ_MP (Thm.SYM normalization) normalized_theorem
      val _ =
        if List.null (Thm.hyp theorem) then ()
        else raise ERR "prove" "result theorem has hypotheses"
      val _ =
        if Term.aconv (Thm.concl theorem) target then ()
        else raise ERR "prove" "result theorem does not match the target"
      val _ = Library.check_oracle_tags
        "SmtSkeletonProve" "result" theorem
      val total_time = Timer.checkRealTimer total_timer
      val normalized_measure = term_measure normalized
      val sat_measure = term_measure sat_target
      val procedure_calls = Redblackmap.foldl
        (fn (name, count, result) => (name, count) :: result) [] (!calls)
      val metrics =
        {target_tree_nodes = #tree_nodes target_measure,
         target_dag_nodes = #dag_nodes target_measure,
         skeleton_dag_nodes = HOLset.numItems (!skeleton_nodes),
         normalized_tree_nodes = #tree_nodes normalized_measure,
         normalized_dag_nodes = #dag_nodes normalized_measure,
         sat_tree_nodes = #tree_nodes sat_measure,
         sat_dag_nodes = #dag_nodes sat_measure,
         distinct_atoms = HOLset.numItems (!distinct_atoms),
         atom_requests = !atom_requests,
         atom_proofs = !atom_proofs,
         atom_cache_hits = !atom_hits,
         node_cache_hits = !node_hits,
         residual_atoms = residual_count,
         atom_seconds = !atom_time,
         sat_seconds = sat_time,
         total_seconds = total_time,
         procedure_calls = procedure_calls}
    in
      {theorem = theorem, metrics = metrics}
    end

end
