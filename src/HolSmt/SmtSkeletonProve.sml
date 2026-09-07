structure SmtSkeletonProve =
struct

  open HolKernel

  val ERR = Feedback.mk_HOL_ERR "SmtSkeletonProve"

  datatype expansion = Expanded of thm | Unable

  type atom_procedure =
    {name : string, expand : term -> expansion}

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
     node_cache_pointer_hits : int,
     node_cache_structural_reanchor_attempts : int,
     node_cache_structural_reanchor_successes : int,
     node_cache_structural_reanchor_fallbacks : int,
     node_cache_reanchor_seconds : Time.time,
     residual_atoms : int,
     atom_seconds : Time.time,
     sat_seconds : Time.time,
     total_seconds : Time.time,
     procedure_calls : (string * int) list}

  datatype node_cache_event =
      NodeCachePointerHit
    | NodeCacheStructuralReanchorAttempt
    | NodeCacheStructuralReanchorSuccess
    | NodeCacheStructuralReanchorFallback
    | NodeCacheReanchorTime of Time.time

  val node_cache_observer =
    ref (NONE : (node_cache_event -> unit) option)

  val sat_target_observer = ref (NONE : (term -> unit) option)
  val sat_completion_observer =
    ref (NONE : ((term * Time.time) -> unit) option)

  fun with_node_cache_observer observer action input =
    let
      val previous = !node_cache_observer
      fun restore () = node_cache_observer := previous
      fun run () = (node_cache_observer := observer; action input)
    in
      Portable.finally restore run ()
    end

  fun observe_node_cache event =
    case !node_cache_observer of
      NONE => ()
    | SOME observer => observer event

  fun with_sat_target_observer observer action input =
    let
      val previous = !sat_target_observer
      fun restore () = sat_target_observer := previous
      fun run () = (sat_target_observer := observer; action input)
    in
      Portable.finally restore run ()
    end

  fun observe_sat_target target =
    case !sat_target_observer of
      NONE => ()
    | SOME observer => observer target

  fun with_sat_observers target_observer completion_observer action input =
    let
      val previous_target = !sat_target_observer
      val previous_completion = !sat_completion_observer
      fun restore () =
        (sat_target_observer := previous_target;
         sat_completion_observer := previous_completion)
      fun run () =
        (sat_target_observer := target_observer;
         sat_completion_observer := completion_observer;
         action input)
    in
      Portable.finally restore run ()
    end

  fun new_context procedures = Context
    {procedures = procedures,
     atom_cache = ref (Redblackmap.mkDict Term.compare)}

  fun cache_size (Context {atom_cache, ...}) =
    Redblackmap.numItems (!atom_cache)

  (* Admission and proof reconstruction share this exact DAG-aware metric.
     In particular, String dispatch must not reject a compact shared term by
     its exponentially larger unfolded tree before this engine sees it. *)
  val max_metric = SmtResource.max_metric
  val saturated_add = SmtResource.saturated_add
  val term_children = SmtResource.term_children
  val term_measure = SmtResource.term_measure
  val phase = SmtResource.profile_phase

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

  (* Congruence reconstructs an alpha-equal left side from its children.
     Anchor it to the caller's existing node immediately.  Because recursive
     results maintain the same invariant, the kernel comparison at each
     anchor sees the original child pointers and remains local to one node. *)
  fun anchor_left term theorem =
    Thm.TRANS (Thm.REFL term) theorem

  fun anchor_right term theorem =
    Thm.TRANS theorem (Thm.REFL term)

  (* Redblackmap keys are structural.  Keep separate entries for equal terms
     with different physical identities when a cached value embeds the exact
     occurrence. *)
  fun pointer_cache_peek dictionary term =
    case Redblackmap.peek (dictionary, term) of
      NONE => NONE
    | SOME bucket =>
        case List.find
            (fn (saved, _) => Portable.pointer_eq (term, saved)) bucket of
          NONE => NONE
        | SOME (_, value) => SOME value

  fun pointer_cache_insert dictionary term value =
    let
      val bucket = Option.getOpt (Redblackmap.peek (dictionary, term), [])
    in
      Redblackmap.insert (dictionary, term, (term, value) :: bucket)
    end

  exception REANCHOR_LIMIT

  (* Build left = right one physical node at a time.  Both endpoint anchors
     compare only a newly built outer node whose children already have the
     requested endpoint pointers.  Structural cache collisions use separate
     pointer buckets, and the fixed skeleton DAG limit bounds reconstruction. *)
  fun bounded_nodewise_equality maximum left right =
    let
      val _ =
        if SmtResource.dag_nodes_up_to maximum left <= maximum then ()
        else raise REANCHOR_LIMIT
      val compared = ref 0
      val cache = ref ([] : (term * term * thm) list)
      fun visit (left, right) =
        if Portable.pointer_eq (left, right) then Thm.REFL left
        else
          case List.find
              (fn (saved_left, saved_right, _) =>
                Portable.pointer_eq (left, saved_left) andalso
                Portable.pointer_eq (right, saved_right)) (!cache) of
            SOME (_, _, theorem) => theorem
          | NONE => compute (left, right)
      and compute (left, right) =
        let
          val _ = compared := !compared + 1
          val _ = if !compared <= maximum then () else raise REANCHOR_LIMIT
          val theorem =
            if Term.is_comb left andalso Term.is_comb right then
              let
                val (left_operator, left_operand) = Term.dest_comb left
                val (right_operator, right_operand) = Term.dest_comb right
              in
                anchor_right right (anchor_left left
                  (Thm.MK_COMB
                    (visit (left_operator, right_operator),
                     visit (left_operand, right_operand))))
              end
            else if Term.is_abs left andalso Term.is_abs right then
              let
                val (left_binder, left_body) = Term.dest_abs left
                val (_, right_body) = Term.dest_abs right
              in
                anchor_right right (anchor_left left
                  (Thm.ABS left_binder (visit (left_body, right_body))))
              end
            else
              Thm.TRANS (Thm.REFL left) (Thm.REFL right)
          val _ = cache := (left, right, theorem) :: !cache
        in
          theorem
        end
      val theorem = visit (left, right)
      val (actual_left, actual_right) =
        boolSyntax.dest_eq (Thm.concl theorem)
      val _ =
        if Portable.pointer_eq (left, actual_left) andalso
           Portable.pointer_eq (right, actual_right) then ()
        else raise ERR "bounded_nodewise_equality"
          "node-wise transport lost an endpoint occurrence"
    in
      theorem
    end

  fun reanchor_cached_theorem occurrence theorem =
    let
      val (cached_left, _) = boolSyntax.dest_eq (Thm.concl theorem)
      val occurrence_equality = bounded_nodewise_equality
        SmtResource.max_skeleton_replay_dag_nodes occurrence cached_left
    in
      Thm.TRANS occurrence_equality theorem
    end

  fun exact_left occurrence theorem =
    let val (left, _) = boolSyntax.dest_eq (Thm.concl theorem)
    in
      if Portable.pointer_eq (occurrence, left) then theorem
      else reanchor_cached_theorem occurrence theorem
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

  fun procedure_names (Context {procedures, ...}) =
    List.map #name procedures

  fun procedure_named procedures name =
    case List.filter (fn procedure => #name procedure = name) procedures of
      [procedure] => procedure
    | [] => raise ERR "procedure_named"
        ("unknown classified atom owner: " ^ name)
    | _ => raise ERR "procedure_named"
        ("duplicate classified atom owner: " ^ name)

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
        let
          fun compute () = case skeleton_children term of
          NONE => (Thm.REFL term, false)
        | SOME [] => (Thm.REFL term, false)
        | SOME children =>
                 let
                   val child_results = List.map visit children
                   val child_changed = List.exists Lib.snd child_results
                   (* Preserve structural cache sharing while normalizing.
                      The completed root equality is anchored once below;
                      anchoring every structurally equal cache hit repeats
                      the same transport throughout an expanded word DAG. *)
                   val congruence =
                     if child_changed then
                       connective_congruence term
                         (List.map Lib.fst child_results)
                     else Thm.REFL term
                   val rebuilt = boolSyntax.rhs (Thm.concl congruence)
                   val (theorem, changed_here) =
                     if boolSyntax.is_disj rebuilt then
                       let val (left, right) = boolSyntax.dest_disj rebuilt
                       in
                         if Term.aconv left right then
                           (Thm.TRANS congruence
                              (Conv.REWR_CONV disj_idempotent rebuilt), true)
                         else (congruence, false)
                       end
                     else if boolSyntax.is_conj rebuilt then
                       let val (left, right) = boolSyntax.dest_conj rebuilt
                       in
                         if Term.aconv left right then
                           (Thm.TRANS congruence
                              (Conv.REWR_CONV conj_idempotent rebuilt), true)
                         else (congruence, false)
                       end
                     else (congruence, false)
                   val result =
                     (theorem, child_changed orelse changed_here)
                   val _ = nodes :=
                     Redblackmap.insert (!nodes, term, result)
                 in
                   result
                 end
        in
          case Redblackmap.peek (!nodes, term) of
            SOME result => result
          | NONE => compute ()
        end
    in
      exact_left skeleton (Lib.fst (visit skeleton))
    end

  (* Turn the shared abstract skeleton into an explicitly linear
     definitional implication.  HolSat sees each connective node once.  Its
     checked theorem is instantiated back with the original DAG nodes, whose
     defining equations are then discharged by reflexivity. *)
  fun linear_sat_target actual_nodes residual_substitution skeleton =
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
      fun actual term = Redblackmap.find (actual_nodes, term)
        handle Redblackmap.NotFound =>
          raise ERR "linear_sat_target"
            "abstract node has no actual-node correspondence"
      val node_substitution = List.map
        (fn (_, variable, term) => variable |-> actual term) entries
      val node_domains = HOLset.addList (HOLset.empty Term.compare,
        List.map #redex node_substitution)
      val residual_domains = HOLset.addList (HOLset.empty Term.compare,
        List.map #redex residual_substitution)
      val _ =
        if List.all (Term.is_var o #redex)
             (node_substitution @ residual_substitution) andalso
           HOLset.numItems node_domains = List.length node_substitution andalso
           HOLset.numItems residual_domains =
             List.length residual_substitution andalso
           HOLset.isEmpty
             (HOLset.intersection (node_domains, residual_domains)) then ()
        else raise ERR "linear_sat_target"
          "generated substitution domains overlap or are not unique variables"
      (* Apply atom and Tseitin substitutions simultaneously.  Term.subst
         returns a matched residue without visiting it, so actual DAGs are
         inserted once rather than copied through a second INST.  HOL free
         variables and bound de Bruijn nodes are distinct constructors, so
         inserting a free-variable residue below an abstraction is
         capture-safe.  The disjoint-domain check above makes this schedule
         independent of substitution-list order. *)
      val substitution = node_substitution @ residual_substitution
      val definition_theorem =
        case entries of
          [] => boolTheory.TRUTH
        | _ => Drule.LIST_CONJ
            (List.map (fn (_, _, term) => Thm.REFL (actual term)) entries)
    in
      {target = target,
       substitution = substitution,
       definition_theorem = definition_theorem}
    end

  fun checked_sat_skeleton_prove
      (actual_nodes, residual_substitution, expected, skeleton) =
    let
      val {target, substitution, definition_theorem} =
        phase "skeleton/cnf-construction"
          (linear_sat_target actual_nodes residual_substitution) skeleton
      val _ = observe_sat_target target
      (* HolSatLib currently exposes search and certificate reconstruction as
         one checked operation, so E0 records that indivisible boundary. *)
      val target_theorem =
        case !sat_completion_observer of
          NONE => phase "skeleton/sat-search+checking"
            checked_sat_prove target
        | SOME observer =>
            let
              val started = Time.now ()
              val theorem = phase "skeleton/sat-search+checking"
                checked_sat_prove target
              val elapsed = Time.- (Time.now (), started)
              val _ = observer (target, elapsed)
            in
              theorem
            end
      val instantiated = phase "skeleton/combined-instantiation"
        (fn substitution => Thm.INST substitution target_theorem)
        substitution
      val theorem = phase "skeleton/cnf-definitions"
        (fn definition_theorem =>
          Thm.MP instantiated definition_theorem) definition_theorem
      val _ = phase "skeleton/cnf-final-check"
        (fn () =>
          if Term.aconv (Thm.concl theorem) expected then ()
          else raise ERR "checked_sat_skeleton_prove"
            "checked definitions did not return the actual skeleton") ()
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
      val actual_nodes = ref (Redblackmap.mkDict Term.compare)
      fun atom term =
        case Redblackmap.peek (!atoms, term) of
          SOME variable => variable
        | NONE =>
            let
              val variable = Term.genvar Type.bool
              val _ = atoms := Redblackmap.insert (!atoms, term, variable)
              val _ = actual_nodes :=
                Redblackmap.insert (!actual_nodes, variable, term)
            in
              variable
            end
      fun visit term =
        case skeleton_children term of
          NONE => atom term
        | SOME [] =>
            (actual_nodes := Redblackmap.insert (!actual_nodes, term, term);
             term)
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
                   val _ = actual_nodes :=
                     Redblackmap.insert (!actual_nodes, result, term)
                 in
                   result
                 end)
      val abstracted = visit skeleton
      val substitution = Redblackmap.foldl
        (fn (actual, variable, result) =>
          (variable |-> actual) :: result) [] (!atoms)
    in
      (abstracted, !actual_nodes, substitution,
       Redblackmap.numItems (!atoms))
    end

  exception PROCEDURE_UNABLE

  fun prove_with_owners
      (Context {procedures, atom_cache}) owners
      (target_measure : {tree_nodes : int, dag_nodes : int}) target =
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
      val nodes = ref (Redblackmap.mkDict Term.compare)
      val skeleton_nodes = ref (HOLset.empty Term.compare)
      val distinct_atoms = ref (HOLset.empty Term.compare)
      val calls = ref (Redblackmap.mkDict String.compare)
      val working_cache = ref (!atom_cache)
      val node_hits = ref 0
      val node_pointer_hits = ref 0
      val node_reanchor_attempts = ref 0
      val node_reanchor_successes = ref 0
      val node_reanchor_fallbacks = ref 0
      val node_reanchor_time = ref Time.zeroTime
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
        case Redblackmap.peek (owners, atom) of
          NONE => (Thm.REFL atom, false)
        | SOME name =>
            let
              val {expand, ...} = procedure_named procedures name
              val _ = owned_atoms := !owned_atoms + 1
              val _ = atom_requests := !atom_requests + 1
              val _ = distinct_atoms := HOLset.add (!distinct_atoms, atom)
              fun prove () =
                let
                  val timer = Timer.startRealTimer ()
                  val _ = add_call name
                  val theorem =
                    case Profile.profile_with_exn_name
                        ("th_lemma[general](atom:" ^ name ^ ")")
                        expand atom of
                      Expanded theorem =>
                        exact_left atom
                          (validate_theorem name atom theorem)
                    | Unable => raise PROCEDURE_UNABLE
                  val elapsed = Timer.checkRealTimer timer
                  val _ = atom_time := Time.+ (!atom_time, elapsed)
                  val _ = working_cache :=
                    Redblackmap.insert (!working_cache, atom, theorem)
                  val _ = atom_proofs := !atom_proofs + 1
                in
                  (theorem, true)
                end
            in
              case Redblackmap.peek (!working_cache, atom) of
                SOME theorem =>
                  (let
                     val theorem = reanchor_cached_theorem atom theorem
                   in
                     atom_hits := !atom_hits + 1;
                     (theorem, true)
                   end handle REANCHOR_LIMIT => prove ())
              | NONE => prove ()
            end
      fun visit term =
        let
          val _ = skeleton_nodes := HOLset.add (!skeleton_nodes, term)
          fun compute children =
            let
              val child_results = List.map visit children
              val changed = List.exists Lib.snd child_results
              val theorem =
                if changed then
                  anchor_left term
                    (connective_congruence term
                      (List.map Lib.fst child_results))
                else Thm.REFL term
              val result = (theorem, changed)
              val _ = nodes :=
                Redblackmap.insert (!nodes, term, (term, result))
            in
              result
            end
        in
          case skeleton_children term of
            NONE => expand term
          | SOME children =>
              (case Redblackmap.peek (!nodes, term) of
                 SOME (saved, (theorem, changed)) =>
                   (node_hits := !node_hits + 1;
                    if Portable.pointer_eq (term, saved) then
                      (node_pointer_hits := !node_pointer_hits + 1;
                       observe_node_cache NodeCachePointerHit;
                       (theorem, changed))
                    else
                      let
                        val _ = node_reanchor_attempts :=
                          !node_reanchor_attempts + 1
                        val _ = observe_node_cache
                          NodeCacheStructuralReanchorAttempt
                        val timer =
                          if SmtResource.e0_enabled () then
                            SOME (Timer.startRealTimer ())
                          else NONE
                        fun finish () =
                          case timer of
                            NONE => ()
                          | SOME timer =>
                              let
                                val elapsed = Timer.checkRealTimer timer
                                val _ = node_reanchor_time := Time.+
                                  (!node_reanchor_time, elapsed)
                              in
                                observe_node_cache
                                  (NodeCacheReanchorTime elapsed)
                              end
                        fun reanchor () =
                          let val result = (exact_left term theorem, changed)
                          in
                            node_reanchor_successes :=
                              !node_reanchor_successes + 1;
                            observe_node_cache
                              NodeCacheStructuralReanchorSuccess;
                            result
                          end
                      in
                        (Portable.finally finish reanchor ()
                         handle REANCHOR_LIMIT =>
                           (node_reanchor_fallbacks :=
                              !node_reanchor_fallbacks + 1;
                            observe_node_cache
                              NodeCacheStructuralReanchorFallback;
                            compute children))
                      end)
               | NONE => compute children)
        end
      val normalization = Lib.fst
        (phase "skeleton/conversion" visit target)
      val normalized = boolSyntax.rhs (Thm.concl normalization)
      val _ =
        if !owned_atoms > 0 andalso Term.aconv normalized target then
          raise ERR "prove" "atom expansion made no progress"
        else ()
      val idempotence = phase "skeleton/cnf-normalization"
        normalize_idempotent_skeleton normalized
      val normalized = boolSyntax.rhs (Thm.concl idempotence)
      val (abstracted, actual_nodes, residual_substitution, residual_count) =
        phase "skeleton/abstraction" abstract_skeleton normalized
      val sat_timer = Timer.startRealTimer ()
      val {theorem = actual_theorem, sat_target} =
        phase "skeleton/cnf+sat" checked_sat_skeleton_prove
          (actual_nodes, residual_substitution, normalized, abstracted)
      val _ =
        if List.null (Thm.hyp actual_theorem) then ()
        else raise ERR "prove" "checked SAT theorem has hypotheses"
      val _ =
        if Term.aconv (Thm.concl actual_theorem) normalized then ()
        else raise ERR "prove"
          "checked SAT theorem does not match the actual skeleton"
      val _ = Library.check_oracle_tags
        "SmtSkeletonProve" "checked-sat" actual_theorem
      val sat_time = Timer.checkRealTimer sat_timer
      val idempotence_sym = phase "skeleton/idempotence-sym"
        Thm.SYM idempotence
      val converted_theorem = phase "skeleton/idempotence-eq-mp"
        (fn equality => Thm.EQ_MP equality actual_theorem)
        idempotence_sym
      val normalization_sym = phase "skeleton/normalization-sym"
        Thm.SYM normalization
      val theorem = phase "skeleton/normalization-eq-mp"
        (fn equality => Thm.EQ_MP equality converted_theorem)
        normalization_sym
      val _ = phase "skeleton/final-hypothesis-check"
        (fn () =>
          if List.null (Thm.hyp theorem) then ()
          else raise ERR "prove" "result theorem has hypotheses") ()
      val _ = phase "skeleton/final-conclusion-check"
        (fn () =>
          if Term.aconv (Thm.concl theorem) target then ()
          else raise ERR "prove" "result theorem does not match the target") ()
      val _ = phase "skeleton/final-oracle-check"
        (fn () => Library.check_oracle_tags
          "SmtSkeletonProve" "result" theorem) ()
      val total_time = Timer.checkRealTimer total_timer
      val normalized_measure = phase "skeleton/metrics-normalized"
        term_measure normalized
      val sat_measure = phase "skeleton/metrics-sat" term_measure sat_target
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
         node_cache_pointer_hits = !node_pointer_hits,
         node_cache_structural_reanchor_attempts = !node_reanchor_attempts,
         node_cache_structural_reanchor_successes = !node_reanchor_successes,
         node_cache_structural_reanchor_fallbacks = !node_reanchor_fallbacks,
         node_cache_reanchor_seconds = !node_reanchor_time,
         residual_atoms = residual_count,
         atom_seconds = !atom_time,
         sat_seconds = sat_time,
         total_seconds = total_time,
         procedure_calls = procedure_calls}
      val _ = atom_cache := !working_cache
    in
      {theorem = theorem, metrics = metrics}
    end

  datatype attempt =
      Proved of {theorem : thm, metrics : metrics}
    | Declined

  fun attempt_with_owners context owners target_measure target =
    Proved (prove_with_owners context owners target_measure target)
    handle PROCEDURE_UNABLE => Declined
         | HolSatLib.SAT_cex _ => Declined

end
