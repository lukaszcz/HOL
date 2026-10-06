structure SmtSkeletonProve =
struct

  open HolKernel

  val ERR = Feedback.mk_HOL_ERR "SmtSkeletonProve"

  datatype expansion = Expanded of thm | Unable

  type atom_procedure =
    {name : string, expand : term -> expansion}

  datatype context = Context of
    {procedures : atom_procedure list,
     fallback : atom_procedure option,
     atom_cache : (term, thm) Redblackmap.dict ref}

  type metrics =
    {target_tree_nodes : int,
     target_dag_nodes : int,
     skeleton_dag_nodes : int,
     normalized_tree_nodes : int,
     normalized_dag_nodes : int,
     sat_tree_nodes : int,
     sat_dag_nodes : int,
     graph_nodes : int,
     graph_observations : int,
     graph_edges : int,
     graph_type_nodes : int,
     graph_type_observations : int,
     graph_type_edges : int,
     graph_leaf_transport_nodes : int,
     graph_leaf_transport_seconds : Time.time,
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
    {procedures = procedures, fallback = NONE,
     atom_cache = ref (Redblackmap.mkDict Term.compare)}

  fun new_dynamic_context procedures fallback = Context
    {procedures = procedures, fallback = SOME fallback,
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

  datatype admission_type_key =
      AdmissionTypeVariable of string
    | AdmissionTypeOperator of KernelSig.kernelid * int list

  fun admission_type_key_compare
      (AdmissionTypeVariable left, AdmissionTypeVariable right) =
        String.compare (left, right)
    | admission_type_key_compare
        (AdmissionTypeVariable _, AdmissionTypeOperator _) = LESS
    | admission_type_key_compare
        (AdmissionTypeOperator _, AdmissionTypeVariable _) = GREATER
    | admission_type_key_compare
        (AdmissionTypeOperator (left_id, left_arguments),
         AdmissionTypeOperator (right_id, right_arguments)) =
        (case KernelSig.id_compare (left_id, right_id) of
           EQUAL => list_compare Int.compare
             (left_arguments, right_arguments)
         | order => order)

  datatype admission_type_node = AdmissionTypeNode of
    {id : int, tree_nodes : int}

  fun new_type_admission_context () =
    let
      val maximum = SmtResource.max_bv_replay_term_nodes
      val ids = ref (Redblackmap.mkDict admission_type_key_compare)
      val physical = ref ([] : (hol_type * admission_type_node) list)
      val next_id = ref 0
      val nodes = ref 0
      val edges = ref 0
      fun intern ty =
        case SmtResource.recent_pointer_lookup physical ty of
          SOME node => node
        | NONE =>
            let
              val arguments = if Type.is_vartype ty then []
                else Lib.snd (Type.dest_type ty)
              val children = List.map intern arguments
              fun node_id (AdmissionTypeNode {id, ...}) = id
              fun node_size (AdmissionTypeNode {tree_nodes, ...}) = tree_nodes
              val key = if Type.is_vartype ty then
                  AdmissionTypeVariable (Type.dest_vartype ty)
                else AdmissionTypeOperator
                  (#Tyop (Type.dest_thy_typeid ty), List.map node_id children)
              val _ = edges := saturated_add (!edges) (List.length children)
              val (id, tree_nodes) =
                case Redblackmap.peek (!ids, key) of
                  SOME (AdmissionTypeNode fields) =>
                    (#id fields, #tree_nodes fields)
                | NONE =>
                    let
                      val size = List.foldl
                        (fn (child, count) =>
                          saturated_add count (node_size child)) 1 children
                      val _ = if size <= maximum then () else
                        SmtResource.check_term_size_for "BitVector"
                          "skeleton-type-work" size
                      val id = !next_id
                    in
                      next_id := id + 1; nodes := !nodes + 1; (id, size)
                    end
              val node = AdmissionTypeNode {id = id, tree_nodes = tree_nodes}
              val _ = if Option.isSome (Redblackmap.peek (!ids, key)) then ()
                else ids := Redblackmap.insert (!ids, key, node)
              val _ = physical := (ty, node) :: !physical
            in node end
      fun type_id ty = let val AdmissionTypeNode {id, ...} = intern ty in id end
      fun admit_abstraction operation term =
        let
          val _ = case Term.term_size_bounded maximum term of
              SOME _ => ()
            | NONE => SmtResource.check_term_size_for "BitVector" operation
                (maximum + 1)
          fun atom_rank atom = if Term.is_var atom then 0 else 1
          fun compare_atoms (left, right) =
            case Int.compare (atom_rank left, atom_rank right) of
              EQUAL => if Term.is_var left then
                  pair_compare (String.compare, Int.compare)
                    ((Lib.fst (Term.dest_var left),
                      type_id (Term.type_of left)),
                     (Lib.fst (Term.dest_var right),
                      type_id (Term.type_of right)))
                else pair_compare (KernelSig.id_compare, Int.compare)
                  ((#Name (Term.dest_thy_constid left),
                    type_id (Term.type_of left)),
                   (#Name (Term.dest_thy_constid right),
                    type_id (Term.type_of right)))
            | order => order
          val atoms = HOLset.listItems
            (Term.all_atomsl [term] (HOLset.empty compare_atoms))
          val _ = List.app (ignore o intern o Term.type_of) atoms
        in () end
    in
      {intern = intern, admit_abstraction = admit_abstraction,
       nodes = nodes, edges = edges, physical = physical}
    end

  (* Build left = right one physical node at a time.  Both endpoint anchors
     compare only a newly built outer node whose children already have the
     requested endpoint pointers.  Structural cache collisions use separate
     pointer buckets, and the fixed skeleton DAG limit bounds reconstruction. *)
  fun bounded_nodewise_equality maximum left right =
    let
      val type_admission = new_type_admission_context ()
      fun inspect term =
        if Term.is_abs term then
          #admit_abstraction type_admission
            "skeleton-cache-abstraction" term
        else ()
      val _ =
        if SmtResource.dag_nodes_up_to_with_inspector inspect maximum left <=
           maximum then ()
        else raise REANCHOR_LIMIT
      val compared = ref 0
      val bucket_count = 4093
      val cache = Array.array
        (bucket_count, [] : (term * term * thm) list)
      fun hash_string string =
        CharVector.foldl (fn (character, hash) =>
          (hash * 33 + Char.ord character) mod bucket_count) 17 string
      fun shallow_hash 0 term =
            if Term.is_var term then hash_string (#1 (Term.dest_var term))
            else if Term.is_const term then
              hash_string (#Name (Term.dest_thy_const term))
            else if Term.is_abs term then 5 else 7
        | shallow_hash depth term =
            if Term.is_comb term then
              (41 * shallow_hash (depth - 1) (Term.rator term) +
               67 * shallow_hash (depth - 1) (Term.rand term) + 11) mod
                bucket_count
            else if Term.is_abs term then
              (73 * shallow_hash (depth - 1) (Term.body term) + 13) mod
                bucket_count
            else shallow_hash 0 term
      fun pair_bucket (left, right) =
        (97 * shallow_hash 3 left + shallow_hash 3 right) mod bucket_count
      fun visit (left, right) =
        if Portable.pointer_eq (left, right) then Thm.REFL left
        else
          let val bucket = pair_bucket (left, right) in
          case List.find
              (fn (saved_left, saved_right, _) =>
                Portable.pointer_eq (left, saved_left) andalso
                Portable.pointer_eq (right, saved_right))
              (Array.sub (cache, bucket)) of
            SOME (_, _, theorem) => theorem
          | NONE => compute (left, right)
          end
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
                val _ = #admit_abstraction type_admission
                  "skeleton-cache-abstraction" left
                val _ = #admit_abstraction type_admission
                  "skeleton-cache-abstraction" right
              in Thm.TRANS (Thm.REFL left) (Thm.REFL right) end
            else
              Thm.TRANS (Thm.REFL left) (Thm.REFL right)
          val bucket = pair_bucket (left, right)
          val _ = Array.update
            (cache, bucket,
             (left, right, theorem) :: Array.sub (cache, bucket))
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

  fun procedure_names (Context {procedures, fallback, ...}) =
    List.map #name procedures @
      (case fallback of NONE => [] | SOME procedure => [#name procedure])

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

  val gate_reduction_conv = Conv.FIRST_CONV
    (List.map Conv.REWR_CONV
      (boolTheory.REFL_CLAUSE :: boolTheory.COND_ID ::
       List.concat (List.map (Drule.CONJUNCTS o Drule.SPEC_ALL)
         [boolTheory.AND_CLAUSES, boolTheory.OR_CLAUSES,
          boolTheory.NOT_CLAUSES, boolTheory.IMP_CLAUSES,
          boolTheory.EQ_CLAUSES, boolTheory.COND_CLAUSES])))

  datatype raw_key =
      RawVariable of string * int
    | RawConstant of KernelSig.kernelid * int
    | RawApplication of int * int

  fun raw_key_rank key =
    case key of RawVariable _ => 0 | RawConstant _ => 1 | RawApplication _ => 2

  fun raw_key_compare (left, right) =
    case Int.compare (raw_key_rank left, raw_key_rank right) of
      EQUAL =>
        (case (left, right) of
           (RawVariable (left_name, left_type),
            RawVariable (right_name, right_type)) =>
             (case String.compare (left_name, right_name) of
                EQUAL => Int.compare (left_type, right_type)
              | order => order)
         | (RawConstant (left_id, left_type),
            RawConstant (right_id, right_type)) =>
             (case KernelSig.id_compare (left_id, right_id) of
                EQUAL => Int.compare (left_type, right_type)
              | order => order)
         | (RawApplication (left_operator, left_operand),
            RawApplication (right_operator, right_operand)) =>
             pair_compare (Int.compare, Int.compare)
               ((left_operator, left_operand),
                (right_operator, right_operand))
         | _ => EQUAL)
    | order => order

  datatype graph_kind =
      GraphTrue
    | GraphFalse
    | GraphAtom of int
    | GraphNegation of int
    | GraphConjunction of int * int
    | GraphDisjunction of int * int
    | GraphImplication of int * int
    | GraphEquality of int * int
    | GraphConditional of int * int * int

  fun graph_kind_rank kind =
    case kind of
      GraphTrue => 0 | GraphFalse => 1 | GraphAtom _ => 2 |
      GraphNegation _ => 3 | GraphConjunction _ => 4 |
      GraphDisjunction _ => 5 | GraphImplication _ => 6 |
      GraphEquality _ => 7 | GraphConditional _ => 8

  fun graph_kind_compare (left, right) =
    case Int.compare (graph_kind_rank left, graph_kind_rank right) of
      EQUAL =>
        (case (left, right) of
           (GraphAtom left_id, GraphAtom right_id) =>
             Int.compare (left_id, right_id)
         | (GraphNegation left_id, GraphNegation right_id) =>
             Int.compare (left_id, right_id)
         | (GraphConjunction left_ids, GraphConjunction right_ids) =>
             pair_compare (Int.compare, Int.compare) (left_ids, right_ids)
         | (GraphDisjunction left_ids, GraphDisjunction right_ids) =>
             pair_compare (Int.compare, Int.compare) (left_ids, right_ids)
         | (GraphImplication left_ids, GraphImplication right_ids) =>
             pair_compare (Int.compare, Int.compare) (left_ids, right_ids)
         | (GraphEquality left_ids, GraphEquality right_ids) =>
             pair_compare (Int.compare, Int.compare) (left_ids, right_ids)
         | (GraphConditional (left_test, left_yes, left_no),
            GraphConditional (right_test, right_yes, right_no)) =>
             list_compare Int.compare
               ([left_test, left_yes, left_no],
                [right_test, right_yes, right_no])
         | _ => EQUAL)
    | order => order

  datatype raw_node = RawNode of
    {id : int, representative : term, equality : thm, tree_nodes : int,
     ty : hol_type}

  datatype graph_node = GraphNode of
    {id : int, kind : graph_kind, representative : term,
     equality : thm, tree_nodes : int}

  (* The graph uses kernel declaration identities and canonical child IDs as
     lookup keys.  Terms remain the proof evidence: every reuse is justified
     by a checked equality with the current occurrence as its exact left
     endpoint.  Whole abstractions form the public-kernel boundary and are
     compared only after bounded raw and type-work admission. *)
  fun build_cnf_graph_mode reduce_gates skeleton =
    let
      val maximum = SmtResource.max_bv_replay_term_nodes
      val type_admission = new_type_admission_context ()
      fun intern_type ty = #intern type_admission ty
      fun type_id (AdmissionTypeNode {id, ...}) = id
      fun admit_type ty = ignore (intern_type ty)
      val admit_abstraction = #admit_abstraction type_admission
      val type_nodes = #nodes type_admission
      val type_edges = #edges type_admission
      val type_physical = #physical type_admission
      val raw_ids = ref (Redblackmap.mkDict raw_key_compare)
      val physical_bucket_count = 4093
      val raw_physical = Array.array
        (physical_bucket_count, [] : (term * raw_node) list)
      val physical_bucket = SmtResource.pointer_bucket physical_bucket_count
      fun physical_find buckets term =
        List.find
          (fn (saved, _) => Portable.pointer_eq (term, saved))
          (Array.sub (buckets, physical_bucket term))
      fun physical_insert buckets term node =
        let val bucket = physical_bucket term in
          Array.update (buckets, bucket,
            (term, node) :: Array.sub (buckets, bucket))
        end
      val abstractions = ref ([] : raw_node list)
      val next_raw_id = ref 0
      val raw_nodes = ref 0
      val raw_edges = ref 0
      val transport_nodes = ref 0
      val transport_time = ref Time.zeroTime
      fun fresh_raw representative equality tree_nodes ty =
        let
          val result = RawNode
            {id = !next_raw_id, representative = representative,
             equality = equality, tree_nodes = tree_nodes, ty = ty}
        in
          next_raw_id := !next_raw_id + 1;
          raw_nodes := !raw_nodes + 1;
          result
        end
      fun raw_id (RawNode {id, ...}) = id
      fun raw_representative (RawNode {representative, ...}) = representative
      fun raw_equality (RawNode {equality, ...}) = equality
      fun raw_tree_nodes (RawNode {tree_nodes, ...}) = tree_nodes
      fun raw_type (RawNode {ty, ...}) = ty
      fun checked_leaf_equality operation occurrence representative =
        let
          val timer = Timer.startRealTimer ()
          val _ = admit_type (Term.type_of occurrence)
          val _ = admit_type (Term.type_of representative)
          val theorem =
            Thm.TRANS (Thm.REFL occurrence) (Thm.REFL representative)
          val _ = transport_nodes := !transport_nodes + 1
          val _ = transport_time := Time.+
            (!transport_time, Timer.checkRealTimer timer)
        in
          theorem
        end
      fun canonical_raw key occurrence representative initial_equality
          tree_nodes ty make_equality =
        case Redblackmap.peek (!raw_ids, key) of
          SOME saved =>
            let
              val representative = raw_representative saved
              val equality = make_equality representative
            in
              RawNode {id = raw_id saved, representative = representative,
                equality = equality, tree_nodes = raw_tree_nodes saved,
                ty = raw_type saved}
            end
        | NONE =>
            let
              val saved = fresh_raw representative initial_equality
                tree_nodes ty
              val _ = raw_ids := Redblackmap.insert (!raw_ids, key, saved)
            in
              saved
            end
      fun intern_abstraction occurrence =
        let
          val size =
            case Term.term_size_bounded maximum occurrence of
              SOME size => size
            | NONE =>
                (SmtResource.check_term_size_for "BitVector"
                   "skeleton-graph-abstraction" (maximum + 1); 0)
          val ty = Term.type_of occurrence
          val _ = admit_abstraction "skeleton-graph-abstraction" occurrence
          fun find [] = NONE
            | find (saved :: rest) =
                let val representative = raw_representative saved
                in
                  admit_abstraction
                    "skeleton-graph-abstraction" representative;
                  if Term.aconv occurrence representative then SOME saved
                  else find rest
                end
        in
          case find (!abstractions) of
            SOME saved =>
              RawNode
                {id = raw_id saved,
                 representative = raw_representative saved,
                 equality = checked_leaf_equality
                   "skeleton-graph-abstraction" occurrence
                   (raw_representative saved),
                 tree_nodes = raw_tree_nodes saved, ty = raw_type saved}
          | NONE =>
              let
                val (_, body) = Term.dest_abs occurrence
                val _ = ignore (intern_raw body)
                val _ = raw_edges := saturated_add (!raw_edges) 1
                val saved = fresh_raw occurrence
                  (Thm.REFL occurrence) size ty
              in abstractions := saved :: !abstractions; saved end
        end
      and intern_raw occurrence =
        case physical_find raw_physical occurrence of
          SOME (_, saved) => saved
        | NONE =>
            let
              val saved =
                if Term.is_var occurrence then
                  let
                    val (name, ty) = Term.dest_var occurrence
                    val type_id = type_id (intern_type ty)
                  in
                    canonical_raw (RawVariable (name, type_id)) occurrence
                      occurrence (Thm.REFL occurrence) 1 ty
                      (checked_leaf_equality "skeleton-graph-variable"
                         occurrence)
                  end
                else if Term.is_const occurrence then
                  let
                    val ty = Term.type_of occurrence
                    val type_id = type_id (intern_type ty)
                    val key = RawConstant
                      (#Name (Term.dest_thy_constid occurrence), type_id)
                  in
                    canonical_raw key occurrence occurrence
                      (Thm.REFL occurrence) 1 ty
                      (checked_leaf_equality "skeleton-graph-constant"
                         occurrence)
                  end
                else if Term.is_comb occurrence then
                  let
                    val (operator, operand) = Term.dest_comb occurrence
                    val operator_node = intern_raw operator
                    val operand_node = intern_raw operand
                    val key = RawApplication
                      (raw_id operator_node, raw_id operand_node)
                    val tree_nodes = saturated_add 1
                      (saturated_add (raw_tree_nodes operator_node)
                        (raw_tree_nodes operand_node))
                    fun equality representative =
                      let
                        val _ = admit_type (raw_type operator_node)
                        val _ = admit_type (raw_type operand_node)
                        val congruence = anchor_left occurrence
                          (Thm.MK_COMB
                            (raw_equality operator_node,
                             raw_equality operand_node))
                      in
                        anchor_right representative congruence
                      end
                    val children_unchanged =
                      Portable.pointer_eq
                        (operator, raw_representative operator_node) andalso
                      Portable.pointer_eq
                        (operand, raw_representative operand_node)
                    val candidate_equality =
                      if children_unchanged then Thm.REFL occurrence
                      else
                        let
                          val _ = admit_type (raw_type operator_node)
                          val _ = admit_type (raw_type operand_node)
                        in
                          anchor_left occurrence
                            (Thm.MK_COMB
                              (raw_equality operator_node,
                               raw_equality operand_node))
                        end
                    val candidate = boolSyntax.rhs
                      (Thm.concl candidate_equality)
                    val ty = Lib.snd (Type.dom_rng (raw_type operator_node))
                    val _ = raw_edges := saturated_add (!raw_edges) 2
                  in
                    canonical_raw key occurrence candidate candidate_equality
                      tree_nodes ty equality
                  end
                else if Term.is_abs occurrence then
                  intern_abstraction occurrence
                else raise ERR "build_cnf_graph"
                  "unknown raw term constructor"
              val _ = physical_insert raw_physical occurrence saved
            in
              saved
            end
      val graph_ids = ref (Redblackmap.mkDict graph_kind_compare)
      val graph_physical = Array.array
        (physical_bucket_count, [] : (term * graph_node) list)
      val graph_observations = ref 0
      val graph_entries = ref ([] : graph_node list)
      val next_graph_id = ref 0
      val graph_edges = ref 0
      val residual_atoms = ref 0
      fun graph_id (GraphNode {id, ...}) = id
      fun graph_representative (GraphNode {representative, ...}) = representative
      fun graph_equality (GraphNode {equality, ...}) = equality
      fun graph_tree_nodes (GraphNode {tree_nodes, ...}) = tree_nodes
      fun add_graph kind representative equality tree_nodes =
        case Redblackmap.peek (!graph_ids, kind) of
          SOME saved =>
            GraphNode
              {id = graph_id saved, kind = kind,
               representative = graph_representative saved,
               equality = anchor_right (graph_representative saved) equality,
               tree_nodes = graph_tree_nodes saved}
        | NONE =>
            let
              val saved = GraphNode
                {id = !next_graph_id, kind = kind,
                 representative = representative, equality = equality,
                 tree_nodes = tree_nodes}
            in
              next_graph_id := !next_graph_id + 1;
              graph_ids := Redblackmap.insert (!graph_ids, kind, saved);
              graph_entries := saved :: !graph_entries;
              saved
            end
      fun connective_kind term ids =
        if boolSyntax.is_neg term then GraphNegation (hd ids)
        else if boolSyntax.is_conj term then
          GraphConjunction (List.nth (ids, 0), List.nth (ids, 1))
        else if boolSyntax.is_disj term then
          GraphDisjunction (List.nth (ids, 0), List.nth (ids, 1))
        else if boolSyntax.is_imp term then
          GraphImplication (List.nth (ids, 0), List.nth (ids, 1))
        else if boolSyntax.is_cond term then
          GraphConditional
            (List.nth (ids, 0), List.nth (ids, 1), List.nth (ids, 2))
        else GraphEquality (List.nth (ids, 0), List.nth (ids, 1))
      fun reduce_gate rebuilt children =
        let
          val variables = ref (Redblackmap.mkDict Int.compare)
          val substitution = ref []
          fun abstract (node as GraphNode {id, kind, ...}) =
            case kind of
              GraphTrue => boolSyntax.T
            | GraphFalse => boolSyntax.F
            | _ =>
                (case Redblackmap.peek (!variables, id) of
                   SOME variable => variable
                 | NONE =>
                     let val variable = Term.genvar Type.bool in
                       variables := Redblackmap.insert
                         (!variables, id, variable);
                       substitution := (variable |->
                         graph_representative node) :: !substitution;
                       variable
                     end)
          val head = #1 (boolSyntax.strip_comb rebuilt)
          val schematic = Term.list_mk_comb
            (head, List.map abstract children)
          val theorem = Conv.QCONV
            (Conv.TRY_CONV gate_reduction_conv) schematic
        in anchor_left rebuilt (Thm.INST (!substitution) theorem) end
      fun visit occurrence =
        case physical_find graph_physical occurrence of
          SOME (_, saved) => saved
        | NONE =>
            let
              val saved =
                if Term.aconv occurrence boolSyntax.T then
                  add_graph GraphTrue occurrence (Thm.REFL occurrence) 1
                else if Term.aconv occurrence boolSyntax.F then
                  add_graph GraphFalse occurrence (Thm.REFL occurrence) 1
                else
                  case skeleton_children occurrence of
                    NONE =>
                      let
                        val raw = intern_raw occurrence
                        val _ = residual_atoms := !residual_atoms + 1
                      in
                        add_graph (GraphAtom (raw_id raw))
                          (raw_representative raw) (raw_equality raw)
                          (raw_tree_nodes raw)
                      end
                  | SOME [] => raise ERR "build_cnf_graph"
                      "unexpected propositional leaf"
                  | SOME children =>
                      let
                        val child_nodes = List.map visit children
                        val child_ids = List.map graph_id child_nodes
                        val congruence = anchor_left occurrence
                          (connective_congruence occurrence
                            (List.map graph_equality child_nodes))
                        val rebuilt = boolSyntax.rhs (Thm.concl congruence)
                        val tree_nodes = saturated_add 1
                          (List.foldl
                            (fn (node, count) => saturated_add count
                              (graph_tree_nodes node)) 0 child_nodes)
                        val _ = graph_edges := saturated_add (!graph_edges)
                          (List.length child_nodes)
                      in
                        if (boolSyntax.is_conj rebuilt orelse
                            boolSyntax.is_disj rebuilt) andalso
                           graph_id (List.nth (child_nodes, 0)) =
                             graph_id (List.nth (child_nodes, 1)) then
                          let
                            val law = if boolSyntax.is_conj rebuilt then
                              conj_idempotent else disj_idempotent
                            val child = hd child_nodes
                            val GraphNode {kind, ...} = child
                            val instantiated = Thm.INST
                              [idempotent_variable |->
                                 graph_representative child] law
                            val theorem = Thm.TRANS congruence instantiated
                          in
                            GraphNode
                              {id = graph_id child,
                               kind = kind,
                               representative = graph_representative child,
                               equality = theorem,
                               tree_nodes = graph_tree_nodes child}
                          end
                        else if reduce_gates then
                          let
                            val reduction = reduce_gate rebuilt child_nodes
                            val residue = boolSyntax.rhs (Thm.concl reduction)
                          in
                            if not (Term.aconv rebuilt residue) then
                              let
                                val node = visit residue
                                val GraphNode {id, kind, representative,
                                  tree_nodes, ...} = node
                              in
                                GraphNode {id = id, kind = kind,
                                  representative = representative,
                                  tree_nodes = tree_nodes,
                                  equality = Thm.TRANS congruence
                                    (Thm.TRANS reduction
                                      (graph_equality node))}
                              end
                            else
                              let
                                val commutative = boolSyntax.is_conj rebuilt
                                  orelse boolSyntax.is_disj rebuilt
                                  orelse boolSyntax.is_eq rebuilt
                                val reverse = commutative andalso
                                  List.nth (child_ids, 0) >
                                  List.nth (child_ids, 1)
                                val oriented = if not reverse then congruence
                                  else Thm.TRANS congruence
                                    (Conv.REWR_CONV
                                      (if boolSyntax.is_conj rebuilt then
                                         boolTheory.CONJ_SYM
                                       else if boolSyntax.is_disj rebuilt then
                                         boolTheory.DISJ_SYM
                                       else boolTheory.EQ_SYM_EQ) rebuilt)
                                val ids = if reverse then List.rev child_ids
                                  else child_ids
                                val right = boolSyntax.rhs
                                  (Thm.concl oriented)
                              in add_graph (connective_kind right ids)
                                right oriented tree_nodes end
                          end
                        else add_graph (connective_kind rebuilt child_ids)
                          rebuilt congruence tree_nodes
                      end
              val _ = physical_insert graph_physical occurrence saved
              val _ = graph_observations := !graph_observations + 1
            in
              saved
            end
      val root = visit skeleton
      val normalized = graph_representative root
      val normalized_raw = intern_raw normalized
      val normalized_tree_nodes = raw_tree_nodes normalized_raw
      val normalized_dag_nodes = !raw_nodes
    in
      {root = root, entries = List.rev (!graph_entries),
       graph_nodes = !next_graph_id,
       graph_observations = !graph_observations,
       graph_edges = !graph_edges,
       raw_nodes = !raw_nodes, raw_edges = !raw_edges,
       normalized_tree_nodes = normalized_tree_nodes,
       normalized_dag_nodes = normalized_dag_nodes,
       type_nodes = !type_nodes,
       type_observations = List.length (!type_physical),
       type_edges = !type_edges,
       transport_nodes = !transport_nodes,
       transport_seconds = !transport_time,
       residual_atoms = List.length
         (List.filter
           (fn GraphNode {kind = GraphAtom _, ...} => true | _ => false)
           (!graph_entries))}
    end

  val build_cnf_graph = build_cnf_graph_mode false

  type sat_context =
    {proofs : (term * thm * int) list ref, nodes : int ref}

  fun new_sat_context () : sat_context = {proofs = ref [], nodes = ref 0}

  fun cached_sat_proof (context : sat_context) target cost prove =
    let
      val maximum = SmtResource.max_skeleton_replay_dag_nodes
      fun validate theorem =
        (if List.null (Thm.hyp theorem) then ()
         else raise ERR "cached_sat_proof" "SAT certificate has hypotheses";
         Library.check_oracle_tags "SmtSkeletonProve"
           "schematic SAT certificate" theorem;
         Thm.EQ_MP (Thm.ALPHA (Thm.concl theorem) target) theorem)
      fun find [] _ = NONE
        | find ((entry as (saved, theorem, _)) :: rest) prior =
            if Term.aconv saved target then
              ( #proofs context := entry :: List.revAppend (prior, rest);
                SOME theorem)
            else find rest (entry :: prior)
      fun retain theorem =
        if cost > maximum then ()
        else
          let
            fun fit entries nodes =
              if nodes + cost <= maximum then (entries, nodes)
              else case entries of
                [] => ([], 0)
              | (_, _, old_cost) :: rest => fit rest (nodes - old_cost)
            val (oldest_first, nodes) = fit
              (List.rev (!(#proofs context))) (!(#nodes context))
          in
            #proofs context := (target, theorem, cost) ::
              List.rev oldest_first;
            #nodes context := nodes + cost
          end
      val theorem = case find (!(#proofs context)) [] of
          SOME theorem => phase "skeleton/schematic-certificate-hit"
            validate theorem
        | NONE => let val theorem = validate (prove ())
                  in retain theorem; theorem end
    in theorem end

  fun checked_graph_sat_prove_in context entries root =
    let
      fun node_id (GraphNode {id, ...}) = id
      fun node_kind (GraphNode {kind, ...}) = kind
      fun node_representative (GraphNode {representative, ...}) =
        representative
      (* Reduction and interning may leave dead gates in the construction
         inventory.  Only dependencies of the observed output belong to the
         SAT problem; their checked definitions suffice for reconstruction. *)
      val inventory = List.foldl
        (fn (node, dictionary) => Redblackmap.insert
          (dictionary, node_id node, node))
        (Redblackmap.mkDict Int.compare) entries
      val live = ref (HOLset.empty Int.compare)
      fun mark id =
        if HOLset.member (!live, id) then ()
        else
          let
            val node = Redblackmap.find (inventory, id)
            val _ = live := HOLset.add (!live, id)
            val children = case node_kind node of
                GraphNegation child => [child]
              | GraphConjunction (left, right) => [left, right]
              | GraphDisjunction (left, right) => [left, right]
              | GraphImplication (left, right) => [left, right]
              | GraphEquality (left, right) => [left, right]
              | GraphConditional (test, yes, no) => [test, yes, no]
              | _ => []
          in List.app mark children end
      val _ = mark (node_id root)
      val entries = List.filter
        (fn node => HOLset.member (!live, node_id node)) entries
      fun generated kind =
        case kind of GraphTrue => false | GraphFalse => false | _ => true
      val variables = List.foldl
        (fn (node, dictionary) =>
          if generated (node_kind node) then
            Redblackmap.insert
              (dictionary, node_id node, Term.mk_var
                ("skeleton_node_" ^ Int.toString (node_id node), Type.bool))
          else dictionary)
        (Redblackmap.mkDict Int.compare) entries
      val kinds = List.foldl
        (fn (node, dictionary) => Redblackmap.insert
          (dictionary, node_id node, node_kind node))
        (Redblackmap.mkDict Int.compare) entries
      fun symbolic id =
        case Redblackmap.peek (kinds, id) of
          NONE => raise ERR "checked_graph_sat_prove" "unknown graph node ID"
        | SOME kind =>
            (case kind of
               GraphTrue => boolSyntax.T
             | GraphFalse => boolSyntax.F
             | _ => Redblackmap.find (variables, id))
      fun body kind =
        case kind of
          GraphNegation child => boolSyntax.mk_neg (symbolic child)
        | GraphConjunction (left, right) =>
            boolSyntax.mk_conj (symbolic left, symbolic right)
        | GraphDisjunction (left, right) =>
            boolSyntax.mk_disj (symbolic left, symbolic right)
        | GraphImplication (left, right) =>
            boolSyntax.mk_imp (symbolic left, symbolic right)
        | GraphEquality (left, right) =>
            boolSyntax.mk_eq (symbolic left, symbolic right)
        | GraphConditional (test, yes, no) =>
            boolSyntax.mk_cond
              (symbolic test, symbolic yes, symbolic no)
        | _ => raise ERR "checked_graph_sat_prove"
            "non-connective graph node has no definition"
      fun is_connective kind =
        case kind of
          GraphNegation _ => true | GraphConjunction _ => true |
          GraphDisjunction _ => true | GraphImplication _ => true |
          GraphEquality _ => true | GraphConditional _ => true | _ => false
      val connective_nodes = List.filter
        (is_connective o node_kind) entries
      val equations = List.map
        (fn node => boolSyntax.mk_eq
          (symbolic (node_id node), body (node_kind node)))
        connective_nodes
      val cnf_equivalence = phase "skeleton/gate-cnf"
        (SmtCircuitSat.balanced_equivalences o
         List.map SmtCircuitSat.definition_cnf) equations
      val antecedent = boolSyntax.lhs (Thm.concl cnf_equivalence)
      val cnf = boolSyntax.rhs (Thm.concl cnf_equivalence)
      val target = boolSyntax.mk_imp
        (antecedent, symbolic (node_id root))
      val sat_target = boolSyntax.mk_imp (cnf, symbolic (node_id root))
      val sat_measure = phase "skeleton/sat-target-measure"
        term_measure sat_target
      val substitution = List.map
        (fn node => Redblackmap.find (variables, node_id node) |->
          node_representative node)
        (List.filter (generated o node_kind) entries)
      val domains = HOLset.addList (HOLset.empty Term.compare,
        List.map #redex substitution)
      val _ =
        if HOLset.numItems domains = List.length substitution andalso
           List.all (Term.is_var o #redex) substitution then ()
        else raise ERR "checked_graph_sat_prove"
          "generated graph substitution domains overlap"
      val definition_theorem = phase "skeleton/reflexive-definitions"
        (SmtCircuitSat.balanced_conjunction o
         List.map (Thm.REFL o node_representative)) connective_nodes
      val _ = observe_sat_target sat_target
      fun prove () = cached_sat_proof context sat_target
        (#dag_nodes sat_measure)
        (fn () => SmtCircuitSat.prove_cnf (cnf, symbolic (node_id root)))
      val cnf_theorem =
        case !sat_completion_observer of
          NONE => phase "skeleton/sat-search+checking"
            prove ()
        | SOME observer =>
            let
              val started = Time.now ()
              val theorem = phase "skeleton/sat-search+checking"
                prove ()
              val elapsed = Time.- (Time.now (), started)
              val _ = observer (sat_target, elapsed)
            in
              theorem
            end
      val target_theorem = phase "skeleton/circuit-implication"
        (fn () =>
          let val supplied_cnf = Thm.EQ_MP cnf_equivalence
            (Thm.ASSUME antecedent)
          in Thm.DISCH antecedent (Thm.MP cnf_theorem supplied_cnf) end) ()
      val _ = Term.aconv (Thm.concl target_theorem) target orelse
        raise ERR "checked_graph_sat_prove" "circuit implication mismatch"
      val instantiated = phase "skeleton/combined-instantiation"
        (fn substitution => Thm.INST substitution target_theorem)
        substitution
      val theorem = phase "skeleton/cnf-definitions"
        (fn definitions => Thm.MP instantiated definitions)
        definition_theorem
    in
      {theorem = theorem, sat_target = sat_target,
       sat_tree_nodes = #tree_nodes sat_measure,
       sat_dag_nodes = #dag_nodes sat_measure}
    end

  fun checked_graph_sat_prove entries root =
    checked_graph_sat_prove_in (new_sat_context ()) entries root

  exception PROCEDURE_UNABLE

  (* Pure propositional replay has no atom-reduction stage.  Construct its
     typed CNF graph directly, keeping all theory atoms opaque, and use the
     same checked circuit certificate and kernel transport as owned replay. *)
  (* A clause about a Boolean gate needs its immediate truth table, not the
     circuits computing its inputs.  Try an opaque clause first, then expose
     each literal's outer connective in turn.  Substitution of the opaque
     atoms into a checked tautology proves the exact original clause.  This
     is incomplete by design; callers retain the full graph procedure. *)
  fun clause_frontier_prove limit target =
    let
      val work = ref 0
      fun tick () =
        (work := !work + 1;
         if !work <= limit then ()
         else raise ERR "clause_frontier_prove" "Boolean frontier too large")
      fun clauses term =
        (tick ();
         if boolSyntax.is_disj term then
           let val (left, right) = boolSyntax.dest_disj term
           in clauses left @ clauses right end
         else [term])
      fun base term =
        if boolSyntax.is_neg term then base (boolSyntax.dest_neg term)
        else term
      val literals = clauses target
      val candidates = List.filter
        (fn term => case skeleton_children term of
           SOME (_ :: _) => true | _ => false) (List.map base literals)
      fun attempt exposed =
        let
          val _ = work := 0
          val atoms = ref (Redblackmap.mkDict Term.compare)
          val substitution = ref []
          (* A gate input may itself be a disjunction spread along the clause
             spine.  Preserve any occurrence of that complete input as one
             atom, rather than flattening it and losing the gate relation. *)
          val stops = HOLset.addList (Term.empty_tmset,
            List.concat (List.map
              (fn term => Option.getOpt (skeleton_children term, []))
              (HOLset.listItems exposed)))
          fun atom term =
            case Redblackmap.peek (!atoms, term) of
              SOME variable => variable
            | NONE =>
                let val variable = Term.genvar Type.bool in
                  atoms := Redblackmap.insert (!atoms, term, variable);
                  substitution := {redex = variable, residue = term} ::
                    !substitution;
                  variable
                end
          fun opaque term = (tick ();
            if Term.aconv term boolSyntax.T orelse
               Term.aconv term boolSyntax.F then term
            else if boolSyntax.is_neg term then
              boolSyntax.mk_neg (opaque (boolSyntax.dest_neg term))
            else atom term)
          fun literal term = (tick ();
            if boolSyntax.is_neg term then
              boolSyntax.mk_neg (literal (boolSyntax.dest_neg term))
            else if HOLset.member (exposed, term) then
              let
                val (head, children) = boolSyntax.strip_comb term
              in Term.list_mk_comb (head, List.map literal children) end
            else opaque term)
          fun clause term = (tick ();
            if HOLset.member (stops, base term) then opaque term
            else if boolSyntax.is_disj term then
              let val (left, right) = boolSyntax.dest_disj term
              in boolSyntax.mk_disj (clause left, clause right) end
            else literal term)
          val schematic = clause target
          val variables = List.map #2 (Redblackmap.listItems (!atoms))
          val valuations = List.foldl
            (fn (_, count) => if count > limit div 2 then limit + 1
                             else count * 2) 1 variables
          val _ = if valuations <= limit then ()
            else raise ERR "clause_frontier_prove"
              "Boolean truth table too large"
          val valuation = Array.array (List.length variables, false)
          fun compile term =
            if Term.aconv term boolSyntax.T then (fn () => true)
            else if Term.aconv term boolSyntax.F then (fn () => false)
            else if Term.is_var term then
              let val index = Lib.index (Term.aconv term) variables
              in fn () => Array.sub (valuation, index) end
            else
              let
                val evaluations = List.map compile
                  (valOf (skeleton_children term))
                fun first () = List.nth (evaluations, 0) ()
                fun second () = List.nth (evaluations, 1) ()
              in
                if boolSyntax.is_neg term then (fn () => not (first ()))
                else if boolSyntax.is_conj term then
                  (fn () => first () andalso second ())
                else if boolSyntax.is_disj term then
                  (fn () => first () orelse second ())
                else if boolSyntax.is_imp term then
                  (fn () => not (first ()) orelse second ())
                else if boolSyntax.is_eq term then
                  (fn () => first () = second ())
                else (fn () => if first () then second ()
                              else List.nth (evaluations, 2) ())
              end
          val evaluate = compile schematic
          fun all_valuations index =
            if index = Array.length valuation then evaluate ()
            else
              (Array.update (valuation, index, false);
               all_valuations (index + 1) andalso
               (Array.update (valuation, index, true);
                all_valuations (index + 1)))
          (* This unchecked search can only decline an attempt.  Acceptance
             still requires the exhaustive kernel proof below. *)
          val _ = if all_valuations 0 then ()
            else raise ERR "clause_frontier_prove"
              "Boolean frontier has a counterexample"
          (* The finite truth table is checked in process.  Hundreds of
             tiny gate clauses must not each launch a SAT subprocess. *)
          val theorem = Tactical.TAC_PROOF (([], schematic),
            List.foldr (fn (variable, continuation) =>
              Tactical.THEN (Tactic.BOOL_CASES_TAC variable, continuation))
              (simpLib.ASM_SIMP_TAC boolSimps.bool_ss []) variables)
          val instantiated = Thm.INST (!substitution) theorem
          val exact = Thm.EQ_MP
            (Thm.ALPHA (Thm.concl instantiated) target) instantiated
          val _ = Library.check_oracle_tags "SmtSkeletonProve"
            "clause-frontier" exact
        in exact end
      fun try [] = raise ERR "clause_frontier_prove"
            "no tautological Boolean frontier"
        | try (candidate :: rest) = attempt candidate
            handle Feedback.HOL_ERR _ => try rest
    in
      try (Term.empty_tmset ::
        List.map (fn term => HOLset.add (Term.empty_tmset, term)) candidates @
        [HOLset.addList (Term.empty_tmset, candidates)])
    end

  fun propositional_prove_in context target =
    let
      val _ = Term.type_of target = Type.bool orelse
        raise ERR "propositional_prove" "target is not Boolean"
      val graph = phase "skeleton/propositional-cnf"
        (build_cnf_graph_mode true) target
      val GraphNode {kind, ...} = #root graph
      val actual = case kind of
          GraphTrue => boolTheory.TRUTH
        | _ => #theorem (phase "skeleton/propositional-sat"
            (checked_graph_sat_prove_in context (#entries graph)) (#root graph))
      val _ = List.null (Thm.hyp actual) orelse
        raise ERR "propositional_prove" "SAT theorem has hypotheses"
      val GraphNode {equality, ...} = #root graph
      val theorem = Thm.EQ_MP (Thm.SYM equality) actual
      val _ = Term.aconv (Thm.concl theorem) target orelse
        raise ERR "propositional_prove" "conclusion does not match target"
      val _ = Library.check_oracle_tags
        "SmtSkeletonProve" "propositional-replay" theorem
    in theorem end

  fun propositional_prove target =
    propositional_prove_in (new_sat_context ()) target

  (* Expose only conditional control flow at equality observations.  Values
     of every type remain opaque; distributing equality over COND uses the
     polymorphic kernel-checked COND_RAND/COND_RATOR laws.  Memoization bounds
     the potentially quadratic product of two conditional value DAGs. *)
  fun conditional_equality_conv target =
    let
      val cache = ref (Redblackmap.mkDict Term.compare)
      val visited = ref 0
      fun visit term =
        case Redblackmap.peek (!cache, term) of
          SOME theorem => anchor_left term theorem
        | NONE =>
            let
              val _ = visited := !visited + 1
              val _ = !visited <=
                  SmtResource.max_skeleton_replay_dag_nodes orelse
                raise ERR "conditional_equality_conv"
                  "conditional equality frontier too large"
              fun equality () =
                let
                  val (left, right) = boolSyntax.dest_eq term
                  fun distribute conversion =
                    let val theorem = conversion term in
                      Thm.TRANS theorem
                        (visit (boolSyntax.rhs (Thm.concl theorem)))
                    end
                in
                  if Term.aconv left right then
                    Conv.REWR_CONV boolTheory.REFL_CLAUSE term
                  else if boolSyntax.is_cond right then
                    distribute (Conv.REWR_CONV boolTheory.COND_RAND)
                  else if boolSyntax.is_cond left then
                    distribute (Conv.THENC
                      (Conv.RATOR_CONV
                         (Conv.REWR_CONV boolTheory.COND_RAND),
                       Conv.REWR_CONV boolTheory.COND_RATOR))
                  else if Term.compare (left, right) = GREATER then
                    Conv.REWR_CONV boolTheory.EQ_SYM_EQ term
                  else Thm.REFL term
                end
              val theorem =
                case skeleton_children term of
                  SOME children => anchor_left term
                    (connective_congruence term (List.map visit children))
                | NONE =>
                    if boolSyntax.is_eq term then equality ()
                    else Thm.REFL term
              val _ = cache := Redblackmap.insert (!cache, term, theorem)
            in theorem end
    in visit target end

  (* Lift checked Boolean equivalences through arbitrary typed applications.
     Theory operators stay uninterpreted: their arguments must be equal by
     congruence, not by an assumed theory identity.  Maximal Boolean islands
     are discharged once rather than lowering all surrounding word circuits. *)
  fun congruence_prove_in context target =
    let
      val (left, right) = boolSyntax.dest_eq target
      val cache = ref (Redblackmap.mkDict
        (pair_compare (Term.compare, Term.compare)))
      val visited = ref 0
      fun boolean_island left right =
        Term.type_of left = Type.bool andalso
        (Option.isSome (skeleton_children left) orelse
         Option.isSome (skeleton_children right))
      fun visit (left, right) =
        if Term.aconv left right then Thm.ALPHA left right
        else
          case Redblackmap.peek (!cache, (left, right)) of
            SOME theorem => theorem
          | NONE =>
              let
                val _ = visited := !visited + 1
                val _ = !visited <=
                    SmtResource.max_skeleton_replay_dag_nodes orelse
                  raise ERR "congruence_prove" "congruence frontier too large"
                fun structural () =
                  if Term.is_comb left andalso Term.is_comb right then
                    let
                      val (left_head, left_arg) = Term.dest_comb left
                      val (right_head, right_arg) = Term.dest_comb right
                    in
                      Thm.MK_COMB (visit (left_head, right_head),
                        visit (left_arg, right_arg))
                    end
                  else raise ERR "congruence_prove"
                    "opaque endpoints are not equal"
                fun boolean () =
                  let
                    val equality = boolSyntax.mk_eq (left, right)
                    val normalized = conditional_equality_conv equality
                    val residue = boolSyntax.rhs (Thm.concl normalized)
                  in Thm.EQ_MP (Thm.SYM normalized)
                    (propositional_prove_in context residue) end
                val theorem =
                  if boolean_island left right then
                    boolean ()
                  else structural ()
                val _ = cache := Redblackmap.insert
                  (!cache, (left, right), theorem)
              in theorem end
      val theorem = visit (left, right)
      val exact = Thm.EQ_MP
        (Thm.ALPHA (Thm.concl theorem) target) theorem
      val _ = List.null (Thm.hyp exact) orelse
        raise ERR "congruence_prove" "congruence introduced hypotheses"
      val _ = Library.check_oracle_tags
        "SmtSkeletonProve" "Boolean congruence" exact
    in exact end

  fun congruence_prove target =
    congruence_prove_in (new_sat_context ()) target

  fun prove_with_owners
      (Context {procedures, fallback, atom_cache}) owners
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
      fun raw_expand atom =
        case (case Redblackmap.peek (owners, atom) of
                SOME name =>
                  SOME (name, procedure_named procedures name, true)
              | NONE => Option.map (fn procedure =>
                  (#name procedure, procedure, false)) fallback) of
          NONE => (Thm.REFL atom, false)
        | SOME (name, procedure, required) =>
            let
              val {expand, ...} = procedure
              val _ = atom_requests := !atom_requests + 1
              val _ = distinct_atoms := HOLset.add (!distinct_atoms, atom)
              fun prove () =
                let
                  val timer = Timer.startRealTimer ()
                  val _ = add_call name
                  val expansion = Profile.profile_with_exn_name
                    ("th_lemma[general](atom:" ^ name ^ ")")
                    expand atom
                  val elapsed = Timer.checkRealTimer timer
                  val _ = atom_time := Time.+ (!atom_time, elapsed)
                in
                  case expansion of
                    Unable =>
                      if required then raise PROCEDURE_UNABLE
                      else (Thm.REFL atom, false)
                  | Expanded theorem =>
                      let
                        val theorem = exact_left atom
                          (validate_theorem name atom theorem)
                        val _ = owned_atoms := !owned_atoms + 1
                        val _ = working_cache :=
                          Redblackmap.insert
                            (!working_cache, atom, theorem)
                        val _ = atom_proofs := !atom_proofs + 1
                      in
                        (theorem, true)
                      end
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
            NONE =>
              (case fallback of
                 NONE => raw_expand term
               | SOME _ =>
                   let
                     val (first, changed) = raw_expand term
                   in
                     if changed then
                       let
                         val residue = boolSyntax.rhs (Thm.concl first)
                         val (rest, rest_changed) = visit residue
                       in
                         (Thm.TRANS first rest,
                          changed orelse rest_changed)
                       end
                     else (first, changed)
                   end)
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
      val graph = phase "skeleton/cnf-normalization"
        build_cnf_graph normalized
      val _ = SmtResource.emit_e0
        ("skeleton-graph nodes=" ^ Int.toString (#graph_nodes graph) ^
         " observations=" ^ Int.toString (#graph_observations graph) ^
         " edges=" ^ Int.toString (#graph_edges graph) ^
         " raw_nodes=" ^ Int.toString (#raw_nodes graph) ^
         " raw_edges=" ^ Int.toString (#raw_edges graph) ^
         " type_nodes=" ^ Int.toString (#type_nodes graph) ^
         " type_observations=" ^
           Int.toString (#type_observations graph) ^
         " type_edges=" ^ Int.toString (#type_edges graph) ^
         " leaf_transport_nodes=" ^ Int.toString (#transport_nodes graph) ^
         " leaf_transport_wall=" ^ Time.toString (#transport_seconds graph))
      val GraphNode
        {representative = normalized, equality = idempotence,
         ...} = #root graph
      val sat_timer = Timer.startRealTimer ()
      val {theorem = actual_theorem, sat_target, sat_tree_nodes,
           sat_dag_nodes} =
        (phase "skeleton/cnf+sat" checked_graph_sat_prove
          (#entries graph) (#root graph)
         handle HolSatLib.SAT_cex theorem =>
           let
             fun label (GraphNode {kind = GraphAtom _, representative, ...}) =
                   let val (head, _) = boolSyntax.strip_comb representative in
                     if Term.is_const head then
                       let
                         val {Thy, Name, ...} = Term.dest_thy_const head
                         fun head_name argument =
                           let val (argument_head, _) =
                             boolSyntax.strip_comb argument
                           in
                             if Term.is_const argument_head then
                               let val {Thy, Name, ...} =
                                 Term.dest_thy_const argument_head
                               in Thy ^ "$" ^ Name end
                             else if Term.is_var argument_head then "variable"
                             else "other"
                           end
                         val (_, arguments) =
                           boolSyntax.strip_comb representative
                         val suffix = if Thy = "fcp" then
                             "[" ^ String.concatWith ","
                               (List.map head_name arguments) ^ "]"
                           else ""
                       in SOME (Thy ^ "$" ^ Name ^ suffix) end
                     else SOME "non-constant"
                   end
               | label _ = NONE
             val labels = List.mapPartial label (#entries graph)
             fun unique [] = []
               | unique (item :: rest) =
                   item :: unique (List.filter (fn other => other <> item) rest)
             val message = "SKELETON_CEX residual_atoms=" ^
               Int.toString (#residual_atoms graph) ^
               " owned_atoms=" ^ Int.toString (!owned_atoms) ^
               " labels=" ^ String.concatWith "," (unique labels)
             val _ = Feedback.HOL_MESG message
           in raise HolSatLib.SAT_cex theorem end)
      val _ =
        if List.null (Thm.hyp actual_theorem) then ()
        else raise ERR "prove" "checked SAT theorem has hypotheses"
      val actual_theorem =
        let val conclusion = Thm.concl actual_theorem in
          if Portable.pointer_eq (conclusion, normalized) then
            actual_theorem
          else
            let
              val equality = phase "skeleton/sat-conclusion-transport"
                (fn () => bounded_nodewise_equality
                  SmtResource.max_skeleton_replay_dag_nodes
                  conclusion normalized) ()
            in Thm.EQ_MP equality actual_theorem end
        end
        handle REANCHOR_LIMIT => raise ERR "prove"
          "checked SAT theorem exceeds the skeleton transport DAG bound"
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
      val procedure_calls = Redblackmap.foldl
        (fn (name, count, result) => (name, count) :: result) [] (!calls)
      val metrics =
        {target_tree_nodes = #tree_nodes target_measure,
         target_dag_nodes = #dag_nodes target_measure,
         skeleton_dag_nodes = HOLset.numItems (!skeleton_nodes),
         normalized_tree_nodes = #normalized_tree_nodes graph,
         normalized_dag_nodes = #normalized_dag_nodes graph,
         sat_tree_nodes = sat_tree_nodes,
         sat_dag_nodes = sat_dag_nodes,
         graph_nodes = #graph_nodes graph,
         graph_observations = #graph_observations graph,
         graph_edges = #graph_edges graph,
         graph_type_nodes = #type_nodes graph,
         graph_type_observations = #type_observations graph,
         graph_type_edges = #type_edges graph,
         graph_leaf_transport_nodes = #transport_nodes graph,
         graph_leaf_transport_seconds = #transport_seconds graph,
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
         residual_atoms = #residual_atoms graph,
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
    handle PROCEDURE_UNABLE =>
             (Feedback.HOL_MESG "SKELETON PROCEDURE_UNABLE"; Declined)
         | HolSatLib.SAT_cex _ =>
             (Feedback.HOL_MESG "SKELETON SAT_CEX"; Declined)
         | HolSatLib.SAT_satisfiable _ =>
             (Feedback.HOL_MESG "SKELETON SAT"; Declined)

end
