structure clasetUnify :> clasetUnify =
struct

open HolKernel

type meta = clasetMeta.meta
type tymeta = clasetMeta.tymeta
type store = clasetMeta.store

datatype mode = Match | Unify
type rule_metas = {terms : meta list, types : tymeta list}
type config = {mode : mode, rule_metas : rule_metas}

fun same_meta left right =
  clasetMeta.is_meta left andalso clasetMeta.is_meta right andalso
  #1 (dest_var left) = #1 (dest_var right)

fun same_tymeta left right =
  clasetMeta.is_tymeta left andalso clasetMeta.is_tymeta right andalso
  dest_vartype left = dest_vartype right

fun term_is_rule ({terms, ...} : rule_metas) tm =
  List.exists (same_meta tm) terms

fun type_is_rule ({types, ...} : rule_metas) ty =
  List.exists (same_tymeta ty) types

fun flexible_term ({mode, rule_metas} : config) tm =
  clasetMeta.is_meta tm andalso
  (case mode of
     Unify => true
   | Match => term_is_rule rule_metas tm)

fun flexible_type ({mode, rule_metas} : config) ty =
  clasetMeta.is_tymeta ty andalso
  (case mode of
     Unify => true
   | Match => type_is_rule rule_metas ty)

fun norm_type store ty = clasetMeta.norm_type store ty

fun fold_pairs step store ([], []) = SOME store
  | fold_pairs step store (left :: lefts, right :: rights) =
      (case step store (left, right) of
         NONE => NONE
       | SOME store' => fold_pairs step store' (lefts, rights))
  | fold_pairs _ _ _ = NONE

fun unify_types store config pair =
  let
    fun recurse current (raw_left, raw_right) =
      let
        val left = norm_type current raw_left
        val right = norm_type current raw_right
      in
        if left = right then SOME current
        else if flexible_type config left then
          clasetMeta.bind_ty (left, right) current
        else if flexible_type config right then
          clasetMeta.bind_ty (right, left) current
        else if is_vartype left orelse is_vartype right then NONE
        else
          let
            val {Thy = left_thy, Tyop = left_op, Args = left_args} =
              dest_thy_type left
            val {Thy = right_thy, Tyop = right_op,
                 Args = right_args} = dest_thy_type right
          in
            if left_thy <> right_thy orelse left_op <> right_op orelse
               length left_args <> length right_args
            then NONE
            else fold_pairs recurse current (left_args, right_args)
          end
      end
  in
    recurse store pair
  end

fun distinct_terms terms =
  length (Lib.op_mk_set aconv terms) = length terms

datatype pattern = NoPattern | Pattern of term

fun pattern_binding store config (head, args) target =
  if flexible_term config head andalso not (null args) andalso
     List.all (clasetMeta.is_eigen store) args andalso
     distinct_terms args
  then Pattern (Term.list_mk_abs (args, target))
  else NoPattern

fun unify store config pair =
  let
    fun bind_term current (left, right) =
      if flexible_term config left then
        clasetMeta.bind (left, right) current
      else if flexible_term config right then
        clasetMeta.bind (right, left) current
      else NONE

    fun recurse current (raw_left, raw_right) =
      case unify_types current config
        (type_of raw_left, type_of raw_right)
      of
        NONE => NONE
      | SOME typed_store =>
          let
            val left = clasetMeta.norm typed_store raw_left
            val right = clasetMeta.norm typed_store raw_right
            val (left_head, left_args) = strip_comb left
            val (right_head, right_args) = strip_comb right
            val applied_meta =
              (clasetMeta.is_meta left_head andalso
               not (null left_args)) orelse
              (clasetMeta.is_meta right_head andalso
               not (null right_args))

            fun approximate () =
              if length left_args <> length right_args then NONE
              else if flexible_term config left_head orelse
                      flexible_term config right_head
              then
                (case recurse typed_store (left_head, right_head) of
                   NONE => NONE
                 | SOME head_store =>
                     fold_pairs recurse head_store
                       (left_args, right_args))
              else if aconv left_head right_head then
                fold_pairs recurse typed_store (left_args, right_args)
              else NONE

            fun structural () =
              case (dest_term left, dest_term right) of
                (VAR _, _) => bind_term typed_store (left, right)
              | (_, VAR _) => bind_term typed_store (right, left)
              | (CONST _, CONST _) => NONE
              | (COMB (left_fun, left_arg),
                 COMB (right_fun, right_arg)) =>
                  (case recurse typed_store (left_fun, right_fun) of
                     NONE => NONE
                   | SOME function_store =>
                       recurse function_store (left_arg, right_arg))
              | (LAMB (left_var, left_body),
                 LAMB (right_var, right_body)) =>
                  let
                    val fresh = genvar (type_of left_var)
                    val left' =
                      subst [left_var |-> fresh] left_body
                    val right' =
                      subst [right_var |-> fresh] right_body
                  in
                    case clasetMeta.register_eigen fresh typed_store of
                      NONE => NONE
                    | SOME scoped_store =>
                        recurse scoped_store (left', right')
                  end
              | _ => NONE
            fun after_patterns () =
              if applied_meta then approximate () else structural ()

            fun try_right_pattern () =
              case pattern_binding typed_store config
                (right_head, right_args) left
              of
                NoPattern => after_patterns ()
              | Pattern residue =>
                  (case clasetMeta.bind
                    (right_head, residue) typed_store
                   of
                     NONE => after_patterns ()
                   | success => success)

            fun try_patterns () =
              case pattern_binding typed_store config
                (left_head, left_args) right
              of
                NoPattern => try_right_pattern ()
              | Pattern residue =>
                  (case clasetMeta.bind
                    (left_head, residue) typed_store
                   of
                     NONE => try_right_pattern ()
                   | success => success)
          in
            if aconv left right then SOME typed_store else try_patterns ()
          end
  in
    recurse store pair
  end

(* Deliberate measured-only fork of [unify].  The ordinary unifier is on a
   very hot production path and must not acquire hook dispatch, clock checks,
   or changed exception edges merely to support a diagnostic.  Keep the fork
   in semantic lockstep through the table-driven parity matrix in
   [classical/selftest.sml]; extend that matrix whenever either worker gains a
   branch. *)
datatype timed_phase = NormalizationSetup | TraversalDecompositionBinding

type timed_unification =
  {clock : unit -> Time.time,
   calls : int ref,
   failures : int ref,
   normalization_setup_time : Time.time ref,
   traversal_decomposition_binding_time : Time.time ref,
   unification_time : Time.time ref,
   max_normalization_setup_time : Time.time ref,
   max_traversal_decomposition_binding_time : Time.time ref,
   max_unification_time : Time.time ref,
   rigid_type_constructor_mismatches : int ref,
   protected_applied_meta_unequal_head_fallbacks : int ref,
   right_pattern_binding_failure_fallbacks : int ref,
   structural_lambda_descents : int ref,
   structural_wildcard_mismatches : int ref}

type timed_unification_statistics =
  {calls : int,
   failures : int,
   normalization_setup_time : Time.time,
   traversal_decomposition_binding_time : Time.time,
   failure_cleanup_time : Time.time,
   unification_time : Time.time,
   max_normalization_setup_time : Time.time,
   max_traversal_decomposition_binding_time : Time.time,
   max_failure_cleanup_time : Time.time,
   max_unification_time : Time.time}

type timed_unification_branch_statistics =
  {rigid_type_constructor_mismatches : int,
   protected_applied_meta_unequal_head_fallbacks : int,
   right_pattern_binding_failure_fallbacks : int,
   structural_lambda_descents : int,
   structural_wildcard_mismatches : int}

exception TIMED_UNIFICATION_CALLBACK of exn

fun new_timed_unification clock : timed_unification =
  {clock = clock, calls = ref 0, failures = ref 0,
   normalization_setup_time = ref Time.zeroTime,
   traversal_decomposition_binding_time = ref Time.zeroTime,
   unification_time = ref Time.zeroTime,
   max_normalization_setup_time = ref Time.zeroTime,
   max_traversal_decomposition_binding_time = ref Time.zeroTime,
   max_unification_time = ref Time.zeroTime,
   rigid_type_constructor_mismatches = ref 0,
   protected_applied_meta_unequal_head_fallbacks = ref 0,
   right_pattern_binding_failure_fallbacks = ref 0,
   structural_lambda_descents = ref 0,
   structural_wildcard_mismatches = ref 0}

fun timed_unification_statistics (timing : timed_unification) =
  {calls = !(#calls timing), failures = !(#failures timing),
   normalization_setup_time = !(#normalization_setup_time timing),
   traversal_decomposition_binding_time =
     !(#traversal_decomposition_binding_time timing),
   failure_cleanup_time = Time.zeroTime,
   unification_time = !(#unification_time timing),
   max_normalization_setup_time =
     !(#max_normalization_setup_time timing),
   max_traversal_decomposition_binding_time =
     !(#max_traversal_decomposition_binding_time timing),
   max_failure_cleanup_time = Time.zeroTime,
   max_unification_time = !(#max_unification_time timing)}

fun timed_unification_branch_statistics (timing : timed_unification) =
  {rigid_type_constructor_mismatches =
     !(#rigid_type_constructor_mismatches timing),
   protected_applied_meta_unequal_head_fallbacks =
     !(#protected_applied_meta_unequal_head_fallbacks timing),
   right_pattern_binding_failure_fallbacks =
     !(#right_pattern_binding_failure_fallbacks timing),
   structural_lambda_descents = !(#structural_lambda_descents timing),
   structural_wildcard_mismatches =
     !(#structural_wildcard_mismatches timing)}

fun unify_timed (timing : timed_unification) store config pair =
  let
    fun invoke_clock () =
      (#clock timing) ()
      handle error => raise TIMED_UNIFICATION_CALLBACK error

    fun add elapsed reference =
      reference := Time.+ (!reference, elapsed)

    fun maximum elapsed reference =
      if Time.< (!reference, elapsed) then reference := elapsed else ()

    val started = invoke_clock ()
    val previous = ref started
    val phase = ref NormalizationSetup
    val call_normalization = ref Time.zeroTime
    val call_traversal = ref Time.zeroTime

    fun accumulate current =
      let
        val finished = invoke_clock ()
        val _ =
          if Time.< (finished, !previous) then
            raise TIMED_UNIFICATION_CALLBACK
              (mk_HOL_ERR "clasetUnify" "unify_timed"
                "the timed diagnostic clock moved backwards")
          else ()
        val elapsed = Time.- (finished, !previous)
        val _ = previous := finished
      in
        case current of
            NormalizationSetup =>
              (add elapsed (#normalization_setup_time timing);
               add elapsed call_normalization)
          | TraversalDecompositionBinding =>
              (add elapsed
                 (#traversal_decomposition_binding_time timing);
               add elapsed call_traversal)
      end

    fun switch next = (accumulate (!phase); phase := next)
    fun normalization () = switch NormalizationSetup
    fun traversal () = switch TraversalDecompositionBinding

    fun finish result =
      let
        val _ = accumulate (!phase)
        val elapsed = Time.+ (!call_normalization, !call_traversal)
        val _ = #calls timing := !(#calls timing) + 1
        val _ =
          case result of
              NONE => #failures timing := !(#failures timing) + 1
            | SOME _ => ()
        val _ = add elapsed (#unification_time timing)
        val _ =
          maximum (!call_normalization)
            (#max_normalization_setup_time timing)
        val _ =
          maximum (!call_traversal)
            (#max_traversal_decomposition_binding_time timing)
        val _ = maximum elapsed (#max_unification_time timing)
      in
        result
      end

    fun fold_pairs_m step current ([], []) = SOME current
      | fold_pairs_m step current (left :: lefts, right :: rights) =
          (case step current (left, right) of
             NONE => NONE
           | SOME next => fold_pairs_m step next (lefts, rights))
      | fold_pairs_m _ _ _ = NONE

    fun unify_types_m initial pair =
      let
        fun recurse current (raw_left, raw_right) =
          let
            val _ = normalization ()
            val left = norm_type current raw_left
            val right = norm_type current raw_right
            val _ = traversal ()
          in
            if left = right then SOME current
            else if flexible_type config left then
              clasetMeta.bind_ty (left, right) current
            else if flexible_type config right then
              clasetMeta.bind_ty (right, left) current
            else if is_vartype left orelse is_vartype right then NONE
            else
              let
                val {Thy = left_thy, Tyop = left_op,
                     Args = left_args} = dest_thy_type left
                val {Thy = right_thy, Tyop = right_op,
                     Args = right_args} = dest_thy_type right
              in
                if left_thy <> right_thy orelse
                   left_op <> right_op orelse
                   length left_args <> length right_args
                then
                  (#rigid_type_constructor_mismatches timing :=
                     !(#rigid_type_constructor_mismatches timing) + 1;
                   NONE)
                else fold_pairs_m recurse current
                  (left_args, right_args)
              end
          end
      in
        recurse initial pair
      end

    fun bind_term current (left, right) =
      (traversal ();
       if flexible_term config left then
         clasetMeta.bind (left, right) current
       else if flexible_term config right then
         clasetMeta.bind (right, left) current
       else NONE)

    fun recurse current (raw_left, raw_right) =
      (traversal ();
       case unify_types_m current
         (type_of raw_left, type_of raw_right)
       of
           NONE => NONE
         | SOME typed_store =>
             let
               val _ = normalization ()
               val left = clasetMeta.norm typed_store raw_left
               val right = clasetMeta.norm typed_store raw_right
               val _ = traversal ()
               val (left_head, left_args) = strip_comb left
               val (right_head, right_args) = strip_comb right
               val applied_meta =
                 (clasetMeta.is_meta left_head andalso
                  not (null left_args)) orelse
                 (clasetMeta.is_meta right_head andalso
                  not (null right_args))

               fun approximate () =
                 if length left_args <> length right_args then NONE
                 else if flexible_term config left_head orelse
                         flexible_term config right_head
                 then
                   (case recurse typed_store (left_head, right_head) of
                      NONE => NONE
                    | SOME head_store =>
                        fold_pairs_m recurse head_store
                          (left_args, right_args))
                 else if aconv left_head right_head then
                   fold_pairs_m recurse typed_store
                     (left_args, right_args)
                 else
                   (#protected_applied_meta_unequal_head_fallbacks timing :=
                      !(#protected_applied_meta_unequal_head_fallbacks timing)
                      + 1;
                    NONE)

               fun structural () =
                 case (dest_term left, dest_term right) of
                     (VAR _, _) => bind_term typed_store (left, right)
                   | (_, VAR _) => bind_term typed_store (right, left)
                   | (CONST _, CONST _) => NONE
                   | (COMB (left_fun, left_arg),
                      COMB (right_fun, right_arg)) =>
                       (case recurse typed_store
                         (left_fun, right_fun)
                        of
                            NONE => NONE
                          | SOME function_store =>
                              recurse function_store
                                (left_arg, right_arg))
                   | (LAMB (left_var, left_body),
                      LAMB (right_var, right_body)) =>
                       let
                         val _ =
                           #structural_lambda_descents timing :=
                             !(#structural_lambda_descents timing) + 1
                         val fresh = genvar (type_of left_var)
                         val left' = subst [left_var |-> fresh] left_body
                         val right' = subst [right_var |-> fresh] right_body
                       in
                         case clasetMeta.register_eigen fresh typed_store of
                             NONE => NONE
                           | SOME scoped_store =>
                               recurse scoped_store (left', right')
                       end
                   | _ =>
                       (#structural_wildcard_mismatches timing :=
                          !(#structural_wildcard_mismatches timing) + 1;
                        NONE)

               fun after_patterns () =
                 if applied_meta then approximate () else structural ()

               fun try_right_pattern () =
                 case pattern_binding typed_store config
                   (right_head, right_args) left
                 of
                     NoPattern => after_patterns ()
                   | Pattern residue =>
                       (case clasetMeta.bind
                         (right_head, residue) typed_store
                        of
                            NONE =>
                              (#right_pattern_binding_failure_fallbacks
                                 timing :=
                                 !(#right_pattern_binding_failure_fallbacks
                                    timing) + 1;
                               after_patterns ())
                          | success => success)

               fun try_patterns () =
                 case pattern_binding typed_store config
                   (left_head, left_args) right
                 of
                     NoPattern => try_right_pattern ()
                   | Pattern residue =>
                       (case clasetMeta.bind
                         (left_head, residue) typed_store
                        of
                            NONE => try_right_pattern ()
                          | success => success)
             in
               if aconv left right then SOME typed_store
               else try_patterns ()
             end)

    val result =
      (finish (recurse store pair)
       handle error =>
         (case error of
              TIMED_UNIFICATION_CALLBACK _ => raise error
            | _ => (ignore (finish NONE); raise error)))
  in
    result
  end

datatype timed_phase_v3 =
    V3NormalizationSetup
  | V3PersistentStoreLookupWalk
  | V3StructuralDecompositionRecursion
  | V3PatternOccursAllowDecision
  | V3PersistentBindingUpdate
  | V3TraversalOther

datatype timed_phase_boundary_v3 = V3PhaseEnter | V3PhaseExit

type timed_unification_common =
  {clock : unit -> Time.time,
   elapsed_sink : Time.time -> unit,
   calls : int ref,
   failures : int ref,
   normalization_setup_events : int ref,
   persistent_store_lookup_walk_events : int ref,
   structural_decomposition_recursion_events : int ref,
   pattern_occurs_allow_decision_events : int ref,
   persistent_binding_update_events : int ref,
   binding_operation_failures : int ref,
   traversal_other_events : int ref,
   normalization_setup_time : Time.time ref,
   persistent_store_lookup_walk_time : Time.time ref,
   structural_decomposition_recursion_time : Time.time ref,
   pattern_occurs_allow_decision_time : Time.time ref,
   persistent_binding_update_time : Time.time ref,
   traversal_other_time : Time.time ref,
   traversal_decomposition_binding_time : Time.time ref,
   unification_time : Time.time ref,
   max_normalization_setup_time : Time.time ref,
   max_persistent_store_lookup_walk_time : Time.time ref,
   max_structural_decomposition_recursion_time : Time.time ref,
   max_pattern_occurs_allow_decision_time : Time.time ref,
   max_persistent_binding_update_time : Time.time ref,
   max_traversal_other_time : Time.time ref,
   max_traversal_decomposition_binding_time : Time.time ref,
   max_unification_time : Time.time ref,
   rigid_type_constructor_mismatches : int ref,
   protected_applied_meta_unequal_head_fallbacks : int ref,
   right_pattern_binding_failure_fallbacks : int ref,
   structural_lambda_descents : int ref,
   structural_wildcard_mismatches : int ref}

type timed_unification_v3 =
  {timing : timed_unification_common,
   operation_phase_trace :
     (timed_phase_boundary_v3 * timed_phase_v3) list ref}

datatype timed_unification_v4 =
  TimedUnificationV4 of timed_unification_common

type timed_unification_statistics_v3 =
  {calls : int,
   failures : int,
   normalization_setup_events : int,
   persistent_store_lookup_walk_events : int,
   structural_decomposition_recursion_events : int,
   pattern_occurs_allow_decision_events : int,
   persistent_binding_update_events : int,
   binding_operation_failures : int,
   traversal_other_events : int,
   operation_phase_trace :
     (timed_phase_boundary_v3 * timed_phase_v3) list,
   normalization_setup_time : Time.time,
   persistent_store_lookup_walk_time : Time.time,
   structural_decomposition_recursion_time : Time.time,
   pattern_occurs_allow_decision_time : Time.time,
   persistent_binding_update_time : Time.time,
   traversal_other_time : Time.time,
   traversal_decomposition_binding_time : Time.time,
   failure_cleanup_time : Time.time,
   unification_time : Time.time,
   max_normalization_setup_time : Time.time,
   max_persistent_store_lookup_walk_time : Time.time,
   max_structural_decomposition_recursion_time : Time.time,
   max_pattern_occurs_allow_decision_time : Time.time,
   max_persistent_binding_update_time : Time.time,
   max_traversal_other_time : Time.time,
   max_traversal_decomposition_binding_time : Time.time,
   max_failure_cleanup_time : Time.time,
   max_unification_time : Time.time}

fun new_timed_unification_common {clock, elapsed}
      : timed_unification_common =
  {clock = clock, elapsed_sink = elapsed, calls = ref 0, failures = ref 0,
   normalization_setup_events = ref 0,
   persistent_store_lookup_walk_events = ref 0,
   structural_decomposition_recursion_events = ref 0,
   pattern_occurs_allow_decision_events = ref 0,
   persistent_binding_update_events = ref 0,
   binding_operation_failures = ref 0,
   traversal_other_events = ref 0,
   normalization_setup_time = ref Time.zeroTime,
   persistent_store_lookup_walk_time = ref Time.zeroTime,
   structural_decomposition_recursion_time = ref Time.zeroTime,
   pattern_occurs_allow_decision_time = ref Time.zeroTime,
   persistent_binding_update_time = ref Time.zeroTime,
   traversal_other_time = ref Time.zeroTime,
   traversal_decomposition_binding_time = ref Time.zeroTime,
   unification_time = ref Time.zeroTime,
   max_normalization_setup_time = ref Time.zeroTime,
   max_persistent_store_lookup_walk_time = ref Time.zeroTime,
   max_structural_decomposition_recursion_time = ref Time.zeroTime,
   max_pattern_occurs_allow_decision_time = ref Time.zeroTime,
   max_persistent_binding_update_time = ref Time.zeroTime,
   max_traversal_other_time = ref Time.zeroTime,
   max_traversal_decomposition_binding_time = ref Time.zeroTime,
   max_unification_time = ref Time.zeroTime,
   rigid_type_constructor_mismatches = ref 0,
   protected_applied_meta_unequal_head_fallbacks = ref 0,
   right_pattern_binding_failure_fallbacks = ref 0,
   structural_lambda_descents = ref 0,
   structural_wildcard_mismatches = ref 0}

fun new_timed_unification_v3_with_sink arguments
      : timed_unification_v3 =
  {timing = new_timed_unification_common arguments,
   operation_phase_trace = ref []}

fun new_timed_unification_v3 clock =
  new_timed_unification_v3_with_sink
    {clock = clock, elapsed = fn _ => ()}

fun new_timed_unification_v4_with_sink arguments
      : timed_unification_v4 =
  TimedUnificationV4 (new_timed_unification_common arguments)

fun new_timed_unification_v4 clock =
  new_timed_unification_v4_with_sink
    {clock = clock, elapsed = fn _ => ()}

fun timed_unification_statistics_v3
      ({timing, operation_phase_trace} : timed_unification_v3) =
  {calls = !(#calls timing), failures = !(#failures timing),
   normalization_setup_events = !(#normalization_setup_events timing),
   persistent_store_lookup_walk_events =
     !(#persistent_store_lookup_walk_events timing),
   structural_decomposition_recursion_events =
     !(#structural_decomposition_recursion_events timing),
   pattern_occurs_allow_decision_events =
     !(#pattern_occurs_allow_decision_events timing),
   persistent_binding_update_events =
     !(#persistent_binding_update_events timing),
   binding_operation_failures = !(#binding_operation_failures timing),
   traversal_other_events = !(#traversal_other_events timing),
   operation_phase_trace = rev (!operation_phase_trace),
   normalization_setup_time = !(#normalization_setup_time timing),
   persistent_store_lookup_walk_time =
     !(#persistent_store_lookup_walk_time timing),
   structural_decomposition_recursion_time =
     !(#structural_decomposition_recursion_time timing),
   pattern_occurs_allow_decision_time =
     !(#pattern_occurs_allow_decision_time timing),
   persistent_binding_update_time =
     !(#persistent_binding_update_time timing),
   traversal_other_time = !(#traversal_other_time timing),
   traversal_decomposition_binding_time =
     !(#traversal_decomposition_binding_time timing),
   failure_cleanup_time = Time.zeroTime,
   unification_time = !(#unification_time timing),
   max_normalization_setup_time =
     !(#max_normalization_setup_time timing),
   max_persistent_store_lookup_walk_time =
     !(#max_persistent_store_lookup_walk_time timing),
   max_structural_decomposition_recursion_time =
     !(#max_structural_decomposition_recursion_time timing),
   max_pattern_occurs_allow_decision_time =
     !(#max_pattern_occurs_allow_decision_time timing),
   max_persistent_binding_update_time =
     !(#max_persistent_binding_update_time timing),
   max_traversal_other_time = !(#max_traversal_other_time timing),
   max_traversal_decomposition_binding_time =
     !(#max_traversal_decomposition_binding_time timing),
   max_failure_cleanup_time = Time.zeroTime,
   max_unification_time = !(#max_unification_time timing)}

fun timed_unification_branch_statistics_v3
      ({timing, ...} : timed_unification_v3) =
  {rigid_type_constructor_mismatches =
     !(#rigid_type_constructor_mismatches timing),
   protected_applied_meta_unequal_head_fallbacks =
     !(#protected_applied_meta_unequal_head_fallbacks timing),
   right_pattern_binding_failure_fallbacks =
     !(#right_pattern_binding_failure_fallbacks timing),
   structural_lambda_descents = !(#structural_lambda_descents timing),
   structural_wildcard_mismatches =
     !(#structural_wildcard_mismatches timing)}

type timed_unification_statistics_v4 =
  {calls : int,
   failures : int,
   normalization_setup_events : int,
   persistent_store_lookup_walk_events : int,
   structural_decomposition_recursion_events : int,
   pattern_occurs_allow_decision_events : int,
   persistent_binding_update_events : int,
   binding_operation_failures : int,
   traversal_other_events : int,
   normalization_setup_time : Time.time,
   persistent_store_lookup_walk_time : Time.time,
   structural_decomposition_recursion_time : Time.time,
   pattern_occurs_allow_decision_time : Time.time,
   persistent_binding_update_time : Time.time,
   traversal_other_time : Time.time,
   traversal_decomposition_binding_time : Time.time,
   failure_cleanup_time : Time.time,
   unification_time : Time.time,
   max_normalization_setup_time : Time.time,
   max_persistent_store_lookup_walk_time : Time.time,
   max_structural_decomposition_recursion_time : Time.time,
   max_pattern_occurs_allow_decision_time : Time.time,
   max_persistent_binding_update_time : Time.time,
   max_traversal_other_time : Time.time,
   max_traversal_decomposition_binding_time : Time.time,
   max_failure_cleanup_time : Time.time,
   max_unification_time : Time.time}

fun timed_unification_statistics_v4
      (TimedUnificationV4 timing) =
  {calls = !(#calls timing), failures = !(#failures timing),
   normalization_setup_events = !(#normalization_setup_events timing),
     persistent_store_lookup_walk_events =
       !(#persistent_store_lookup_walk_events timing),
     structural_decomposition_recursion_events =
       !(#structural_decomposition_recursion_events timing),
     pattern_occurs_allow_decision_events =
       !(#pattern_occurs_allow_decision_events timing),
     persistent_binding_update_events =
       !(#persistent_binding_update_events timing),
     binding_operation_failures = !(#binding_operation_failures timing),
     traversal_other_events = !(#traversal_other_events timing),
     normalization_setup_time = !(#normalization_setup_time timing),
     persistent_store_lookup_walk_time =
       !(#persistent_store_lookup_walk_time timing),
     structural_decomposition_recursion_time =
       !(#structural_decomposition_recursion_time timing),
     pattern_occurs_allow_decision_time =
       !(#pattern_occurs_allow_decision_time timing),
     persistent_binding_update_time =
       !(#persistent_binding_update_time timing),
     traversal_other_time = !(#traversal_other_time timing),
     traversal_decomposition_binding_time =
       !(#traversal_decomposition_binding_time timing),
     failure_cleanup_time = Time.zeroTime,
     unification_time = !(#unification_time timing),
     max_normalization_setup_time =
       !(#max_normalization_setup_time timing),
     max_persistent_store_lookup_walk_time =
       !(#max_persistent_store_lookup_walk_time timing),
     max_structural_decomposition_recursion_time =
       !(#max_structural_decomposition_recursion_time timing),
     max_pattern_occurs_allow_decision_time =
       !(#max_pattern_occurs_allow_decision_time timing),
     max_persistent_binding_update_time =
       !(#max_persistent_binding_update_time timing),
     max_traversal_other_time = !(#max_traversal_other_time timing),
     max_traversal_decomposition_binding_time =
       !(#max_traversal_decomposition_binding_time timing),
     max_failure_cleanup_time = Time.zeroTime,
     max_unification_time = !(#max_unification_time timing)}

fun timed_unification_branch_statistics_v4
      (TimedUnificationV4 timing) =
  {rigid_type_constructor_mismatches =
     !(#rigid_type_constructor_mismatches timing),
   protected_applied_meta_unequal_head_fallbacks =
     !(#protected_applied_meta_unequal_head_fallbacks timing),
   right_pattern_binding_failure_fallbacks =
     !(#right_pattern_binding_failure_fallbacks timing),
   structural_lambda_descents = !(#structural_lambda_descents timing),
   structural_wildcard_mismatches =
     !(#structural_wildcard_mismatches timing)}

fun timed_unification_trace_allocations_v4
      (_ : timed_unification_v4) = 0

fun unify_timed_common record (timing : timed_unification_common)
      store config pair =
  let
    datatype phase_frame =
        RunningFrame of timed_phase_v3 * Time.time
      | PausedFrame of timed_phase_v3

    fun invoke_clock () =
      (#clock timing) ()
      handle error => raise TIMED_UNIFICATION_CALLBACK error

    fun add elapsed reference =
      reference := Time.+ (!reference, elapsed)

    fun maximum elapsed reference =
      if Time.< (!reference, elapsed) then reference := elapsed else ()

    fun increment reference = reference := !reference + 1

    val call_normalization = ref Time.zeroTime
    val call_lookup = ref Time.zeroTime
    val call_structural = ref Time.zeroTime
    val call_decision = ref Time.zeroTime
    val call_binding = ref Time.zeroTime
    val call_other = ref Time.zeroTime
    val phase_stack =
      ref ([] : phase_frame list)

    fun accumulate current elapsed =
      case current of
            V3NormalizationSetup =>
              add elapsed call_normalization
          | V3PersistentStoreLookupWalk =>
              add elapsed call_lookup
          | V3StructuralDecompositionRecursion =>
              add elapsed call_structural
          | V3PatternOccursAllowDecision =>
              add elapsed call_decision
          | V3PersistentBindingUpdate =>
              add elapsed call_binding
          | V3TraversalOther =>
              add elapsed call_other

    fun count_event next =
      case next of
          V3NormalizationSetup =>
            increment (#normalization_setup_events timing)
        | V3PersistentStoreLookupWalk =>
            increment (#persistent_store_lookup_walk_events timing)
        | V3StructuralDecompositionRecursion =>
            increment (#structural_decomposition_recursion_events timing)
        | V3PatternOccursAllowDecision =>
            increment (#pattern_occurs_allow_decision_events timing)
        | V3PersistentBindingUpdate =>
            increment (#persistent_binding_update_events timing)
        | V3TraversalOther => increment (#traversal_other_events timing)

    fun backwards () =
      raise TIMED_UNIFICATION_CALLBACK
        (mk_HOL_ERR "clasetUnify" "unify_timed_v3"
          "the timed diagnostic clock moved backwards")

    fun pause finished [] = ()
      | pause finished (PausedFrame _ :: _) = ()
      | pause finished (RunningFrame (phase, started) :: _) =
          if Time.< (finished, started) then backwards ()
          else accumulate phase (Time.- (finished, started))

    fun enter phase =
      let
        val now = invoke_clock ()
        val _ = pause now (!phase_stack)
        val parents =
          case !phase_stack of
              [] => []
            | RunningFrame (parent, _) :: rest =>
                PausedFrame parent :: rest
            | PausedFrame parent :: rest =>
                PausedFrame parent :: rest
        val _ = phase_stack := RunningFrame (phase, now) :: parents
        val _ = count_event phase
      in
        record V3PhaseEnter phase
      end

    fun exit phase =
      case !phase_stack of
          [] =>
            raise TIMED_UNIFICATION_CALLBACK
              (mk_HOL_ERR "clasetUnify" "unify_timed_v3"
                "the timed diagnostic phase stack is empty")
        | PausedFrame active :: parents =>
            if active <> phase then
              raise TIMED_UNIFICATION_CALLBACK
                (mk_HOL_ERR "clasetUnify" "unify_timed_v3"
                  "the timed diagnostic phase stack is inconsistent")
            else phase_stack := parents
        | RunningFrame (active, started) :: parents =>
            let
              (* Pop first.  Any failure below leaves a parent paused, so
                 unwinding cannot attempt to close this child twice. *)
              val _ = phase_stack := parents
              val now = invoke_clock ()
              val _ =
                if active <> phase then
                  raise TIMED_UNIFICATION_CALLBACK
                    (mk_HOL_ERR "clasetUnify" "unify_timed_v3"
                      "the timed diagnostic phase stack is inconsistent")
                else if Time.< (now, started) then backwards ()
                else ()
              val _ = accumulate active (Time.- (now, started))
              val resumed =
                case parents of
                    [] => []
                  | RunningFrame (parent, _) :: rest =>
                      RunningFrame (parent, now) :: rest
                  | PausedFrame parent :: rest =>
                      RunningFrame (parent, now) :: rest
              val _ = phase_stack := resumed
            in
              record V3PhaseExit phase
            end

    fun scoped phase operation =
      let
        val _ = enter phase
        val result =
          operation ()
          handle error => ((exit phase handle _ => ()); raise error)
        val _ = exit phase
      in
        result
      end

    fun meta_phase meta =
      case meta of
             clasetMeta.DiagnosticNormalizationSetup =>
               V3NormalizationSetup
           | clasetMeta.DiagnosticStoreLookupWalk =>
               V3PersistentStoreLookupWalk
           | clasetMeta.DiagnosticPatternOccursAllowDecision =>
               V3PatternOccursAllowDecision
           | clasetMeta.DiagnosticPersistentBindingUpdate =>
               V3PersistentBindingUpdate
           | clasetMeta.DiagnosticTraversalOther => V3TraversalOther

    fun meta_switch (boundary, phase) =
      case boundary of
          clasetMeta.DiagnosticEnter => enter (meta_phase phase)
        | clasetMeta.DiagnosticExit => exit (meta_phase phase)

    fun finish result =
      let
        val _ =
          if null (!phase_stack) then ()
          else
            raise TIMED_UNIFICATION_CALLBACK
              (mk_HOL_ERR "clasetUnify" "unify_timed_v3"
                "the timed diagnostic phase stack is not empty")
        val traversal =
          Time.+
            (!call_lookup,
             Time.+
               (!call_structural,
                Time.+
                  (!call_decision,
                   Time.+ (!call_binding, !call_other))))
        val elapsed = Time.+ (!call_normalization, traversal)
        val _ =
          ((#elapsed_sink timing) elapsed
           handle error => raise TIMED_UNIFICATION_CALLBACK error)
        val _ = add (!call_normalization)
          (#normalization_setup_time timing)
        val _ = add (!call_lookup)
          (#persistent_store_lookup_walk_time timing)
        val _ = add (!call_structural)
          (#structural_decomposition_recursion_time timing)
        val _ = add (!call_decision)
          (#pattern_occurs_allow_decision_time timing)
        val _ = add (!call_binding)
          (#persistent_binding_update_time timing)
        val _ = add (!call_other) (#traversal_other_time timing)
        val _ = increment (#calls timing)
        val _ =
          case result of
              NONE => increment (#failures timing)
            | SOME _ => ()
        val _ = add traversal (#traversal_decomposition_binding_time timing)
        val _ = add elapsed (#unification_time timing)
        val _ = maximum (!call_normalization)
          (#max_normalization_setup_time timing)
        val _ = maximum (!call_lookup)
          (#max_persistent_store_lookup_walk_time timing)
        val _ = maximum (!call_structural)
          (#max_structural_decomposition_recursion_time timing)
        val _ = maximum (!call_decision)
          (#max_pattern_occurs_allow_decision_time timing)
        val _ = maximum (!call_binding)
          (#max_persistent_binding_update_time timing)
        val _ = maximum (!call_other) (#max_traversal_other_time timing)
        val _ = maximum traversal
          (#max_traversal_decomposition_binding_time timing)
        val _ = maximum elapsed (#max_unification_time timing)
      in
        result
      end

    fun binding operation =
      let
        val result = operation ()
        val _ =
          case result of
              NONE => increment (#binding_operation_failures timing)
            | SOME _ => ()
      in
        result
      end

    fun fold_pairs_m step current ([], []) = SOME current
      | fold_pairs_m step current (left :: lefts, right :: rights) =
          scoped V3StructuralDecompositionRecursion
            (fn () =>
              case step current (left, right) of
                  NONE => NONE
                | SOME next => fold_pairs_m step next (lefts, rights))
      | fold_pairs_m _ _ _ =
          scoped V3StructuralDecompositionRecursion (fn () => NONE)

    fun unify_types_m initial pair =
      let
        fun recurse current (raw_left, raw_right) =
          let
            val left =
              clasetMeta.norm_type_diagnostic meta_switch current raw_left
            val right =
              clasetMeta.norm_type_diagnostic meta_switch current raw_right
          in
            scoped V3PatternOccursAllowDecision
              (fn () =>
                if left = right then SOME current
                else if flexible_type config left then
                  binding
                    (fn () =>
                      clasetMeta.bind_ty_diagnostic meta_switch
                        (left, right) current)
                else if flexible_type config right then
                  binding
                    (fn () =>
                      clasetMeta.bind_ty_diagnostic meta_switch
                        (right, left) current)
                else if is_vartype left orelse is_vartype right then NONE
                else
                  scoped V3StructuralDecompositionRecursion
                    (fn () =>
                      let
                        val {Thy = left_thy, Tyop = left_op,
                             Args = left_args} = dest_thy_type left
                        val {Thy = right_thy, Tyop = right_op,
                             Args = right_args} = dest_thy_type right
                      in
                        if left_thy <> right_thy orelse
                           left_op <> right_op orelse
                           length left_args <> length right_args
                        then
                          (increment
                             (#rigid_type_constructor_mismatches timing);
                           NONE)
                        else
                          fold_pairs_m recurse current
                            (left_args, right_args)
                      end))
          end
      in
        recurse initial pair
      end

    fun pattern_binding_m current (head, args) target =
      scoped V3PatternOccursAllowDecision
        (fn () =>
          if flexible_term config head andalso not (null args) andalso
             List.all
               (clasetMeta.is_eigen_diagnostic meta_switch current) args
             andalso distinct_terms args
          then
            scoped V3NormalizationSetup
              (fn () => Pattern (Term.list_mk_abs (args, target)))
          else NoPattern)

    fun bind_term current (left, right) =
      scoped V3PatternOccursAllowDecision
        (fn () =>
          if flexible_term config left then
            binding
              (fn () =>
                clasetMeta.bind_diagnostic meta_switch
                  (left, right) current)
          else if flexible_term config right then
            binding
              (fn () =>
                clasetMeta.bind_diagnostic meta_switch
                  (right, left) current)
          else NONE)

    fun recurse current (raw_left, raw_right) =
      scoped V3StructuralDecompositionRecursion
        (fn () =>
          case unify_types_m current (type_of raw_left, type_of raw_right) of
           NONE => NONE
         | SOME typed_store =>
             let
               val left =
                 clasetMeta.norm_diagnostic meta_switch typed_store raw_left
               val right =
                 clasetMeta.norm_diagnostic meta_switch typed_store raw_right
               val (left_head, left_args) = strip_comb left
               val (right_head, right_args) = strip_comb right
               val applied_meta =
                 scoped V3PatternOccursAllowDecision
                   (fn () =>
                     (clasetMeta.is_meta left_head andalso
                      not (null left_args)) orelse
                     (clasetMeta.is_meta right_head andalso
                      not (null right_args)))

               fun approximate () =
                 scoped V3StructuralDecompositionRecursion
                   (fn () =>
                     if length left_args <> length right_args then NONE
                     else
                       scoped V3PatternOccursAllowDecision
                         (fn () =>
                           if flexible_term config left_head orelse
                              flexible_term config right_head
                           then
                             (case recurse typed_store
                               (left_head, right_head)
                              of
                                  NONE => NONE
                                | SOME head_store =>
                                    fold_pairs_m recurse head_store
                                      (left_args, right_args))
                           else if aconv left_head right_head then
                             fold_pairs_m recurse typed_store
                               (left_args, right_args)
                           else
                             (increment
                                (#protected_applied_meta_unequal_head_fallbacks
                                  timing);
                              NONE)))

               fun structural () =
                 scoped V3StructuralDecompositionRecursion
                   (fn () =>
                     case (dest_term left, dest_term right) of
                      (VAR _, _) => bind_term typed_store (left, right)
                    | (_, VAR _) => bind_term typed_store (right, left)
                    | (CONST _, CONST _) => NONE
                    | (COMB (left_fun, left_arg),
                       COMB (right_fun, right_arg)) =>
                        (case recurse typed_store
                          (left_fun, right_fun)
                         of
                             NONE => NONE
                           | SOME function_store =>
                               recurse function_store
                                 (left_arg, right_arg))
                    | (LAMB (left_var, left_body),
                       LAMB (right_var, right_body)) =>
                        let
                          val _ =
                            increment (#structural_lambda_descents timing)
                          val fresh = genvar (type_of left_var)
                          val left' = subst [left_var |-> fresh] left_body
                          val right' = subst [right_var |-> fresh] right_body
                        in
                          case binding
                            (fn () =>
                              clasetMeta.register_eigen_diagnostic
                                meta_switch fresh typed_store)
                          of
                              NONE => NONE
                            | SOME scoped_store =>
                                recurse scoped_store (left', right')
                        end
                    | _ =>
                        (increment (#structural_wildcard_mismatches timing);
                         NONE))

               fun after_patterns () =
                 scoped V3PatternOccursAllowDecision
                   (fn () =>
                     if applied_meta then approximate () else structural ())

               fun try_right_pattern () =
                 case pattern_binding_m typed_store
                   (right_head, right_args) left
                 of
                     NoPattern => after_patterns ()
                   | Pattern residue =>
                       (case binding
                         (fn () =>
                           clasetMeta.bind_diagnostic meta_switch
                             (right_head, residue) typed_store)
                        of
                            NONE =>
                              (increment
                                 (#right_pattern_binding_failure_fallbacks
                                   timing);
                               after_patterns ())
                          | success => success)

               fun try_patterns () =
                 case pattern_binding_m typed_store
                   (left_head, left_args) right
                 of
                     NoPattern => try_right_pattern ()
                   | Pattern residue =>
                       (case binding
                         (fn () =>
                           clasetMeta.bind_diagnostic meta_switch
                             (left_head, residue) typed_store)
                        of
                            NONE => try_right_pattern ()
                          | success => success)
             in
               scoped V3PatternOccursAllowDecision
                 (fn () =>
                   if aconv left right then SOME typed_store
                   else try_patterns ())
             end)

    val result =
      (finish (recurse store pair)
       handle error =>
         (case error of
              TIMED_UNIFICATION_CALLBACK _ => raise error
            | _ =>
                ((ignore (finish NONE) handle _ => ()); raise error)))
  in
    result
  end

fun unify_timed_v3
      ({timing, operation_phase_trace} : timed_unification_v3)
      store config pair =
  unify_timed_common
    (fn boundary => fn phase =>
      operation_phase_trace :=
        (boundary, phase) :: !operation_phase_trace)
    timing store config pair

fun unify_timed_v4 (TimedUnificationV4 timing) store config pair =
  unify_timed_common (fn _ => fn _ => ()) timing store config pair

end
