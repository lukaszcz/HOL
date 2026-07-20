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

end
