structure clasetUnify :> clasetUnify =
struct

open HolKernel

type meta = clasetMeta.meta
type tymeta = clasetMeta.tymeta
type store = clasetMeta.store

datatype mode = Match | Unify
type rule_metas = {terms : meta list, types : tymeta list}
type config = {mode : mode, rule_metas : rule_metas}

val same_meta = clasetMeta.same_meta
val same_tymeta = clasetMeta.same_tymeta

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

end
