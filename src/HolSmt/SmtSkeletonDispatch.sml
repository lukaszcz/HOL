(* Copyright (c) 2026 The HOL4 contributors. *)

(* Bounded, mutually-exclusive ownership for skeleton atom reduction. *)

structure SmtSkeletonDispatch =
struct

  open HolKernel

  val ERR = Feedback.mk_HOL_ERR "SmtSkeletonDispatch"

  datatype attempt =
      Proved of {theorem : thm, metrics : SmtSkeletonProve.metrics}
    | Declined

  val regex_constants =
    [("smtstring", "smt_in_re"),
     ("smtstringz3", "aut_accept")]

  val integer_operators =
    ["int_lt", "int_le", "int_add", "int_sub", "int_mul", "int_neg"]

  val real_operators =
    ["real_lt", "real_lte", "real_add", "real_sub", "real_mul",
     "real_neg"]

  fun member name = List.exists (Lib.equal name)

  fun node_features term =
    if not (Term.is_const term) then (false, false, false, false)
    else
      let val {Thy, Name, ...} = Term.dest_thy_const term in
        (Thy = "words",
         List.exists
           (fn (thy, name) => Thy = thy andalso Name = name)
           regex_constants,
         (Thy = "integer" andalso member Name integer_operators) orelse
         (Thy = "real" andalso member Name real_operators),
         (Thy = "integer" andalso
            member Name ["ediv", "emod", "int_abs"]) orelse
         (Thy = "real" andalso member Name ["real_abs", "real_div"]) orelse
         (Thy = "HolSmt" andalso
            member Name ["smt_ediv_total", "smt_emod_total"]))
      end

  fun merge_features ((word1, regex1, arith1, arith_boundary1),
      (word2, regex2, arith2, arith_boundary2)) =
    (word1 orelse word2, regex1 orelse regex2, arith1 orelse arith2,
     arith_boundary1 orelse arith_boundary2)

  fun conversion_attempt conversion atom =
    SmtSkeletonProve.Expanded (conversion atom)
    handle Conv.UNCHANGED => SmtSkeletonProve.Unable

  fun arithmetic_attempt arith_prove atom =
    let
      fun prove target =
        SOME (arith_prove target)
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else NONE
    in
      case prove atom of
        SOME theorem =>
          SmtSkeletonProve.Expanded (Drule.EQT_INTRO theorem)
      | NONE =>
          (case prove (boolSyntax.mk_neg atom) of
             SOME theorem =>
               SmtSkeletonProve.Expanded (Drule.EQF_INTRO theorem)
           | NONE => SmtSkeletonProve.Unable)
    end

  fun new_context arith_prove =
    SmtSkeletonProve.new_context
      [{name = "char-word",
        expand = conversion_attempt
          SmtStringProve.char_word_expansion_conv},
       {name = "word",
        expand = conversion_attempt blastLib.BBLAST_CONV},
       {name = "ground-regex",
        expand = conversion_attempt SmtStringProve.ground_eval_conv},
       {name = "arithmetic",
        expand = arithmetic_attempt arith_prove}]

  val procedure_names = SmtSkeletonProve.procedure_names

  fun distinct strings =
    let
      fun loop _ [] = true
        | loop seen (name :: rest) =
            not (HOLset.member (seen, name)) andalso
            loop (HOLset.add (seen, name)) rest
    in
      loop (HOLset.empty String.compare) strings
    end

  fun analyze context target =
    let
      val names = procedure_names context
      val _ = if distinct names then () else
        raise ERR "analyze" "duplicate atom-procedure registry name"
      val feature_cache = ref (Redblackmap.mkDict Term.compare)
      val observed = ref 0
      fun summary term =
        case Redblackmap.peek (!feature_cache, term) of
          SOME result => result
        | NONE =>
            let
              val _ = observed := !observed + 1
              val _ = SmtResource.check_dag_size_for
                "Skeleton" "general-reduction" (!observed)
              val children = List.map summary
                (SmtSkeletonProve.term_children term)
              val result_features = List.foldl
                (fn ((child_features, _), aggregate) =>
                  merge_features (aggregate, child_features))
                (node_features term) children
              val result_tree = List.foldl
                (fn ((_, child_tree), aggregate) =>
                  SmtSkeletonProve.saturated_add aggregate child_tree)
                1 children
              val result = (result_features, result_tree)
              val _ = feature_cache :=
                Redblackmap.insert (!feature_cache, term, result)
            in
              result
            end
      val (_, target_tree_nodes) = summary target
      val owners = ref (Redblackmap.mkDict Term.compare)
      val skeleton_nodes = ref (HOLset.empty Term.compare)
      val has_owner = ref false
      val ambiguous = ref false
      fun select atom =
        let
          val ((word, regex, arith, arith_boundary), _) = summary atom
          val char = SmtStringProve.char_word_expansion_domain atom
          val candidates =
            (if char then ["char-word"] else []) @
              (if word andalso not char then ["word"] else []) @
              (if regex andalso List.null (Term.free_vars atom) then
                 ["ground-regex"]
               else []) @
              (if arith andalso not arith_boundary andalso
                  not (Library.is_nonlinear atom) then
                 ["arithmetic"]
               else [])
        in
          case candidates of
            [] => ()
          | [name] =>
              (has_owner := true;
               owners := Redblackmap.insert (!owners, atom, name))
          | _ => ambiguous := true
        end
      fun skeleton term =
        if HOLset.member (!skeleton_nodes, term) then ()
        else
          let val _ = skeleton_nodes := HOLset.add (!skeleton_nodes, term)
          in
            case SmtSkeletonProve.skeleton_children term of
              NONE => select term
            | SOME children => List.app skeleton children
          end
      val root_is_connective =
        case SmtSkeletonProve.skeleton_children target of
          SOME _ => true
        | NONE => false
      val _ = if root_is_connective then skeleton target else ()
    in
      if Term.type_of target <> Type.bool orelse
         not root_is_connective orelse !ambiguous orelse not (!has_owner) then
        NONE
      else
        SOME
          {owners = !owners,
           target_measure =
             {tree_nodes = target_tree_nodes, dag_nodes = !observed}}
    end

  fun attempt context target =
    let
      fun run target =
        if Term.type_of target <> Type.bool orelse
           (case SmtSkeletonProve.skeleton_children target of
              NONE => true
            | SOME _ => false) then
          Declined
        else
          case SmtResource.profile_phase "skeleton/ownership-analysis"
              (analyze context) target of
            NONE => Declined
          | SOME {owners, target_measure} =>
              (case SmtSkeletonProve.attempt_with_owners
                  context owners target_measure target of
                 SmtSkeletonProve.Proved result => Proved result
               | SmtSkeletonProve.Declined => Declined)
    in
      Profile.profile_with_exn_name
        "th_lemma[general](candidate/attempt)"
        (SmtResource.with_resource_step_time
          "Skeleton" "general-reduction" run) target
    end

  fun prove context target =
    case attempt context target of
      Proved result => result
    | Declined => raise ERR "prove" "general reduction declined"

end
