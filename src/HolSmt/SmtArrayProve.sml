(* Copyright (c) 2026 The HOL4 contributors. *)

(* Solver-neutral checked replay support for SMT-LIB ArraysEx lemmas. *)

structure SmtArrayProve =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtArrayProve"

  (* METIS on the array-replay path runs with a time/inference bound so that
     a hard or ultimately-unprovable goal cannot hang proof reconstruction
     (mirrors the bounded METIS in Alethe_ProofReplay). *)
  val metis_limit : mlibMeter.limit = {time = SOME 1.0, infs = SOME 5000}
  fun with_metis_limit f = Lib.with_flag (metisTools.limit, metis_limit) f

  fun unsupported t =
    raise ERR "array_prove"
      ("unsupported th-lemma shape: theory=array; checked replay is only " ^
       "implemented for function-update select/store/extensionality lemmas; " ^
       "conclusion=" ^ Library.term_to_string t)

  (* A simplification prover that deals with function (i.e., array) updates
     when the indices are integer or word literals. *)
  val simp_prove_update =
  let
    val word_type = wordsSyntax.mk_word_type Type.alpha
    val x = Term.mk_var ("x", word_type)
    val y = Term.mk_var ("y", word_type)
    val pat = boolSyntax.mk_eq (x, y)
  in
    simpLib.SIMP_PROVE (simpLib.&& (simpLib.++
    (intSimps.int_ss, simpLib.std_conv_ss {name = "word_EQ_CONV",
      pats = [pat], conv = wordsLib.word_EQ_CONV}),
    [combinTheory.UPDATE_def, boolTheory.EQ_SYM_EQ])) []
  end

  val array_rewrites = [
    combinTheory.UPDATE_def,
    combinTheory.APPLY_UPDATE_THM,
    combinTheory.UPDATE_APPLY_IMP_ID,
    combinTheory.UPDATE_EQ,
    boolTheory.FUN_EQ_THM,
    boolTheory.EQ_SYM_EQ
  ]

  (* A minimal, array-oriented simpset for the RW_TAC-based provers below.
     It deliberately avoids the general arithmetic decision procedures that
     srw_ss() pulls in (the source of nonlinear-arithmetic blowups), while
     still reducing literal integer/word indices so that select/store lemmas
     over concrete indices normalize.  Built from bool_ss plus the explicit
     array rewrites, a num reducer, and a word-equality conv. *)
  val array_ss =
  let
    val word_type = wordsSyntax.mk_word_type Type.alpha
    val x = Term.mk_var ("x", word_type)
    val y = Term.mk_var ("y", word_type)
    val pat = boolSyntax.mk_eq (x, y)
  in
    simpLib.++ (simpLib.++ (simpLib.++
      (boolSimps.bool_ss, numSimps.REDUCE_ss),
      intSimps.INT_REDUCE_ss),
      simpLib.std_conv_ss {name = "word_EQ_CONV",
        pats = [pat], conv = wordsLib.word_EQ_CONV})
  end

  fun symbolic_index_prove t =
    with_metis_limit (fn () =>
      Tactical.prove (t,
        Tactical.THEN (bossLib.RW_TAC array_ss [
            combinTheory.UPDATE_def,
            combinTheory.APPLY_UPDATE_THM,
            boolTheory.EQ_SYM_EQ
          ], bossLib.METIS_TAC []))) ()

  fun extensionality_prove t =
    Tactical.prove (t,
      bossLib.RW_TAC array_ss [
        boolTheory.FUN_EQ_THM,
        combinTheory.APPLY_UPDATE_THM,
        combinTheory.UPDATE_APPLY_IMP_ID,
        combinTheory.UPDATE_EQ,
        boolTheory.EQ_SYM_EQ
      ])

  fun choice_extensionality_prove t =
    with_metis_limit (fn () =>
      Tactical.prove (t,
        Tactical.THEN
          (bossLib.RW_TAC array_ss array_rewrites,
           bossLib.METIS_TAC [boolTheory.SELECT_AX]))) ()

  fun metis_array_prove t =
    with_metis_limit (fn () => metisLib.METIS_PROVE array_rewrites t) ()

  fun has_update_comb t =
    Lib.can (HolKernel.find_term combinSyntax.is_update_comb) t

  (* Genuine array lemmas either contain an UPDATE (store) combinator, or are
     extensionality equalities between function-typed terms.  Arithmetic goals
     such as `... = 0` are equalities at a base type (:int/:real/:bool), for
     which `Type.dom_rng (type_of lhs)` fails.  Gating on this predicate lets
     array_prove fail fast on non-array goals, so its unbounded RW_TAC/METIS
     tactics never run on arithmetic/word/boolean goals. *)
  fun is_array_goal t =
    has_update_comb t orelse
    List.exists
      (fn lit =>
        case Lib.total boolSyntax.dest_eq lit of
          SOME (l, _) => Lib.can Type.dom_rng (Term.type_of l)
        | NONE => false)
      (boolSyntax.strip_disj t)

  (* Degenerate/trivial conclusions - e.g. the minimal th-lemma placeholders
     `false = false` / `true = true` that the replay unit tests feed through the
     array dispatch, or a reflexive `l = l` - are proved directly and cheaply.
     This runs before the `is_array_goal` gate so such trivial goals still
     succeed even though they carry no array structure. *)
  fun trivial_prove t =
    if Term.aconv t boolSyntax.T then boolTheory.TRUTH
    else
      let val (l, r) = boolSyntax.dest_eq t
      in if Term.aconv l r then Thm.REFL l else raise ERR "trivial_prove" ""
      end

  fun array_prove t =
    trivial_prove t
    handle Feedback.HOL_ERR _ =>
    if is_array_goal t then
      Z3_ProformaThms.prove Z3_ProformaThms.array_thms t
      handle Feedback.HOL_ERR _ =>
      simp_prove_update t
      handle Feedback.HOL_ERR _ =>
      symbolic_index_prove t
      handle Feedback.HOL_ERR _ =>
      extensionality_prove t
      handle Feedback.HOL_ERR _ =>
      choice_extensionality_prove t
      handle Feedback.HOL_ERR _ =>
      (if has_update_comb t then metis_array_prove t else unsupported t)
      handle Feedback.HOL_ERR _ =>
      unsupported t
    else
      unsupported t

end
