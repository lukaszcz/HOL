(* Copyright (c) 2009-2011 Tjark Weber. All rights reserved. *)

(* Common auxiliary functions, tracing *)

structure Library =
struct

  structure Parse :> Parse =
  struct
    infixr $
    fun f $ x = f x
    open Parse
    val (Type,Term) = parse_from_grammars $ valOf $ grammarDB {thyname="words"}
  end

  (***************************************************************************)
  (* tracing                                                                 *)
  (***************************************************************************)

  (* possible values:
     0 - no output at all (except for fatal errors)
     1 - warnings only
     2 - also diagnostic messages of constant length
     3 - also diagnostic messages that are potentially lengthy (e.g., terms,
         models, proofs)
     4 - moreover, temporary files (for communication with the SMT solver) are
         not removed after solver invocation *)
  val trace = ref 2

  val _ = Feedback.register_trace ("HolSmtLib", trace, 4)

  (***************************************************************************)
  (* I/O, parsing                                                            *)
  (***************************************************************************)

  (* opens 'path' as an output text file; writes all elements of
     'strings' to this file (in the given order); closes the file *)
  fun write_strings_to_file path strings =
  let
    val outstream = TextIO.openOut path
  in
    List.app (TextIO.output o Lib.pair outstream) strings;
    TextIO.closeOut outstream
  end

  (* true if 'name' can be found on the current PATH *)
  fun command_available name =
    OS.Process.isSuccess
      (OS.Process.system ("command -v " ^ name ^ " > /dev/null 2>&1"))
    handle _ => false

  (***************************************************************************)
  (* solver versions                                                         *)
  (***************************************************************************)

  (* The `major.minor` series of a dotted version string, ignoring the patch
     level.  NONE when the string is not version-shaped at all, which is how
     the `<unknown>`/`<undiscoverable>` sentinels that stand in for a version
     that could not be discovered are told apart from a real one. *)
  fun version_series version =
    case String.tokens (fn c => c = #".") version of
      [] => NONE
    | major :: rest =>
      (case Int.fromString major of
         NONE => NONE
       | SOME major =>
         let
           val minor =
             case rest of
               minor :: _ => Option.getOpt (Int.fromString minor, 0)
             | [] => 0
         in
           SOME (major, minor)
         end)

  fun version_compare (version1, version2) =
    let
      fun components version =
        List.map (fn token => Option.getOpt (Int.fromString token, 0))
          (String.tokens (fn c => c = #".") version)
    in
      List.collate Int.compare (components version1, components version2)
    end

  val warned_solver_versions = ref ([] : string list)

  fun warn_solver_version key message =
    if List.exists (fn warned => warned = key) (!warned_solver_versions) then
      ()
    else
      (warned_solver_versions := key :: !warned_solver_versions;
       if !trace > 0 then
         Feedback.HOL_WARNING "Library" "resolve_solver_version" message
       else ())

  (* Resolves a configured solver version to the tested version whose proof
     dialect the rule registries should replay under.  A patch release does
     not change the dialect, so a version whose `major.minor` matches a tested
     one resolves to it silently.  Anything else warns once and still
     proceeds: an untested version replays under the nearest tested version,
     an undiscoverable one under the latest.  An unknown or untested solver is
     never by itself a reason to refuse replay. *)
  fun resolve_solver_version {solver : string, supported : string list,
                              version : string} =
    case supported of
      [] => version
    | first :: _ =>
      let
        val series_compare = Lib.pair_compare (Int.compare, Int.compare)
        fun later (version, best) =
          if version_compare (version, best) = GREATER then version else best
        val latest = List.foldl later first supported
        fun warn message = warn_solver_version (solver ^ "/" ^ version) message
      in
        case version_series version of
          NONE =>
            (warn ("the " ^ solver ^ " version could not be determined; " ^
                   "replaying proofs under the tested version " ^ latest);
             latest)
        | SOME series =>
          let
            (* Bracket `series` by the tested versions on either side of it.
               Minor numbers restart with each major, so they cannot be
               subtracted across majors; ordering is the only sound way to say
               which tested version a given one sits nearest to.  `side`
               selects the candidates on one side of `series`, and `prefer`
               picks whichever of them lies closest to it. *)
            fun nearest side prefer =
              List.foldl
                (fn (candidate, best) =>
                  case version_series candidate of
                    NONE => best
                  | SOME candidate_series =>
                    if side (series_compare (candidate_series, series)) then
                      case best of
                        NONE => SOME candidate
                      | SOME incumbent =>
                        if version_compare (candidate, incumbent) = prefer then
                          SOME candidate
                        else best
                    else best)
                NONE supported
            val below = nearest (fn order => order <> GREATER) GREATER
            val above = nearest (fn order => order <> LESS) LESS
            val resolved =
              case (below, above) of
                (SOME lower, SOME upper) =>
                  (* `series` is tested, or sits in a gap between two tested
                     versions; prefer the newer side of a gap. *)
                  if version_series lower = SOME series then lower
                  else if version_series upper = SOME series then upper
                  else upper
              | (SOME lower, NONE) => lower   (* newer than every tested one *)
              | (NONE, SOME upper) => upper   (* older than every tested one *)
              | (NONE, NONE) => latest
          in
            if version_series resolved = SOME series then
              resolved
            else
              (warn (solver ^ " version " ^ version ^ " is not among the " ^
                     "tested versions " ^ String.concatWith ", " supported ^
                     "; replaying proofs under the nearest of them, " ^
                     resolved);
               resolved)
          end
      end

  (* Takes a function that returns characters, returns a function that
     returns tokens. SMT-LIB 2 tokens are separated by whitespace (which is
     dropped) or parentheses (which are tokens themselves). Tokens are
     simply strings; we use no markup. *)
  fun get_token (get_char : unit -> char) : unit -> string =
  let
    val buffer = ref (NONE : string option)
    fun line_comment () =
      if get_char () = #"\n" then
        ()
      else line_comment ()
    fun aux_symbol cs c =
      if c = #"|" then
        (* we return |x| as x *)
        String.implode (List.rev cs)
      else
        aux_symbol (c :: cs) (get_char ())
    fun aux_string cs c =
      if c = #"\"" then
        (* we return "x" as x *)
        String.implode (List.rev cs)
      else if c = #"\\" then
        (* The only escape sequences in SMT-LIB are \" and \\. We simply drop
           the backslash. *)
        aux_string (get_char () :: cs) (get_char ())
      else
        aux_string (c :: cs) (get_char ())
    fun (* whitespace *)
        aux [] #" " = aux [] (get_char ())
      | aux [] #"\t" = aux [] (get_char ())
      | aux [] #"\n" = aux [] (get_char ())
      | aux [] #"\r" = aux [] (get_char ())
      | aux cs #" " = String.implode (List.rev cs)
      | aux cs #"\t" = String.implode (List.rev cs)
      | aux cs #"\n" = String.implode (List.rev cs)
      | aux cs #"\r" = String.implode (List.rev cs)
      (* parentheses *)
      | aux [] #"(" = "("
      | aux [] #")" = ")"
      | aux cs #"(" = (buffer := SOME "("; String.implode (List.rev cs))
      | aux cs #")" = (buffer := SOME ")"; String.implode (List.rev cs))
      (* | *)
      | aux [] #"|" = aux_symbol [] (get_char ())
      | aux _ #"|" =
        raise Feedback.mk_HOL_ERR "Library" "get_token" "invalid '|'"
      (* " *)
      | aux [] #"\"" = aux_string [] (get_char ())
      | aux _ #"\"" =
        raise Feedback.mk_HOL_ERR "Library" "get_token" "invalid '\"'"
      (* ; *)
      | aux [] #";" = (line_comment (); aux [] (get_char ()))
      | aux cs #";" = (line_comment (); String.implode (List.rev cs))
      (* everything else *)
      | aux cs c = aux (c :: cs) (get_char ())
          handle Feedback.HOL_ERR _ =>
            (* end of stream *)
            String.implode (List.rev (c :: cs))
  in
    fn () =>
      let
        val token = case !buffer of
            SOME token => (buffer := NONE; token)
          | NONE => aux [] (get_char ())
      in
        if !trace > 3 then
          Feedback.HOL_MESG ("HolSmtLib: next token is '" ^ token ^ "'")
        else ();
        token
      end
  end

  fun undo_look_ahead symbols get_token =
  let
    val buffer = ref symbols
    fun get_token' () =
      case !buffer of
        [] => get_token ()
      | x::xs => (buffer := xs; x)
  in
    get_token'
  end

  fun parse_arbnum (s : string) =
    let
      fun handle_err () =
        raise Feedback.mk_HOL_ERR "Library" "parse_arbnum"
          ("numeral expected, but '" ^ s ^ "' found")
    in
      Arbnum.fromString s
        (* Moscow ML's Arbnum implementation throws Option.Option on error,
           while Poly/ML's throws the Fail exception *)
        handle Option.Option => handle_err ()
             | Fail _ => handle_err ()
    end

  fun expect_token (expected : string) (actual : string) : unit =
    if expected = actual then
      ()
    else
      raise Feedback.mk_HOL_ERR "Library" "expect_token"
        ("'" ^ expected ^ "' expected, but '" ^ actual ^ "' found")

  (* extends a dictionary that maps keys to lists of values *)
  fun extend_dict ((key, value), dict) =
  let
    val values = Redblackmap.find (dict, key)
      handle Redblackmap.NotFound => []
  in
    Redblackmap.insert (dict, key, value :: values)
  end

  (* the same as `extend_dict`, but ensures the key did not contain any
     associated value in the dictionary prior to this call *)
  fun extend_dict_unique ((key, value), dict) =
  let
    val values = Redblackmap.find (dict, key)
      handle Redblackmap.NotFound => []
    val new_dict = Redblackmap.insert (dict, key, value :: values)
  in
    if not (List.null values) then
      raise Feedback.mk_HOL_ERR "Library" "extend_dict_unique"
          ("key '" ^ key ^ "' already contained a value")
    else
      new_dict
  end

  (* entries in 'dict2' are prepended to entries in 'dict1' *)
  fun union_dict dict1 dict2 = Redblackmap.foldl (fn (key, vals, dict) =>
    let
      val values = Redblackmap.find (dict1, key)
        handle Redblackmap.NotFound => []
    in
      Redblackmap.insert (dict, key, vals @ values)
    end) dict1 dict2

  (* creates a dictionary that maps strings to lists of parsing functions *)
  fun dict_from_list xs
      : (string, (string -> Term.term list -> 'a list -> 'a) list)
        Redblackmap.dict =
    List.foldl extend_dict (Redblackmap.mkDict String.compare) xs

  (***************************************************************************)
  (* auxiliary functions                                                     *)
  (***************************************************************************)

  (* Convert a term to a string, in such a way that terms with exponentially
     large term sizes can still be printed very quickly.

     This function is needed because Z3 can create terms which cause a
     combinatorial explosion in both the running time and the output size if
     they were to be printed out fully, and in fact the default HOL
     pretty-printers do suffer from apparent hangs when printing such terms.

     To prevent this from happening, this function temporarily sets
     `max_print_depth` so that sub-terms deeper than some value get abbreviated
     with the string "...", therefore preventing the full gigantic term tree
     from being traversed. It also removes non-trivial overloads, since some of
     them are also causing the pretty-printer to appear to hang when printing
     terms. *)
  fun term_to_string tm =
  let
    val grammar = Parse.term_grammar ()
    val simpler_grammar = term_grammar.clear_overloads grammar
  in
    Lib.with_flag(Globals.max_print_depth, 15)
      (Parse.term_to_string_by_grammar (Parse.type_grammar (), simpler_grammar))
        tm
  end

  (* the same as above, but print a theorem instead *)
  fun thm_to_string thm =
  let
    fun hyps_to_string hyps =
      String.concatWith ", " (List.map term_to_string hyps)
    val hyps_contents =
      if !Globals.show_assums then
        hyps_to_string (Thm.hyp thm)
      else
        "."
  in
    " [" ^ hyps_contents ^ "] |- " ^ term_to_string (Thm.concl thm)
  end

  (* srcname is only a label for Sanity's report; the caller supplies it
     because there need not be a current theory to name --- HolSmtLib
     probes the solvers as it loads, before any segment is open *)
  fun check_oracle_tags srcname name thm =
    if Sanity.check_tags ((srcname, name), thm) then
      raise Feedback.mk_HOL_ERR "HolSmtLib" "check_oracle_tags"
        ("solver '" ^ name ^ "' produced unexpected oracle/axiom tags: " ^
         thm_to_string thm)
    else
      ()

  (* `is_def_oriented` must return false when:
     1. `lhs` is not a variable in `var_set` but `rhs` is, or
     2. `lhs` and `rhs` are both variables in `var_set` but `rhs` is smaller
         than `lhs` (for some definition of "smaller").
     Otherwise, it must return true. *)
  fun is_def_oriented var_set (lhs, rhs) =
    (not (HOLset.member (var_set, rhs))) orelse
      (HOLset.member (var_set, lhs) andalso
        Term.var_compare (rhs, lhs) <> LESS)

  (* Orient a definition of the form `lhs = rhs` into `rhs = lhs`, if necessary.
     This is used to ensure that the `lhs` is a variable in `var_set`. Also, if
     both the `lhs` and the `rhs` are variables in `var_set`, then the `rhs`
     must not be "smaller" than the `lhs`. This is done to avoid ending up with
     circular definitions after they are all aggregated into the final theorem,
     i.e. we want to avoid ending up with both `var1 = var2` and `var2 = var1`. *)
  fun orient_def var_set (lhs, rhs) =
    if is_def_oriented var_set (lhs, rhs) then
      (lhs, rhs)
    else
      (rhs, lhs)

  (***************************************************************************)
  (* Derived rules                                                           *)
  (***************************************************************************)

  (* A |- ... /\ t /\ ...
     --------------------
            A |- t        *)
  fun conj_elim (thm, t) =
  let
    fun elim conj =
      if Term.aconv t conj then
        Lib.I
      else
        let
          val (l, r) = boolSyntax.dest_conj conj
        in
          elim l o Thm.CONJUNCT1
            handle Feedback.HOL_ERR _ =>
              elim r o Thm.CONJUNCT2
        end
  in
    elim (Thm.concl thm) thm
  end

  (*        A |- t
     --------------------
     A |- ... \/ t \/ ... *)
  fun disj_intro (thm, disj) =
    if Term.aconv (Thm.concl thm) disj then
      thm
    else
      let
        val (l, r) = boolSyntax.dest_disj disj
      in
        Thm.DISJ1 (disj_intro (thm, l)) r
          handle Feedback.HOL_ERR _ =>
            Thm.DISJ2 l (disj_intro (thm, r))
      end

  (* auxiliary function: fails unless 's' is a subterm of 't' with
     respect to 'destfn' *)
  fun check_subterm destfn s t =
    if Term.aconv s t then
      ()
    else
      let
        val (l, r) = destfn t
      in
        check_subterm destfn s l
          handle Feedback.HOL_ERR _ =>
            check_subterm destfn s r
      end

  (* |- ... \/ t \/ ... \/ ~t \/ ... *)
  fun gen_excluded_middle disj =
  let
    val (pos, neg) = Lib.tryfind (fn neg =>
      let
        val pos = boolSyntax.dest_neg neg
        val _ = check_subterm boolSyntax.dest_disj pos disj
      in
        (pos, neg)
      end) (boolSyntax.strip_disj disj)
    val th1 = disj_intro (Thm.ASSUME pos, disj)
    val th2 = disj_intro (Thm.ASSUME neg, disj)
  in
    Thm.DISJ_CASES (Thm.SPEC pos boolTheory.EXCLUDED_MIDDLE) th1 th2
  end

  (* A |- ... /\ t /\ ... /\ ~t /\ ...
     ---------------------------------
                  A |- F               *)
  fun gen_contradiction thm =
  let
    val (pos, neg) = Lib.tryfind (fn neg =>
      let
        val pos = boolSyntax.dest_neg neg
        val _ = check_subterm boolSyntax.dest_conj pos (Thm.concl thm)
      in
        (pos, neg)
      end) (boolSyntax.strip_conj (Thm.concl thm))
    val th1 = conj_elim (thm, pos)
    val th2 = conj_elim (thm, neg)
  in
    Thm.MP (Thm.NOT_ELIM th2) th1
  end

  (* Given two terms ``lhs`` and ``rhs``, find an instantiation of free
     variables such that a theorem with the conclusion ``lhs = rhs`` can be
     returned. The instantiations become hypotheses of the returned theorem.
     e.g.:

     gen_instantiation (``x+1+z2``, ``z1+2``, {``z1``, ``z2``, ``z3``})
     returns the theorem:

     { z1 = x+1, z2 = 2 } |- x+1+z2 = z1+2

     In cases where we end up with an hypothesis of the form `var1 = var2`,
     we might orient the hypothesis to become `var2 = var1` to make sure that
     the left-hand side is a variable in `var_set`. If both `var1` and `var2`
     are in `var_set`, then we make sure that the left-hand side contains the
     "smaller" variable. This avoids creating circular definitions across
     multiple calls of this function (i.e. one call instantiating `z1 = z2`
     and another instantiating `z2 = z1`). *)
  fun gen_instantiation (lhs, rhs, var_set) =
  let
    val substs = Unify.simp_unify_terms [] lhs rhs
    fun orient {redex, residue} = orient_def var_set (redex, residue)
    val oriented_substs = List.map orient substs
    val asl = List.map boolSyntax.mk_eq oriented_substs
    val thms = List.map Thm.ASSUME asl
    val concl = boolSyntax.mk_eq (lhs, rhs)
  in
    Tactical.TAC_PROOF ((asl, concl), Tactical.THEN (Tactic.SUBST_TAC thms,
      Tactic.REFL_TAC))
  end

  (* Prove ``left = right`` where the two sides are related by `conv` (up to
     alpha-equivalence).  `conv` is applied to whichever side changes; the
     result is aligned to the other side with `Thm.ALPHA`, retrying in the
     reverse direction (via `Thm.SYM`) if the forward one fails.  `name`
     labels the error raised when `conv` leaves its input unchanged. *)
  fun conversion_equal name conv (left, right) =
  let
    fun forward (source, expected) =
      let
        val theorem = conv source
          handle Conv.UNCHANGED =>
            raise Feedback.mk_HOL_ERR "Library" name
              "conversion made no change"
        val normalized = Lib.snd (boolSyntax.dest_eq (Thm.concl theorem))
      in
        Thm.TRANS theorem (Thm.ALPHA normalized expected)
      end
  in
    forward (left, right)
    handle Feedback.HOL_ERR _ => Thm.SYM (forward (right, left))
  end

  (***************************************************************************)
  (* Tactics                                                                 *)
  (***************************************************************************)

  (* A tactic that unfolds operations of set theory, replacing them by
     propositional logic (representing sets as predicates). *)
  val SET_SIMP_TAC =
  let
    val thms = [pred_setTheory.SPECIFICATION, pred_setTheory.GSPEC_ETA,
      pred_setTheory.EMPTY_DEF, pred_setTheory.UNIV_DEF,
      pred_setTheory.UNION_DEF, pred_setTheory.INTER_DEF]
  in
    simpLib.SIMP_TAC (simpLib.mk_simpset [pred_setSimps.SET_SPEC_ss]) thms
  end

  (* A tactic that unfolds LET. *)
  val LET_SIMP_TAC =
    simpLib.SIMP_TAC (simpLib.mk_simpset [boolSimps.LET_ss]) []

  (* A tactic that simplifies certain word expressions. *)

  val TO_WORD_EXTRACT = boolLib.TAC_PROOF(([],
        “(!w : 'a word.
            dimindex(:'b) < dimindex(:'a) ==>
            (w2w w : 'b word = (dimindex(:'b) - 1 >< 0) w)) /\
         (!w : 'a word.
            dimindex(:'b) < dimindex(:'a) ==>
            (sw2sw w : 'b word = (dimindex(:'b) - 1 >< 0) w))”),
        BasicProvers.SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [])

  val WORD_BIT_EXTRACT = simpLib.SIMP_PROVE
        (simpLib.++(bossLib.std_ss, wordsLib.WORD_BIT_EQ_ss))
        [wordsLib.WORD_DECIDE “1w :word1 ' 0”]
        “!w:'a word i. i < dimindex (:'a) ==> (w ' i = ((i >< i) w = 1w:word1))”

  val WORD_SHIFT_BV = simpLib.SIMP_PROVE bossLib.bool_ss
        [wordsTheory.word_shift_bv]
       “(!w:'a word n. n < dimword (:'a) ==> (w << n = w <<~ n2w n)) /\
        (!w:'a word n. n < dimword (:'a) ==> (w >> n = w >>~ n2w n)) /\
        (!w:'a word n. n < dimword (:'a) ==> (w >>> n = w >>>~ n2w n))”

  val bit_field_insert_rwt = simpLib.SIMP_RULE
        (simpLib.++(bossLib.bool_ss, boolSimps.LET_ss)) [] wordsTheory.bit_field_insert;

  val WORD_SIMP_TAC = let
    open Tactical Conv Tactic wordsTheory simpLib
  in
    CONV_TAC (DEPTH_CONV wordsLib.EXPAND_REDUCE_CONV) THEN
      SIMP_TAC (pureSimps.pure_ss ++ numSimps.REDUCE_ss ++ wordsLib.SIZES_ss)
        [word_rol_bv_def, word_ror_bv_def,
         w2n_n2w, word_bit_def, bit_field_insert_rwt,
         word_lsb_def, word_msb_def,
         WORD_SLICE_THM, WORD_BITS_EXTRACT,
         WORD_BIT_EXTRACT, WORD_SHIFT_BV, TO_WORD_EXTRACT] THEN
      CONV_TAC (DEPTH_CONV wordsLib.EXTEND_EXTRACT_CONV)
  end

(*
  val WORD_SIMP_TAC =
    simpLib.SIMP_TAC (simpLib.++ (bossLib.pure_ss, wordsLib.WORD_ss))
      [wordsTheory.EXTRACT_ALL_BITS, wordsTheory.WORD_EXTRACT_ZERO,
      wordsTheory.LSL_LIMIT, wordsTheory.LSR_LIMIT]
*)

  (***************************************************************************)
  (* term / type structure helpers                                           *)
  (* (shared by the SMT-LIB translator, the logic-fragment checker, and Z3   *)
  (*  proof replay)                                                          *)
  (***************************************************************************)

  (* does 'ty', or any of its domain/range components, satisfy 'pred'? *)
  fun type_contains pred ty =
    pred ty orelse
    (let val (dom, rng) = Type.dom_rng ty
     in type_contains pred dom orelse type_contains pred rng end
     handle Feedback.HOL_ERR _ => false)

  fun type_contains_int ty =
    type_contains (fn ty => Type.compare (ty, intSyntax.int_ty) = EQUAL) ty

  fun type_contains_real ty =
    type_contains (fn ty => Type.compare (ty, realSyntax.real_ty) = EQUAL) ty

  fun type_contains_word ty =
    type_contains (Lib.can wordsSyntax.dest_word_type) ty

  (* Outbound HOL strings retain their native char-list representation. *)
  fun type_contains_native_string ty =
    type_contains (fn ty => Type.compare (ty, stringSyntax.string_ty) = EQUAL)
      ty

  (* Inbound SMT-LIB String is the smtstringTheory num-list representation. *)
  val smt_string_ty = listSyntax.mk_list_type numSyntax.num

  fun type_contains_string ty =
    type_contains
      (fn candidate => Type.compare (candidate, smt_string_ty) = EQUAL)
      ty

  (* 'tm' is exactly the constant 'c' (same name and theory) *)
  fun same_const c tm = Term.is_const tm andalso Term.same_const tm c

  (* every subterm of 'tm' (including 'tm' itself), in pre-order; threading an
     accumulator keeps the walk linear rather than quadratic in the size of
     the application spine *)
  fun subterms tm =
    let
      fun walk (tm, acc) =
        tm ::
        (let val (rator, rand) = Term.dest_comb tm
         in walk (rator, walk (rand, acc)) end
         handle Feedback.HOL_ERR _ =>
           (let val (_, body) = Term.dest_abs tm
            in walk (body, acc) end
            handle Feedback.HOL_ERR _ => acc))
    in
      walk (tm, [])
    end

  fun has_quantifier tm =
    boolSyntax.is_forall tm orelse boolSyntax.is_exists tm orelse
    (let val (rator, rand) = Term.dest_comb tm
     in has_quantifier rator orelse has_quantifier rand end
     handle Feedback.HOL_ERR _ =>
       (let val (_, body) = Term.dest_abs tm
        in has_quantifier body end
        handle Feedback.HOL_ERR _ => false))

  (***************************************************************************)
  (* nonlinear arithmetic detection and proving                              *)
  (***************************************************************************)

  (* Is 'tm' a numeric literal (numeral, int literal, or real literal)? *)
  fun is_numeric_literal tm =
    numSyntax.is_numeral tm orelse
    intSyntax.is_int_literal tm orelse
    (realSyntax.is_real_literal tm
     handle Feedback.HOL_ERR _ => false)

  (* Does 'tm' contain a nonlinear arithmetic subterm?
     A subterm is nonlinear if it is a multiplication of two non-literal
     terms, or an exponentiation/power with exponent > 1. *)
  fun is_nonlinear tm =
  let
    fun is_nl_mult dest_mult t =
      (let val (l, r) = dest_mult t
       in not (is_numeric_literal l) andalso not (is_numeric_literal r) end)
      handle Feedback.HOL_ERR _ => false
    fun check t =
      is_nl_mult realSyntax.dest_mult t orelse
      is_nl_mult intSyntax.dest_mult t orelse
      is_nl_mult numSyntax.dest_mult t
    fun walk t =
      check t orelse
      (let val (f, x) = Term.dest_comb t
       in walk f orelse walk x end
       handle Feedback.HOL_ERR _ => false)
  in
    walk tm
  end

  (* e.g., "(A --> B) --> C --> D" acc  ==>  [A, B, C, D] @ acc *)
  fun strip_fun_tys ty acc =
    let val (dom, rng) = Type.dom_rng ty
    in strip_fun_tys dom (strip_fun_tys rng acc) end
    handle Feedback.HOL_ERR _ => ty :: acc

  (* approximate: does term contain real type? *)
  fun term_contains_real_ty tm =
    let val (rator, rand) = Term.dest_comb tm
    in term_contains_real_ty rator orelse term_contains_real_ty rand end
    handle Feedback.HOL_ERR _ =>
      List.exists (Lib.equal realSyntax.real_ty)
        (strip_fun_tys (Term.type_of tm) [])

  val csdp_missing_diagnostic =
    "nonlinear real arithmetic replay requires the CSDP semidefinite solver " ^
    "(`coinor-csdp`, or `HOL4_CSDP_EXECUTABLE`); " ^
    "CSDP executable not found"

  fun raise_csdp_missing () =
    raise Feedback.mk_HOL_ERR "Library" "nla_prove" csdp_missing_diagnostic

  fun env_csdp_missing () =
    case OS.Process.getEnv "HOL4_CSDP_EXECUTABLE" of
        SOME path =>
          String.isSubstring "/" path andalso
          (not (OS.FileSys.access (path, [OS.FileSys.A_EXEC]))
           handle OS.SysErr _ => true)
      | NONE => false

  fun wrap_csdp_missing f x =
    if env_csdp_missing () then raise_csdp_missing ()
    else
      f x
      handle Feedback.HOL_ERR holerr =>
        if String.isSubstring "CSDP not found" (Feedback.message_of holerr)
        then raise_csdp_missing ()
        else raise Feedback.HOL_ERR holerr

  (* Prove a nonlinear arithmetic goal using NLArith/SOSLib.
     Type-dispatches: real → REAL_NLA then REAL_SOS, int → INT_SOS,
     num → NUM_SOS_RULE.  Avoids trying wrong-type provers. *)
  fun nla_prove tm =
    if term_contains_real_ty tm then
      NLArith.REAL_NLA tm
      handle Feedback.HOL_ERR _ =>
      (* REAL_NLA can't handle strict ineqs with equality preconditions;
         REAL_SOS (which uses CSDP) can. *)
      wrap_csdp_missing SOSLib.REAL_SOS tm
    else
      wrap_csdp_missing SOSLib.INT_SOS tm
      handle Feedback.HOL_ERR _ =>
      wrap_csdp_missing SOSLib.NUM_SOS_RULE tm

  (* Polynomial arithmetic should treat conditional branches as opaque atoms;
     splitting them first is both unnecessary and potentially exponential. *)
  fun arith_prove_raw tm =
    Tactical.TAC_PROOF (([], tm), intLib.INT_RING_TAC)
    handle Feedback.HOL_ERR _ =>
    intLib.ARITH_PROVE tm
    handle Feedback.HOL_ERR _ =>
    RealField.REAL_ARITH tm
    handle Feedback.HOL_ERR _ =>
    raise Feedback.mk_HOL_ERR "Library" "arith_prove_raw"
      ("failed: " ^ term_to_string tm)

  fun contains_conditional tm =
    List.exists (Lib.can boolSyntax.dest_cond) (subterms tm)

  (* cvc5 and Z3 may lower MIN/MAX or natural subtraction to conditionals.
     Normalize just that shape before arithmetic, rather than broadening the
     ordinary arithmetic path to case-split every goal. *)
  fun arith_prove_conditional tm =
    if not (contains_conditional tm) then
      raise Feedback.mk_HOL_ERR "Library" "arith_prove_conditional"
        "no conditional arithmetic subterm"
    else
      let
        val tm_eq_tm' =
          simpLib.SIMP_CONV (bossLib.srw_ss())
            [boolTheory.COND_EXPAND, boolTheory.COND_RAND,
             boolTheory.COND_RATOR, arithmeticTheory.MIN_DEF,
             arithmeticTheory.MAX_DEF, integerTheory.INT_MIN,
             integerTheory.INT_MAX, realTheory.min_def, realTheory.max_def] tm
          handle Conv.UNCHANGED => Thm.REFL tm
        val tm' = boolSyntax.rhs (Thm.concl tm_eq_tm')
      in
        if Term.aconv tm tm' then
          raise Feedback.mk_HOL_ERR "Library" "arith_prove_conditional"
            "conditional normalization made no progress"
        else
          Thm.EQ_MP (Thm.SYM tm_eq_tm') (arith_prove_raw tm')
      end

  fun arith_prove_with_cases tm =
    arith_prove_raw tm
    handle Feedback.HOL_ERR _ =>
    arith_prove_conditional tm
    handle Feedback.HOL_ERR _ =>
    if is_nonlinear tm then nla_prove tm
    else raise Feedback.mk_HOL_ERR "Library" "arith_prove_with_cases"
      ("failed: " ^ term_to_string tm)

  fun NLA_TAC (goal as (_, term)) =
    if term_contains_real_ty term then
      NLArith.NLA_TAC goal
      handle Feedback.HOL_ERR _ =>
      SOSLib.REAL_SOS_TAC goal
    else
      SOSLib.INT_SOS_TAC goal
      handle Feedback.HOL_ERR _ =>
      SOSLib.NUM_SOS_RULE_TAC goal

end
