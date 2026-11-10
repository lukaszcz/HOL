(* Copyright (c) 2009-2011 Tjark Weber. All rights reserved. *)

(* Common auxiliary functions, tracing *)

structure Library =
struct

  open SmtReplayGraph SmtReplayUnify SmtReplayResolve
       SmtReplayProof SmtReplayUnifyPlan SmtReplayUnifyBinder
  structure ReplayG = SmtReplayGraph
  structure ReplayU = SmtReplayUnify
  structure ReplayR = SmtReplayResolve
  structure ReplayP = SmtReplayProof
  structure ReplayN = SmtReplayUnifyPlan
  structure ReplayB = SmtReplayUnifyBinder

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

  (* HolSmt's replay support contains a handful of precomputed theorems.
     They are built while the library is loaded, which can happen before a
     client has opened a theory (notably when running the HolSmt selftests).
     Give those declaration-time proofs an explicit, otherwise unchanged
     context.  Keeping the trace bracket here also prevents an implementation
     detail of the checked replay path from leaking into a client's transcript.
     Calls made while a theory is active retain that theory in the snapshot. *)
  fun proof_context () =
    let
      val ctxt = Context.snapshot ()
    in
      case Context.current_thy ctxt of
        SOME _ => ctxt
      | NONE =>
          (Thm.setCT "HolSmtLib";
           let val proof_ctxt = Context.snapshot ()
           in
             Context.restore ctxt;
             proof_ctxt
           end)
    end

  fun prove (tm, tac) =
    Feedback.with_traces
      [("metis", 0), ("ambient context inside proof", 0)]
      (fn () => Feedback.quiet_messages
        (fn () => Tactical.prove_in (proof_context ()) (tm, tac)) ()) ()

  (* Ordinary blastLib deliberately retains its upstream sparse-multiply
     converter. Its arithmetic normal form need not have a dense literal as
     the exact left endpoint (notably the all-ones coefficient). Normalize
     this ring identity explicitly in replay, before that converter runs.
     The equality is kernel checked; no word proposition is assumed true.
     Callers retain their existing source-size and step-time envelopes. *)
  fun replay_minus_one_mul_conv target =
    let
      val (coefficient, _) = wordsSyntax.dest_word_mul target
      val (value, width) = wordsSyntax.dest_mod_word_literal coefficient
      val successor = Arbnum.+ (value, Arbnum.one)
      (* Do not allocate 2^width merely to reject a small coefficient at
         an enormous word Type. A possible power is bounded by the actual
         coefficient's binary size before it is constructed. *)
      val _ =
        if Arbnum.log2 successor = width andalso
             successor = Arbnum.pow (Arbnum.two, width) then ()
        else raise Conv.UNCHANGED
      val one = wordsSyntax.mk_n2w
        (numSyntax.term_of_int 1, wordsSyntax.dim_of coefficient)
      val minus_one = wordsSyntax.mk_word_2comp one
      val equality = Drule.EQT_ELIM (wordsLib.WORD_EVAL_CONV
        (boolSyntax.mk_eq (coefficient, minus_one)))
      val normalized = Conv.LAND_CONV (fn _ => equality) target
      val reduced = Conv.REWR_CONV
        (Conv.GSYM wordsTheory.WORD_NEG_MUL)
        (boolSyntax.rhs (Thm.concl normalized))
    in
      Thm.TRANS (Thm.REFL target) (Thm.TRANS normalized reduced)
    end

  val replay_word_normalize_conv =
    Conv.QCONV (Conv.DEPTH_CONV replay_minus_one_mul_conv)

  val replay_word_simp_conv =
    Conv.THENC (replay_word_normalize_conv, blastLib.WORD_SIMP_CONV)

  fun replay_bblast_prove target =
    let
      val normalization = replay_word_normalize_conv target
      val theorem = blastLib.BBLAST_PROVE
        (boolSyntax.rhs (Thm.concl normalization))
    in
      Thm.EQ_MP (Thm.SYM normalization) theorem
    end

  (* Permanent coverage-ablation switch.  Replay fast paths consult this
     single predicate; complete rule procedures remain enabled. *)
  fun no_fastpath () =
    OS.Process.getEnv "HOL4_HOLSMT_NO_FASTPATH" = SOME "1"

  fun fastpath_refusal component reason =
    raise Feedback.mk_HOL_ERR "Library" "require_fastpath"
      ("fast path refused: " ^ reason ^ "; component=" ^ component)

  fun is_fastpath_refusal holerr =
    Feedback.top_structure_of holerr = "Library" andalso
    Feedback.top_function_of holerr = "require_fastpath" andalso
    String.isPrefix "fast path refused: " (Feedback.message_of holerr)

  (* A redundant route must never receive a larger resource envelope than
     the complete checked-replay rung behind it.  Use that rung's existing
     tree-node and step-time measures rather than a width/corpus threshold.
     Refusal is deliberately an ordinary HOL_ERR: the enclosing ladder must
     continue to its complete procedure.  Exceptions raised by [fastpath]
     itself are not caught or relabelled. *)
  local
    datatype 'a fastpath_result =
        FastpathSuccess of 'a
      | FastpathWorkerTimeout of exn
  in
  fun require_fastpath component target fastpath input =
    if no_fastpath () then
      fastpath_refusal component
        "disabled by HOL4_HOLSMT_NO_FASTPATH=1"
    else
      let
        val limit = SmtResource.max_bitblast_term_nodes
        val observed = SmtResource.term_nodes_up_to limit target
        val () =
          if observed <= limit then ()
          else fastpath_refusal component
            ("term-size observed=" ^ Int.toString observed ^
             " maximum=" ^ Int.toString limit)
      in
        case (Timeout.apply SmtResource.max_bitblast_step_time
            (fn input =>
               FastpathSuccess (fastpath input)
               handle timeout as Timeout.TIMEOUT _ =>
                 FastpathWorkerTimeout timeout)
            input
          handle Timeout.TIMEOUT _ =>
            fastpath_refusal component
              ("step-time maximum=" ^
               LargeInt.toString
                 (Time.toSeconds SmtResource.max_bitblast_step_time) ^
               " s")) of
          FastpathSuccess result => result
        | FastpathWorkerTimeout timeout => raise timeout
      end
  end

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

  (* Checked solver replay may use theorems loaded from a theory file, whose
     unavoidable HOL4 tag is DISK_THM.  It may not use any other oracle or
     any axiom.  In particular, do not delegate this security boundary to
     Sanity.check_tags: its accepted-oracle and accepted-axiom lists are
     mutable process-wide policy. *)
  fun check_oracle_tags _ name thm =
    let
      val (oracles, axioms) = Tag.dest_tag (Thm.tag thm)
      val unexpected_oracles =
        List.filter (fn oracle => oracle <> "DISK_THM") oracles
      fun tags_to_string tags =
        "[" ^ String.concatWith ", " tags ^ "]"
    in
      if null unexpected_oracles andalso null axioms then
        ()
      else
        raise Feedback.mk_HOL_ERR "HolSmtLib" "check_oracle_tags"
          ("solver '" ^ name ^
           "' produced unexpected oracle/axiom tags; oracles=" ^
           tags_to_string unexpected_oracles ^ "; axioms=" ^
           tags_to_string axioms ^ "; theorem: " ^ thm_to_string thm)
    end

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
     i.e. avoid both `var1 = var2` and `var2 = var1`. *)
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
  local
  datatype graph_instantiation = Instantiation of ReplayN.plan
    | InstantiationDeclined of string * bool
  fun graph_instantiation_with_normalizer graph normalizer extra_binders
      discover_binder
      {scope,flexible,lhs,rhs,seed,binders} =
    let
      fun failure ReplayU.TypeMismatch = ("type mismatch",false)
        | failure ReplayU.RigidMismatch = ("rigid mismatch",false)
        | failure ReplayU.OccursCheck = ("occurs check",false)
        | failure ReplayU.NeedsBinderAdmission = ("binder admission",true)
        | failure ReplayU.EscapingScope = ("scope escape",false)
      fun run equations = ReplayU.unify_with_binders graph discover_binder
        {scope = scope,flexible = flexible,equations = equations,
         binders = binders @ extra_binders ()}
      val initial = List.map (fn {variable,residue} => (variable,residue))
        (seed : ReplayU.assignment list)
    in case run (initial @ [(lhs,rhs)]) of
        ReplayU.NoMatch reason => InstantiationDeclined (failure reason)
      | ReplayU.Unified result =>
        let val assignments = ReplayU.assignments result in
          if List.null assignments then
            Instantiation (ReplayN.discover graph scope result)
          else case ReplayR.prepare_using graph scope normalizer
              {flexible = flexible,assignments = assignments,
               roots = List.map #residue assignments,preserved = []} of
              ReplayR.Refused ReplayR.NeedsBinderAdmission =>
                InstantiationDeclined ("binder admission",true)
            | ReplayR.Refused _ =>
                raise Feedback.mk_HOL_ERR "Library" "graph_instantiation"
                  "successful unifier has an invalid assignment dependency"
            | ReplayR.Resolved resolution =>
              let
                (* Preserve the legacy flat definition hypotheses. Alias
                   chains would change Z3's early/deferred rung selection. *)
                val normalized = List.map (fn {variable,residue} =>
                  (variable,ReplayR.node resolution residue)) assignments
              in case run (normalized @ [(lhs,rhs)]) of
                  ReplayU.NoMatch _ =>
                    raise Feedback.mk_HOL_ERR "Library" "graph_instantiation"
                      "normalized assignments lost a checked match"
                | ReplayU.Unified result =>
                    Instantiation (ReplayN.discover graph scope result)
              end
        end
    end
  fun graph_instantiation_using graph input =
    graph_instantiation_with_normalizer graph (fn _ => NONE)
      (fn () => []) (fn _ => NONE) input
  fun graph_instantiation graph {scope,flexible,lhs,rhs} =
    graph_instantiation_using graph {scope = scope,flexible = flexible,
      lhs = lhs,rhs = rhs,seed = [],binders = []}

  fun instantiation_declined reason =
    raise Feedback.mk_HOL_ERR "Library" "gen_instantiation"
      ("simp_unify_terms rejected protected goal variables: " ^
       "graph match declined: " ^ reason)

  in
  (* Production graph entry point retains obligations and compact proofs.
     The caller owns graph import and any local binder admission. *)
  fun graph_gen_instantiation graph input =
    case graph_instantiation graph input of Instantiation plan => plan
      | InstantiationDeclined (reason,_) => instantiation_declined reason
  fun graph_gen_instantiation_using graph input =
    case graph_instantiation_using graph input of Instantiation plan => plan
      | InstantiationDeclined (reason,_) => instantiation_declined reason

  fun gen_instantiation (lhs,rhs,var_set) =
    let
      val graph = ReplayG.new ()
      val root = ReplayG.root_scope graph
      val variables = HOLset.listItems var_set
      val flexible = List.map
        (ReplayG.variable graph root ReplayG.SolverFlexible) variables
      val scope = ReplayG.new_scope graph root
        (ListPair.zip (variables,flexible))
      (* This legacy helper never had a generic input quota. Its public
         adapter memoizes exposed DAG nodes and imposes no new tree cutoff. *)
      val maximum = case Int.maxInt of SOME maximum => maximum
        | NONE => 1073741823
      val left = ReplayG.import graph scope maximum lhs
      val right = ReplayG.import graph scope maximum rhs
      fun assemble plan relations raw left right =
        let
          val obligations = ReplayN.obligations plan
          val binders = ReplayN.binder_relations plan
          val definitions = List.map
            (fn {assignment = {variable,residue},equation} =>
              {variable = variable,residue = residue,equation = equation})
            obligations
          fun local_proof (needed : ReplayN.binder_relation) =
            let
              val relation = case List.find (fn relation =>
                  ReplayB.left relation = #left needed andalso
                  ReplayB.right relation = #right needed) relations of
                    SOME relation => relation
                  | NONE => raise Fail "missing bounded binder relation"
              val proof = ReplayB.prove graph scope relation definitions
              val target = ReplayG.representative graph (#equation needed)
            in Thm.EQ_MP (Thm.ALPHA (Thm.concl proof) target) proof end
          fun general () =
            let
              val sources = List.map #equation obligations @
                List.map #equation binders
              val block = ReplayP.freeze graph
                {scope = scope,roots = ReplayN.roots plan,
                 sources = sources,template_limit = maximum}
              val (_,indices) = List.foldl (fn (equation,(index,table)) =>
                (index+1,Redblackmap.insert
                  (table,ReplayG.node_id equation,index)))
                (0,Redblackmap.mkDict Int.compare) sources
              fun witness (obligation : ReplayN.obligation) =
                ReplayP.source block (Redblackmap.find
                  (indices,ReplayG.node_id (#equation obligation)))
              fun binder_witness (relation : ReplayN.binder_relation) =
                ReplayP.source block (Redblackmap.find
                  (indices,ReplayG.node_id (#equation relation)))
              val proofs = List.foldl (fn (relation,table) =>
                Redblackmap.insert (table,ReplayG.node_id (#equation relation),
                  local_proof relation))
                (Redblackmap.mkDict Int.compare) binders
              val edges = ReplayN.assemble_with_relations block plan
                {assignment = witness,binder = binder_witness}
              val target = #target (List.last (ReplayN.equations plan))
            in if List.null binders then
                ReplayP.realize block target (List.last edges)
              else ReplayP.realize_with_sources block target (List.last edges)
                (fn (_,node) => Redblackmap.peek (proofs,ReplayG.node_id node))
            end
          val theorem = if raw then ReplayN.realize_local plan
              {assignment = fn {equation,...} =>
                 Thm.ASSUME (ReplayG.representative graph equation),
               binder = local_proof}
            else general ()
        in Thm.TRANS left (Thm.TRANS theorem (Thm.SYM right)) end
      val binder_limit = SmtResource.max_bv_replay_term_nodes
      fun binder_admission action = action ()
        handle Feedback.HOL_ERR error =>
          if Feedback.top_structure_of error = "SmtReplayUnifyBinder" andalso
             Feedback.top_function_of error = "admission" then
            (SmtResource.check_term_size_for
              "BitVector" "binder-opening" (binder_limit+1);
             raise Feedback.HOL_ERR error)
          else raise Feedback.HOL_ERR error
      fun graph_attempt (left : ReplayG.source) (right : ReplayG.source) =
        let
          val relations = ref []
          val normalized = ref []
          val raw_needed = ref false
          fun pair left right = if ReplayG.node_id left <
              ReplayG.node_id right then
                (ReplayG.node_id left,ReplayG.node_id right)
            else (ReplayG.node_id right,ReplayG.node_id left)
          fun compare ((a,b),(c,d)) = case Int.compare (a,c) of
              EQUAL => Int.compare (b,d) | order => order
          val aligned = ref NONE
          fun aligned_pairs () = case !aligned of SOME pairs => pairs
            | NONE =>
              let
                val visited = ref (Redblackset.empty compare)
                fun visit left right =
                  let val key = pair left right in
                    if Redblackset.member (!visited,key) then () else
                    (visited := Redblackset.add (!visited,key);
                     case (ReplayG.view graph left,ReplayG.view graph right) of
                         (ReplayG.Application (lf,lx),
                          ReplayG.Application (rf,rx)) =>
                           (visit lf rf;visit lx rx)
                       | _ => ())
                  end
                val _ = visit (#node left) (#node right)
                val _ = aligned := SOME (!visited)
              in !visited end
          (* Preserve the old fallback's call-site Type policy. Aligned
             binders retain their existing stricter internal-Type admission;
             newly demanded pairs had only whole-input result-Type admission.
             Both paths bound every native binder operand/residue/output. *)
          fun result_types () =
            let
              fun visit [] _ = ()
                | visit (ty::rest) count =
                    if count >= binder_limit then
                      SmtResource.check_term_size_for "BitVector"
                        "binder-opening" (binder_limit+1)
                    else visit ((if Type.is_vartype ty then [] else
                      #2 (Type.dest_type ty)) @ rest) (count+1)
            in List.app (fn term => visit [Term.type_of term] 0) [lhs,rhs] end
          fun legacy_decline () =
            (List.app (fn term =>
               case SmtReplayImport.bounded_raw_size binder_limit term of
                   SOME _ => ()
                 | NONE => SmtResource.check_term_size_for "BitVector"
                     "binder-opening" (binder_limit+1)) [lhs,rhs];
             result_types ();
             instantiation_declined "bounded binder mismatch")
          fun discover (left,right) = binder_admission (fn () =>
            let
              val strict = Redblackset.member (aligned_pairs (),pair left right)
              val _ = if strict then ()
                else (result_types ();raw_needed := true)
              val discover = if strict then ReplayB.discover
                else ReplayB.discover_raw
            in case discover graph scope
                {left = left,right = right,flexible = flexible,
                 limit = binder_limit} of
                SOME relation =>
                  (relations := relation :: !relations;
                   SOME (ReplayB.assignments relation))
              | NONE => if strict then
                  instantiation_declined "bounded binder mismatch"
                else legacy_decline ()
            end)
          fun normalize {node,resolve} = binder_admission (fn () =>
            let val normalize = if !raw_needed then ReplayB.normalize_raw
                  else ReplayB.normalize
                val (result,relation) = normalize graph scope
                  {node = node,resolve = resolve,limit = binder_limit}
                val _ = normalized := relation :: !normalized
            in SOME result end)
          fun extra_binders () = List.map (fn relation =>
            (ReplayB.left relation,ReplayB.right relation))
            (!relations @ !normalized)
        in case graph_instantiation_with_normalizer graph normalize
            extra_binders discover
            {scope = scope,flexible = flexible,
             lhs = #node left,rhs = #node right,seed = [],binders = []}
          of Instantiation plan => SOME
               (assemble plan (!relations @ !normalized) (!raw_needed)
                 (#bridge left) (#bridge right))
           | InstantiationDeclined (reason,false) =>
               if !raw_needed then legacy_decline ()
               else instantiation_declined reason
           | InstantiationDeclined (_,true) => NONE
        end
      fun admit_nodes (left : ReplayG.source) (right : ReplayG.source) =
        binder_admission (fn () =>
          (ReplayB.admit graph binder_limit left,
           ReplayB.admit graph binder_limit right))
    in case graph_attempt left right of SOME theorem => theorem
      | NONE => let val (left,right) = admit_nodes left right in
          case graph_attempt left right of SOME theorem => theorem
            | NONE =>
                (* Only an opaque binder beyond local admission can remain.
                   Never retry native discovery/substitution over the input
                   application DAG, even when the DAG itself is small. *)
                (SmtResource.check_term_size_for "BitVector" "binder-opening"
                   (binder_limit+1);
                 instantiation_declined "binder admission")
          end end
  end

  (* Normalize checked variable definitions by capture-avoiding kernel
     substitution.  Each layer substitutes simultaneously over the stored
     DAG; an acyclic definition graph stabilizes within its variable count.
     Cyclic expansion is an ordinary, bounded normalization refusal. *)
  local
    structure G = SmtReplayGraph
    structure P = SmtReplayProof
    datatype definition_step =
        DefinitionLeaf
      | DefinitionApplication of
          {operator : G.node, operand : G.node, result : G.node}
      | DefinitionReplacement of
          {fact : int, rhs : G.node, result : G.node}
  in
  fun checked_definition_rewrite_conv definitions target =
    let
      val operation = "checked_definition_rewrite_conv"
      fun error message = Feedback.mk_HOL_ERR "Library" operation message
      val limit = SmtResource.max_bv_replay_term_nodes
      val source_limit = case Int.maxInt of SOME n => n
        | NONE => SmtResource.max_metric
      fun variable theorem =
        let val left = boolSyntax.lhs (Thm.concl theorem) in
          if Term.is_var left then left
          else raise error "left endpoint is not a variable"
        end
      val theta = List.map (fn theorem =>
        {redex = variable theorem, residue = theorem}) definitions

      (* SUBST_CONV first replaces template variables by fresh holes using
         Term.subst. Both kernels' substitution maps keep the last supplied
         entry for a duplicate redex; only that hole selects a theorem in
         SUBST. Search in that order, without inspecting unused residues. *)
      val prospective_rules = List.rev (List.map (fn {redex,residue} =>
        (redex, boolSyntax.rhs (Thm.concl residue), ref NONE)) theta)
      fun residue_size (rhs, cached) = case !cached of SOME size => size
        | NONE =>
            let val size = case
                  SmtReplayImport.bounded_raw_size limit rhs of
                    SOME size => size | NONE => limit + 1
            in cached := SOME size;size end
      fun binder_refusal () = SmtResource.check_term_size_for
        "BitVector" "binder-opening" (limit + 1)
      fun prospective_refusal remaining =
        (* An excessive output necessarily changes this admitted input.
           At exhausted depth, the old worker reports the cycle BEFORE its
           next input-size check. Preserve that first error without doing
           the now-known unsafe substitution. *)
        if remaining = 0 then raise error "cyclic definition expansion"
        else binder_refusal ()

      (* Typed variable identity is metadata, not native aconv: independent
         equal Type DAGs must not be unfolded during admission. Use the
         graph's pointer-memoized Type interner only on a name collision. *)
      val identities = G.new ()
      fun same_variable left right =
        Portable.pointer_eq (left,right) orelse
        (#1 (Term.dest_var left) = #1 (Term.dest_var right) andalso
         G.variable identities (G.root_scope identities) G.RigidSource left =
         G.variable identities (G.root_scope identities) G.RigidSource right)

      (* Exact simultaneous raw-node prediction, saturated at limit+1.
         Opening is confined to the already admitted input, never a residue.
         Shadowed variables are not replaced; capture renaming changes no
         node counts. RHS sizes are lazy/memoized, not recursively rewritten.
         A large binder result would hit the existing binder-opening gate
         on the next iteration: refuse BEFORE native capture avoidance (and
         before graph import can inspect the newly inserted annotations). *)
      fun prospective_size term =
        let
          fun add (left,right) =
            if left > limit orelse right > limit - left then limit + 1
            else left + right
          fun selected _ [] = 1
            | selected variable ((redex,rhs,cached)::rest) =
                if same_variable variable redex then residue_size (rhs,cached)
                else selected variable rest
          fun walk shadowed term =
            if Term.is_var term then
              if List.exists (fn bound => same_variable bound term) shadowed
              then 1 else selected term prospective_rules
            else if Term.is_comb term then
              let val (operator,operand) = Term.dest_comb term
                  val left = walk shadowed operator
              in
                if left >= limit then limit + 1
                else add (1,add (left,walk shadowed operand))
              end
            else if Term.is_abs term then
              let
                val (bound,body) =
                  SmtReplayImport.dest_abs_preserving_names term
              in add (1,walk (bound::shadowed) body) end
            else 1
        in walk [] term end

      (* Outside binders, native SUBST inserts a residue once without
         traversing it. Keep that ordinary path (including large outputs).
         Find only the required binder islands, memoizing exposed source
         applications by POINTER, not by whole-term comparison. Bounded
         buckets keep collisions linear in the admitted input tree; losing
         optional memo entries loses reuse, never a checked conversion. *)
      exception ProspectiveBinder
      fun admit_binder_insertions root =
        let
          val seen = ref (Redblackmap.mkDict Int.compare)
          fun visit term =
            let
              val key = SmtReplayImport.pointer_bucket 3 4093 term
              val bucket = case Redblackmap.peek (!seen,key) of
                  SOME terms => terms | NONE => []
            in
              if List.exists (fn old => Portable.pointer_eq (old,term))
                  bucket then ()
              else
                (if List.length bucket < 8 then
                   seen := Redblackmap.insert (!seen,key,term::bucket)
                 else ();
                 if Term.is_abs term then
                   if prospective_size term > limit then
                     raise ProspectiveBinder else ()
                 else if Term.is_comb term then
                   let val (operator,operand) = Term.dest_comb term
                   in visit operator;visit operand end
                 else ())
            end
        in visit root end

      (* This adapter opens only an already bounded binder island. SUBST
         handles lexical capture without making an expanded ABS proof. Both
         its input and prospective output precede every native invocation. *)
      fun binder remaining term =
        let
          val _ = case SmtReplayImport.bounded_raw_size limit term of
              SOME _ => ()
            | NONE => SmtResource.check_term_size_for
                "BitVector" "binder-opening" (limit + 1)
          val _ = if prospective_size term > limit then
                    prospective_refusal remaining else ()
          val step = Drule.SUBST_CONV theta term term
          val right = boolSyntax.rhs (Thm.concl step)
        in
          if Term.aconv term right then Thm.REFL term
          else if remaining = 0 then
            raise error "cyclic definition expansion"
          else Thm.TRANS step (binder (remaining - 1) right)
        end

      fun graph_conversion initial_step root =
        let
          val graph = G.new ()
          val scope = G.root_scope graph
          fun source term = G.import graph scope source_limit term
          val original = source root
          val rules = ref (Redblackmap.mkDict Int.compare)
          val _ = List.app (fn theorem =>
            let
              val left = #node (source (variable theorem))
              val right = #node (source
                (boolSyntax.rhs (Thm.concl theorem)))
            in rules := Redblackmap.insert
              (!rules, G.node_id left, (right, theorem)) end) definitions
          val facts = ref ([] : (G.source * Thm.thm) list)
          val fact_count = ref 0
          fun fact theorem =
            let val index = !fact_count in
              fact_count := index + 1;
              facts := (source (Thm.concl theorem), theorem) :: !facts;
              index
            end
          val steps = ref (Redblackmap.mkDict Int.compare)
          val active = ref (Redblackset.empty Int.compare)
          fun discover node =
            case Redblackmap.peek (!steps, G.node_id node) of
              SOME (_, result) => result
            | NONE =>
                let
                  val _ = if Redblackset.member (!active, G.node_id node)
                    then raise error "cyclic definition expansion"
                    else active := Redblackset.add (!active, G.node_id node)
                  val (step, result) = case G.view graph node of
                      G.Variable (G.RigidSource, _) =>
                        (case Redblackmap.peek (!rules, G.node_id node) of
                           NONE => (DefinitionLeaf, node)
                         | SOME (right, theorem) =>
                             if right = node then (DefinitionLeaf, node)
                             else
                               let val index = fact theorem
                                   val result = discover right
                               in (DefinitionReplacement
                                 {fact = index, rhs = right, result = result},
                                 result) end)
                    | G.Application (operator, operand) =>
                        let
                          val left = discover operator
                          val right = discover operand
                          val result = G.application graph scope (left, right)
                        in (DefinitionApplication
                          {operator = operator, operand = operand,
                           result = result}, result) end
                    | G.OpaqueRetained => discover_binder node
                    | _ => (DefinitionLeaf, node)
                  val _ = steps := Redblackmap.insert
                    (!steps, G.node_id node, (step, result))
                  val _ = active := Redblackset.delete (!active, G.node_id node)
                in result end
          and discover_binder node =
            let
              val term = G.representative graph node
              val theorem = binder (List.length definitions) term
              val right = boolSyntax.rhs (Thm.concl theorem)
            in
              if Portable.pointer_eq (term,right) then
                (DefinitionLeaf,node)
              else
                let val result = #node (source right)
                in (DefinitionReplacement
                  {fact = fact theorem,rhs = result,result = result},result)
                end
            end
          (* On an unsafe prospective insertion, probe the virtual next
             root in ORIGINAL graph order, not with a global cycle scan.
             Source applications need only ordered visits: never construct
             their virtually substituted terms. A selected RHS is raw, so
             discover (not probe) must visit it; a source binder still owes
             the initial simultaneous layer. These phases have distinct
             memos even when they share the same original graph node.
             Imports/checked raw discovery retain their existing ownership;
             only admitted binder islands may execute native substitution.
             This path fails before root proof assembly or realization. *)
          val probed = ref (Redblackset.empty Int.compare)
          fun probe node =
            if Redblackset.member (!probed,G.node_id node) then ()
            else
              let
                val _ = case G.view graph node of
                    G.Variable (G.RigidSource,_) =>
                      (case Redblackmap.peek (!rules,G.node_id node) of
                         SOME (right,_) => ignore (discover right)
                       | NONE => ())
                  | G.Application (operator,operand) =>
                      (probe operator;probe operand)
                  | G.OpaqueRetained =>
                      let
                        val term = G.representative graph node
                        val _ = if prospective_size term > limit then
                                  binder_refusal () else ()
                        val step = Drule.SUBST_CONV theta term term
                        val right = boolSyntax.rhs (Thm.concl step)
                      in ignore (binder (List.length definitions) right) end
                  | _ => ()
                val _ = probed := Redblackset.add (!probed,G.node_id node)
              in () end
          val result = if initial_step then
              (probe (#node original);
               raise error "prospective binder probe did not fail")
            else discover (#node original)
        in
          if result = #node original then Thm.REFL root
          else
            let
              val marker = Term.genvar (G.type_of graph result)
              val equality_head = Term.rator (Term.rator
                (boolSyntax.mk_eq (marker, marker)))
              val equality = G.application graph scope
                (G.application graph scope
                  (G.constant graph scope equality_head, #node original),
                 result)
              val facts = List.rev (!facts)
              val block = P.freeze graph
                {scope = scope, roots = [equality],
                 sources = List.map (fn (source, _) => #node source) facts,
                 template_limit = limit}
              val assembled = ref (Redblackmap.mkDict Int.compare)
              fun trans left right = P.compose block
                (fn [left, right] => Thm.TRANS left right
                  | _ => raise error "invalid transitivity premises")
                [left, right]
              fun reflexive node = P.checked block
                (Thm.REFL (P.name block node))
              fun source_fact index =
                let val node = #node (#1 (List.nth (facts, index))) in
                  P.compose block
                    (fn [constructor, premise] => Thm.EQ_MP
                        constructor premise
                      | _ => raise error "invalid definition premises")
                    [P.constructor block node, P.source block index]
                end
              fun assemble node =
                case Redblackmap.peek (!assembled, G.node_id node) of
                  SOME proof => proof
                | NONE =>
                    let
                      val (step, result) = Redblackmap.find
                        (!steps, G.node_id node)
                      val proof = case step of
                          DefinitionLeaf => reflexive node
                        | DefinitionReplacement {fact, rhs, ...} =>
                            if rhs = result then source_fact fact
                            else trans (source_fact fact) (assemble rhs)
                        | DefinitionApplication {operator, operand, ...} =>
                            if result = node then reflexive node
                            else
                              let
                                val children = P.compose block
                                  (fn [left, right] =>
                                      Thm.MK_COMB (left, right)
                                    | _ => raise error
                                        "invalid congruence premises")
                                  [assemble operator, assemble operand]
                                val backwards = P.compose block
                                  (fn [proof] => Thm.SYM proof
                                    | _ => raise error
                                        "invalid constructor premise")
                                  [P.definition block result]
                              in trans (P.definition block node)
                                (trans children backwards) end
                      val _ = assembled := Redblackmap.insert
                        (!assembled, G.node_id node, proof)
                    in proof end
              val proof = P.compose block
                (fn [constructor, conversion] => Thm.EQ_MP
                    (Thm.SYM constructor) conversion
                  | _ => raise error "invalid equality naming premises")
                [P.constructor block equality, assemble (#node original)]
              val realized = P.realize block equality proof
              (* Restore the supplied semantic definition theorems after
                 the compact context has been discharged. Their original
                 hypotheses survive; constructor/context facts do not. *)
              val restored = List.foldl
                (fn ((source, theorem), result) =>
                  let
                    val witness = Thm.EQ_MP (#bridge source) theorem
                    val _ = check_oracle_tags "Library" operation witness
                  in Drule.PROVE_HYP witness result end) realized facts
            in Thm.TRANS (#bridge original) restored end
        end

      fun normalize remaining term =
        let
          val has_binder = ref false
          (* Observe the existing raw-size pass, without a second scan of
             binder-free syntax or any extra Type getter/admission. *)
          val size = SmtReplayImport.bounded_raw_size_observing_binders
            (fn () => has_binder := true) limit term
        in
          case size of NONE => graph_conversion false term
          | SOME _ =>
              if !has_binder andalso
                 ((admit_binder_insertions term;false)
                   handle ProspectiveBinder => true) then
                (* The next root is excessive, hence changed. Exhaustion
                   precedes its size check; otherwise graph discovery of
                   that next root chooses the first error. *)
                if remaining = 0 then
                  raise error "cyclic definition expansion"
                else graph_conversion true term
              else let
                val step = Drule.SUBST_CONV theta term term
                val right = boolSyntax.rhs (Thm.concl step)
              in
                if Term.aconv term right then Thm.REFL term
                else if remaining = 0 then
                  raise error "cyclic definition expansion"
                else Thm.TRANS step (normalize (remaining - 1) right)
              end
        end
    in
      if List.null definitions then Thm.REFL target
      else normalize (List.length definitions) target
    end
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

  val TO_WORD_EXTRACT = HolSmtTheory.TO_WORD_EXTRACT

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
        (simpLib.++(bossLib.bool_ss, boolSimps.LET_ss)) []
        wordsTheory.bit_field_insert;

  (* Lowers constant-index bit operations and shifts to the bit-vector forms
     the translation encodes natively.  Each assumption is rewritten on its
     own, like the conclusion: a word operation left in an assumption is
     translated as an uninterpreted function, which can make an unsatisfiable
     negation satisfiable. *)
  val WORD_SIMP_TAC = let
    open Tactical Conv Tactic wordsTheory simpLib
    val ss = pureSimps.pure_ss ++ numSimps.REDUCE_ss ++ wordsLib.SIZES_ss
    val thms =
      [word_rol_bv_def, word_ror_bv_def,
       w2n_n2w, word_bit_def, bit_field_insert_rwt,
       word_lsb_def, word_msb_def,
       WORD_SLICE_THM, WORD_BITS_EXTRACT,
       WORD_BIT_EXTRACT, WORD_SHIFT_BV, TO_WORD_EXTRACT]
  in
    CONV_TAC (DEPTH_CONV wordsLib.EXPAND_REDUCE_CONV) THEN
      SIMP_TAC ss thms THEN
      CONV_TAC (DEPTH_CONV wordsLib.EXTEND_EXTRACT_CONV) THEN
      RULE_ASSUM_TAC
        (CONV_RULE (DEPTH_CONV wordsLib.EXTEND_EXTRACT_CONV) o
         SIMP_RULE ss thms o
         CONV_RULE (DEPTH_CONV wordsLib.EXPAND_REDUCE_CONV))
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

  (* Does [ty], a function component, or a native sequence element type
     satisfy [pred]?  Do not descend through arbitrary constructor arguments:
     word widths and similar phantom parameters are not SMT value sorts. *)
  fun type_contains pred ty =
    pred ty orelse
    (case Lib.total Type.dest_type ty of
       SOME ("fun", [dom, rng]) =>
         type_contains pred dom orelse type_contains pred rng
     | SOME ("list", [element]) => type_contains pred element
     | _ => false)

  fun type_contains_int ty =
    type_contains (fn ty => Type.compare (ty, intSyntax.int_ty) = EQUAL) ty

  fun type_contains_real ty =
    type_contains (fn ty => Type.compare (ty, realSyntax.real_ty) = EQUAL) ty

  fun type_contains_word ty =
    type_contains (Lib.can wordsSyntax.dest_word_type) ty

  (* HOL's own :string, i.e. a char list.  Used by the logic-fragment checker
     to keep a parsed char-list string out of the datatype classification; the
     SMT String sort is 'type_contains_string' below. *)
  fun type_contains_native_string ty =
    type_contains (fn ty => Type.compare (ty, stringSyntax.string_ty) = EQUAL)
      ty

  (* The SMT-LIB String sort, i.e. smtstring$smtstr.  HOL's :string is
     deliberately not included: it is never emitted as an SMT String. *)
  fun type_contains_string ty =
    type_contains
      (fn candidate =>
        case Lib.total Type.dest_thy_type candidate of
          SOME {Thy = "smtstring", Tyop = "smtstr", Args = []} => true
        | _ => false)
      ty

  (* 'tm' is exactly the constant 'c' (same name and theory) *)
  fun same_const c tm = Term.is_const tm andalso Term.same_const tm c

  (* the constant 'c' occurs somewhere in 'tm' *)
  fun contains_const c tm = SmtResource.contains (same_const c) tm

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

  (* Rewrites contributed by the rows of a goal-directed fact table whose
     head constant occurs in 'tm'.  The goal is traversed once, rather than
     once per row: constants are identified by theory and name, exactly as
     'same_const' compares them. *)
  fun goal_directed_rewrites table tm =
    let
      val name_compare = Lib.pair_compare (String.compare, String.compare)
      fun add (subterm, names) =
        case Lib.total Term.dest_thy_const subterm of
          SOME {Thy, Name, ...} => HOLset.add (names, (Thy, Name))
        | NONE => names
      val names =
        List.foldl add (HOLset.empty name_compare) (subterms tm)
      fun occurs head =
        case Lib.total Term.dest_thy_const head of
          SOME {Thy, Name, ...} => HOLset.member (names, (Thy, Name))
        | NONE => false
    in
      List.concat
        (List.map (fn (_, _, facts) => facts)
          (List.filter (fn (_, head, _) => occurs head) table))
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
     A multiplication is nonlinear when both operands are non-literal.  A
     num, int, or real power is nonlinear when its base is non-literal and
     its exponent is symbolic or a literal at least 2.  Exponents 0 and 1,
     and powers with literal bases, stay on the linear/evaluation side. *)
  fun is_nonlinear tm =
  let
    fun is_nl_mult dest_mult t =
      (let val (l, r) = dest_mult t
       in not (is_numeric_literal l) andalso not (is_numeric_literal r) end)
      handle Feedback.HOL_ERR _ => false
    fun is_nl_power dest_power t =
      (let
         val (base, exponent) = dest_power t
       in
         not (is_numeric_literal base) andalso
         (case Lib.total numSyntax.dest_numeral exponent of
            SOME n => Arbnum.<= (Arbnum.two, n)
          | NONE => true)
       end)
      handle Feedback.HOL_ERR _ => false
    fun check t =
      is_nl_mult realSyntax.dest_mult t orelse
      is_nl_mult intSyntax.dest_mult t orelse
      is_nl_mult numSyntax.dest_mult t orelse
      is_nl_power realSyntax.dest_pow t orelse
      is_nl_power intSyntax.dest_exp t orelse
      is_nl_power numSyntax.dest_exp t
  in
    List.exists check (subterms tm)
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
     Type-dispatches: real to REAL_NLA then REAL_SOS, int to INT_SOS,
     num to NUM_SOS_RULE. Avoids trying wrong-type provers. *)
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

  (* SOS procedures accept polynomial arithmetic.  A totalized division or
     remainder encoding can contain syntactic products, but those products do
     not make the surrounding term polynomial.  Powers with symbolic
     exponents are nonpolynomial too.  Sending either family to CSDP is both
     fruitless and very expensive. *)
  fun contains_nonpolynomial_arithmetic tm =
    let
      fun is_real_division_head head =
        Term.same_const head realSyntax.div_tm
      fun is_nonpolynomial_head head =
        List.exists (Term.same_const head)
          [numSyntax.div_tm, numSyntax.mod_tm,
           intSyntax.div_tm, intSyntax.mod_tm,
           intSyntax.quot_tm, intSyntax.rem_tm] orelse
        (case Lib.total Term.dest_thy_const head of
           SOME {Thy = "HolSmt", Name, ...} =>
             List.exists (Lib.equal Name)
               ["smt_ediv_total", "smt_emod_total", "smt_rdiv"]
         | _ => false)
      fun is_symbolic_power_application head arguments =
        List.exists (Term.same_const head)
          [numSyntax.exp_tm, intSyntax.exp_tm, realSyntax.exp_tm] andalso
        (case arguments of
           [_, exponent] => not (numSyntax.is_numeral exponent)
         | _ => true)
      fun is_nonpolynomial_application head arguments =
        if is_real_division_head head then
          (case arguments of
             [_, denominator] => not (is_numeric_literal denominator)
           | _ => true)
        else
          is_nonpolynomial_head head orelse
          is_symbolic_power_application head arguments
      fun search term =
        case Lib.total Term.dest_abs term of
          SOME (_, body) => search body
        | NONE =>
            let val (head, arguments) = boolSyntax.strip_comb term in
              is_nonpolynomial_application head arguments orelse
              List.exists search arguments
            end
    in search tm end

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
    if is_nonlinear tm andalso not (contains_nonpolynomial_arithmetic tm) then
      nla_prove tm
    else raise Feedback.mk_HOL_ERR "Library" "arith_prove_with_cases"
      ("failed: " ^ term_to_string tm)

  fun NLA_TAC (goal as (_, term)) ctxt =
    if term_contains_real_ty term then
      NLArith.NLA_TAC goal ctxt
      handle Feedback.HOL_ERR _ =>
      SOSLib.REAL_SOS_TAC goal ctxt
    else
      SOSLib.INT_SOS_TAC goal ctxt
      handle Feedback.HOL_ERR _ =>
      SOSLib.NUM_SOS_RULE_TAC goal ctxt

end
