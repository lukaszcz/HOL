(* Task46 legacy private-FP/deferred closure controls, including complete
   final-F certificates through check_proof.  Every cached dependency below
   is an actual kernel theorem. *)
structure CPC_DeferredMarkerTests =
struct
  open HolKernel Parse boolLib bossLib
  structure P = CPC_ProofParser
  structure R = CPC_ProofReplay

  fun require message yes = if yes then () else raise Fail message
  fun test label action =
    (testutils.tprint label; action (); testutils.OK ())
  fun clean theorem =
    (require "private/deferred theorem has axioms"
       (null (Tag.axioms_of (Thm.tag theorem)));
     require "private/deferred theorem has oracle tags"
       (List.all (fn tag => tag = "DISK_THM")
         (#1 (Tag.dest_tag (Thm.tag theorem)))))
  fun exact goal hypotheses theorem =
    (require "wrong private/deferred conclusion"
       (Term.aconv (Thm.concl theorem) goal);
     require "wrong private/deferred actual Hyp"
       (HOLset.equal (Thm.hypset theorem,
         HOLset.addList (Term.empty_tmset, hypotheses)));
     clean theorem)
  fun rejects function message action =
    require "private marker rejected at the wrong gate (or accepted)"
      ((action (); false) handle Feedback.HOL_ERR detail =>
         Feedback.top_structure_of detail = "CPC_ProofReplay" andalso
         Feedback.top_function_of detail = function andalso
         Feedback.message_of detail = message)

  fun parse_cpc_proof_string contents =
    let
      val dicts = SmtLib_Logics.parsedicts_of_logic "ALL"
      val instream = TextIO.openString contents
      val result = Exn.capture
        (P.parse_stream_with_version dicts "1.3.4") instream
      val _ = TextIO.closeIn instream
    in Exn.release result end

  (* Definitions alone can be pruned.  Keep both allocated occurrences in
     real parsed ASSUMEs and check them against the parser's identity table. *)
  fun reflexive_marker command =
    case command of
      CPC_Proof.ASSUME (_, {term, ...}) =>
        let val (left, right) = boolSyntax.dest_eq term
        in require "marker fixture is not reflexive" (Term.aconv left right);
           require "parser did not allocate a private marker"
             (P.is_cpc_fp_private_marker left);
           left
        end
    | _ => raise Fail "missing marker-retaining parsed ASSUME"
  fun marker_pair proof =
    case CPC_Proof.proof_commands proof of
      [first, second] =>
        let val first = reflexive_marker first
            val second = reflexive_marker second
        in require "private occurrences were conflated"
             (not (Term.aconv first second));
           (first, second)
        end
    | _ => raise Fail "wrong marker fixture command count"
  fun unbound_pair () =
    let
      val pair as (first, second) = marker_pair (parse_cpc_proof_string
        "((define @t1 () (@fp.INF (_ BitVec 1))) \
        \(define @t2 () (@fp.INF (_ BitVec 1))) \
        \(assume @p1 (= @t1 @t1)) (assume @p2 (= @t2 @t2)))")
      val registered = P.cpc_fp_private_unbound_markers ()
      fun registered_inf marker = List.exists (fn (saved, kind) =>
        kind = "@fp.INF" andalso Term.aconv marker saved) registered
    in
      require "wrong unbound private marker registry"
        (length registered = 2 andalso registered_inf first andalso
         registered_inf second andalso
         null (P.cpc_fp_private_bindings ()));
      pair
    end

  (* Exact bridge body from Unittest.cpc_fp_private_witness_search_success.
     Only marker allocation changes: printed names are NOT marker authority. *)
  fun bridge source marker = boolSyntax.mk_eq
    (``smtfp_is_infinite ^source``,
     boolSyntax.mk_eq (``1w : word1``, marker))
  fun witness source = SmtLib_Theories.mk_bbterm
    [``smtfp_is_infinite ^source``]
  fun no_private theorem =
    require "allocated private marker leaked from closed theorem"
      (not (List.exists (fn term => HolKernel.can
        (HolKernel.find_term P.is_cpc_fp_private_marker) term)
        (Thm.concl theorem :: Thm.hyp theorem)))

  fun two_markers () =
    let
      val x = ``x : (3,5) smtfp``
      val y = ``y : (3,5) smtfp``
      val (first, second) = unbound_pair ()
      val left = bridge x first
      val right = bridge y second
      val source = Thm.CONJ (Thm.ASSUME left) (Thm.ASSUME right)
      val _ = exact (boolSyntax.mk_conj (left, right)) [left, right] source
      val theorem = R.discharge_private_fp_for_test source
      val expected = boolSyntax.mk_conj
        (bridge x (witness x), bridge y (witness y))
    in exact expected [] theorem; no_private theorem end

  fun false_bridge () =
    let
      val (first, second) = unbound_pair ()
      val left = bridge ``x : (3,5) smtfp`` first
      (* Still a classification anchor, but its checked witness is false. *)
      val right = boolSyntax.mk_eq
        (``smtfp_is_infinite (y : (3,5) smtfp)``,
         boolSyntax.mk_eq (``0w : word1``, second))
      val source = Thm.CONJ (Thm.ASSUME left) (Thm.ASSUME right)
      val _ = exact (boolSyntax.mk_conj (left, right)) [left, right] source
    in rejects "instantiate_cpc_fp_unbound_markers"
      "no checked assignment discharges private FP bridges"
      (fn () => ignore (R.discharge_private_fp_for_test source)) end

  fun unanchored_leak () =
    let
      val (marker, _) = unbound_pair ()
      val leaked = boolSyntax.mk_eq (marker, ``1w : word1``)
      val source = Thm.ASSUME leaked
      val _ = exact leaked [leaked] source
    in rejects "instantiate_cpc_fp_unbound_markers"
      "private FP components have no classification anchors"
      (fn () => ignore (R.discharge_private_fp_for_test source)) end

  fun foreign_hypothesis () =
    let
      val (marker, _) = unbound_pair ()
      val x = ``x : (3,5) smtfp``
      val obligation = bridge x marker
      val foreign = Term.mk_var ("@fp.task46_foreign", Type.bool)
      val source = Thm.CONJ (Thm.ASSUME obligation) (Thm.ASSUME foreign)
      val expected = boolSyntax.mk_conj (bridge x (witness x), foreign)
      val theorem = R.discharge_private_fp_for_test source
    in exact expected [foreign] theorem; no_private theorem end

  fun source_looking_variable () =
    let
      val _ = unbound_pair ()
      val ordinary = Term.mk_var ("@fp.INF#unbound0", ``:word1``)
      val _ = require "printed source name became marker authority"
        (not (P.is_cpc_fp_private_marker ordinary))
      val obligation = bridge ``x : (3,5) smtfp`` ordinary
      val source = Thm.ASSUME obligation
      val theorem = R.discharge_private_fp_for_test source
      val contextual = R.discharge_private_fp_with_context_for_test
        [obligation] source
    in
      (* No witness may be invented for this ordinary source variable. *)
      exact obligation [obligation] theorem;
      exact obligation [obligation] contextual;
      require "ordinary source variable was substituted"
        (List.exists (Term.aconv ordinary)
          (Term.free_vars (Thm.concl theorem)))
    end

  fun explicit_marker () =
    let
      val proof = parse_cpc_proof_string
        "((declare-const x (_ FloatingPoint 3 5)) \
        \(define @t1 () (@fp.INF (_ BitVec 1) x)) \
        \(assume @p1 (= @t1 @t1)))"
      val marker = case CPC_Proof.proof_commands proof of
          [command] => reflexive_marker command
        | _ => raise Fail "wrong explicit marker command count"
      val source = case P.cpc_fp_private_bindings () of
          [{marker = saved, kind, source}] =>
            (require "wrong explicit marker registry"
               (kind = "@fp.INF" andalso Term.aconv saved marker);
             source)
        | _ => raise Fail "missing explicit marker binding"
      val _ = require "explicit marker entered unbound registry"
        (null (P.cpc_fp_private_unbound_markers ()))
    in (marker, source) end

  fun explicit_positive () =
    let val (marker, source) = explicit_marker ()
        val theorem = R.discharge_private_fp_for_test
          (Thm.ASSUME (bridge source marker))
    in exact (bridge source (witness source)) [] theorem;
       no_private theorem end

  fun source_exclusion explicit () =
    let
      val marker = if explicit then #1 (explicit_marker ())
        else #1 (unbound_pair ())
      val original = boolSyntax.mk_eq (marker, marker)
      val source = Thm.ASSUME original
      val _ = exact original [original] source
    in rejects "instantiate_cpc_fp_unbound_markers"
      "private FP component occurs in the original proof context"
      (fn () => ignore (R.discharge_private_fp_with_context_for_test
        [original] source)) end

  fun mixed_markers () =
    let
      val (unbound, explicit) = marker_pair (parse_cpc_proof_string
        "((declare-const y (_ FloatingPoint 3 5)) \
        \(define @t1 () (@fp.INF (_ BitVec 1))) \
        \(define @t2 () (@fp.INF (_ BitVec 1) y)) \
        \(assume @p1 (= @t1 @t1)) (assume @p2 (= @t2 @t2)))")
      val _ = require "mixed fixture lost one marker class"
        (length (P.cpc_fp_private_unbound_markers ()) = 1 andalso
         length (P.cpc_fp_private_bindings ()) = 1)
      val explicit_source = case P.cpc_fp_private_bindings () of
          [{marker, kind, source}] =>
            (require "wrong mixed explicit marker binding"
               (kind = "@fp.INF" andalso Term.aconv marker explicit);
             source)
        | _ => raise Fail "missing mixed explicit marker binding"
      val x = ``x : (3,5) smtfp``
      val obligation = bridge x unbound
      val foreign = Term.mk_var ("task46_mixed_foreign", Type.bool)
      (* Keep the explicit component in a checked REFL conclusion, not an
         extra FP bridge: unbound witness validation precedes explicit
         instantiation.  The explicit-only bridge is checked separately.
         A foreign Hyp must survive both instantiations and closure. *)
      val source = Thm.CONJ (Thm.ASSUME obligation)
        (Thm.CONJ (Thm.REFL explicit) (Thm.ASSUME foreign))
      val endpoint = boolSyntax.mk_conj (obligation,
        boolSyntax.mk_conj (boolSyntax.mk_eq (explicit, explicit), foreign))
      val _ = exact endpoint [obligation, foreign] source
      (* Match the two sequential kernel instantiations.  Use the parsed
         operand: SMT FloatingPoint widths are not HOL smtfp type indices. *)
      val unbound_endpoint = Term.subst
        [{redex = unbound, residue = witness x}] endpoint
      val expected = Term.subst
        [{redex = explicit, residue = witness explicit_source}]
        unbound_endpoint
      val theorem = R.discharge_private_fp_for_test source
    in exact expected [foreign] theorem; no_private theorem end

  fun registry () =
    (P.cpc_fp_private_bindings (), P.cpc_fp_private_unbound_markers ())
  fun exact_registry (bindings, unbound) =
    let
      fun same_binding (left : P.cpc_fp_private_binding,
                        right : P.cpc_fp_private_binding) =
        #kind left = #kind right andalso
        Term.aconv (#marker left) (#marker right) andalso
        Term.aconv (#source left) (#source right)
      fun same_unbound ((left, kind), (right, saved_kind)) =
        kind = saved_kind andalso Term.aconv left right
      val (actual_bindings, actual_unbound) = registry ()
    in require "private proof scope did not restore exact registry"
      (ListPair.allEq same_binding (bindings, actual_bindings) andalso
       ListPair.allEq same_unbound (unbound, actual_unbound)) end

  (* Keep only a new proof record sharing the parsed command spine. A weak
     key on the original record (or on a fresh wrapper ref) cannot survive
     the GC below. Metadata must not retain a replay result or source thm. *)
  fun retained_fixture name : CPC_Proof.proof =
    let
      val parsed = parse_cpc_proof_string
        ("((declare-const " ^ name ^ " (_ FloatingPoint 3 5)) " ^
         "(define @u () (@fp.INF (_ BitVec 1))) " ^
         "(define @e () (@fp.INF (_ BitVec 1) " ^ name ^ ")) " ^
         "(assume @p1 (= @u @u)) (assume @p2 (= @e @e)))")
    in {commands = CPC_Proof.proof_commands parsed,
        cvc_version = CPC_Proof.proof_version parsed} end

  fun retained_registry () =
    let
      val proof_a = retained_fixture "task46_registry_a"
      val (unbound, explicit) = marker_pair proof_a
      val saved_a as (bindings_a, _) = registry ()
      val explicit_source = case bindings_a of
          [{source, ...}] => source
        | _ => raise Fail "missing retained explicit binding"
      val proof_b = retained_fixture "task46_registry_b"
      val (unbound_b, explicit_b) = marker_pair proof_b
      val saved_b = registry ()
      val _ = PolyML.fullGC ()
      fun active_a () =
        (exact_registry saved_a;
         require "retained proof did not restore marker identity"
           (P.is_cpc_fp_private_marker unbound andalso
            P.is_cpc_fp_private_marker explicit andalso
            not (P.is_cpc_fp_private_marker unbound_b) andalso
            not (P.is_cpc_fp_private_marker explicit_b)))
      fun replay_a foreign =
        let
          val _ = active_a ()
          val _ = P.with_cpc_fp_private_proof proof_b
            (fn () => exact_registry saved_b) ()
          val _ = active_a ()
          val original = boolSyntax.mk_eq (explicit, explicit)
          val raw = R.replay_root_for_test proof_a
          val _ = active_a ()
          val _ = exact original [original] raw
          val closed = R.discharge_private_fp_for_test raw
          val replacement = witness explicit_source
          val _ = exact (boolSyntax.mk_eq (replacement, replacement))
            [] closed
          val _ = no_private closed
          val _ = exact original [original] raw
          val x = ``task46_registry_x : (3,5) smtfp``
          val obligation = bridge x unbound
          val source = Thm.CONJ (Thm.ASSUME obligation)
            (Thm.CONJ (Thm.REFL explicit) (Thm.ASSUME foreign))
          val endpoint = boolSyntax.mk_conj (obligation,
            boolSyntax.mk_conj (original, foreign))
          val expected = boolSyntax.mk_conj (bridge x (witness x),
            boolSyntax.mk_conj
              (boolSyntax.mk_eq (replacement, replacement), foreign))
          val theorem = R.discharge_private_fp_for_test source
          val _ = exact expected [foreign] theorem
          val _ = no_private theorem
          (* Re-entering the same retained proof must use this invocation's
             actual Source/Hyp, not a previously closed source theorem. *)
          val _ = exact endpoint [obligation, foreign] source
        in foreign end
      fun healthy name =
        let
          val foreign = Term.mk_var (name, Type.bool)
          val result = P.with_cpc_fp_private_proof proof_a replay_a foreign
        in require "proof scope changed action input/result"
             (Term.aconv foreign result);
           exact_registry saved_b end
      fun terminal primary same =
        let
          val outcome = Exn.capture
            (P.with_cpc_fp_private_proof proof_a
              (fn () => (active_a (); raise primary))) ()
        in require "proof registry scope swallowed/replaced an exception"
             (case outcome of Exn.Exn actual => same actual | _ => false);
           exact_registry saved_b end
      val _ = healthy "task46_registry_first"
      val failure = "task46_registry_failure"
      val _ = terminal (Fail failure)
        (fn Fail actual => actual = failure | _ => false)
      val _ = terminal Interrupt (fn Interrupt => true | _ => false)
      val _ = healthy "task46_registry_after_interrupt"
      val duration = Time.fromMilliseconds 463
      val _ = terminal (Timeout.TIMEOUT duration)
        (fn Timeout.TIMEOUT actual => Portable.pointer_eq (duration, actual)
          | _ => false)
      val _ = healthy "task46_registry_after_timeout"
      val resource = case Exn.capture (fn () =>
          SmtResource.check_dag_size_with_limit "Task46" "registry" 1 2)
          () of
          Exn.Exn error => error
        | _ => raise Fail "registry resource fixture did not gate"
      val _ = terminal resource (fn Feedback.HOL_ERR actual =>
          (case resource of Feedback.HOL_ERR expected =>
             SmtResource.is_resource_gate actual andalso
             Portable.pointer_eq (actual, expected)
           | _ => false)
        | _ => false)
      val _ = healthy "task46_registry_after_resource"
      (* An unregistered proof must not inherit the ambient B authority. *)
      val unknown = {commands = [],
        cvc_version = CPC_Proof.proof_version proof_a}
      val _ = P.with_cpc_fp_private_proof unknown
        (fn () => exact_registry ([], [])) ()
    in exact_registry saved_b end

  fun source_name_collision () =
    let
      val prefix = "%%genvar%%"
      val probe = Term.genvar ``:word1``
      val probe_name = #1 (Term.dest_var probe)
      val _ = require "unexpected genvar naming convention"
        (String.isPrefix prefix probe_name)
      val serial = valOf (Int.fromString
        (String.extract (probe_name, String.size prefix, NONE)))
      (* No source declarations or callback probes consume fresh variables.
         Cover the next 32 candidates and require evidence of an actual
         collision, not just accidental freshness after unrelated genvars. *)
      val variables = List.tabulate (32, fn index => Term.mk_var
        (prefix ^ Int.toString (serial + index + 1), ``:word1``))
      val context = List.map (fn term => boolSyntax.mk_eq (term, term))
        variables
      fun action () =
        let
          val proof = parse_cpc_proof_string
            "((define @t1 () (@fp.INF (_ BitVec 1))) \
            \(assume @p1 (= @t1 @t1)))"
          val marker = case CPC_Proof.proof_commands proof of
              [command] => reflexive_marker command
            | _ => raise Fail "wrong collision fixture command count"
          val name = #1 (Term.dest_var marker)
          val _ = require "freshness control did not force a name collision"
            (List.exists (fn source =>
              name = #1 (Term.dest_var source) ^ "'") variables)
          val _ = require "private allocation captured a source variable"
            (List.all (fn source => not (Term.aconv marker source) andalso
              name <> #1 (Term.dest_var source)) variables)
          val x = ``task46_fresh_x : (3,5) smtfp``
          val obligation = bridge x marker
          val source = Thm.CONJ (Thm.ASSUME obligation)
            (Drule.LIST_CONJ (List.map Thm.ASSUME context))
          val theorem = R.discharge_private_fp_with_context_for_test
            context source
          val expected = boolSyntax.mk_conj (bridge x (witness x),
            boolSyntax.list_mk_conj context)
        in exact expected context theorem; no_private theorem;
           exact (boolSyntax.mk_conj
             (obligation, boolSyntax.list_mk_conj context))
             (obligation :: context) source end
    in P.with_cpc_fp_private_source_terms context action () end

  (* A depth-70 shared source is tiny as a DAG, but impossible to expand
     as a tree. Ordinary parsing must not demand its freshness variables;
     actual private allocation must scan it without losing the sharing.
     The source variables are known by construction: never FVL/free_vars
     this fixture, even when checking the result. *)
  fun shared_source_freshness () =
    Timeout.apply (Time.fromSeconds 10) (fn () =>
      let
        val prefix = "%%genvar%%"
        val probe_name = #1 (Term.dest_var (Term.genvar ``:word1``))
        val _ = require "unexpected shared-source genvar naming convention"
          (String.isPrefix prefix probe_name)
        val serial = valOf (Int.fromString
          (String.extract (probe_name, String.size prefix, NONE)))
        val variables = List.tabulate (32, fn index => Term.mk_var
          (prefix ^ Int.toString (serial + index + 1), ``:word1``))
        val leaf = boolSyntax.list_mk_conj (List.map
          (fn term => boolSyntax.mk_eq (term, term)) variables)
        fun share 0 term = term
          | share depth term =
              share (depth - 1) (boolSyntax.mk_conj (term, term))
        val shared = share 70 leaf
        val _ = P.with_cpc_fp_private_source_terms [shared] (fn () =>
          let
            val proof = parse_cpc_proof_string
              "((step @p (= true true) :rule refl :args (true)))"
            val _ = require "ordinary shared-source parse changed commands"
              (case CPC_Proof.proof_commands proof of
                 [CPC_Proof.STEP {id = "@p", conclusion = SOME {term, ...},
                    args = [{term = argument, ...}], premises = [], ...}] =>
                   Term.aconv term (boolSyntax.mk_eq
                     (boolSyntax.T, boolSyntax.T)) andalso
                   Term.aconv argument boolSyntax.T
               | _ => false)
          in exact_registry ([], []) end) ()
      in P.with_cpc_fp_private_source_terms [shared] (fn () =>
        let
          val proof = parse_cpc_proof_string
            "((define @t1 () (@fp.INF (_ BitVec 1))) \
            \(assume @p1 (= @t1 @t1)))"
          val marker = case CPC_Proof.proof_commands proof of
              [command] => reflexive_marker command
            | _ => raise Fail "wrong shared-source marker command count"
          val name = #1 (Term.dest_var marker)
          val _ = require "shared-source fixture did not force a collision"
            (List.exists (fn source =>
              name = #1 (Term.dest_var source) ^ "'") variables)
          val _ = require "shared-source variable became a private marker"
            (List.all (fn source => not (Term.aconv marker source) andalso
              name <> #1 (Term.dest_var source) andalso
              not (P.is_cpc_fp_private_marker source)) variables)
        in exact_registry ([], [(marker, "@fp.INF")]) end) () end) ()

  (* Force a native descriptor collision, not merely a source-looking
     printed name. The lambda fixtures enter add_term only as compounds:
     inline @var and ordinary parser binders must reserve their own atoms. *)
  fun parsed_source_freshness () =
    let
      fun check (label, declarations, operand, bound) =
        let
          val prefix = "%%genvar%%"
          val probe_name = #1 (Term.dest_var (Term.genvar ``:word1``))
          val _ = require "unexpected parsed-source genvar convention"
            (String.isPrefix prefix probe_name)
          val serial = valOf (Int.fromString
            (String.extract (probe_name, String.size prefix, NONE)))
          val name = prefix ^ Int.toString (serial + 1)
          val ordinary = Term.mk_var (name, ``:word1``)
          val proof = parse_cpc_proof_string
            ("(" ^ declarations name ^
             "(define @t1 () (@fp.SIGN (_ BitVec 1) " ^ operand ^ ")) " ^
             "(assume @p1 (= @t1 @t1)))")
          val marker = case CPC_Proof.proof_commands proof of
              [command] => reflexive_marker command
            | _ => raise Fail (label ^ ": wrong marker command count")
          val source = case P.cpc_fp_private_bindings () of
              [{marker = saved, kind = "@fp.SIGN", source}] =>
                (require (label ^ ": wrong saved marker")
                   (Term.aconv saved marker); source)
            | _ => raise Fail (label ^ ": wrong explicit binding")
          val _ = require (label ^ ": fixture missed the next genvar")
            (#1 (Term.dest_var marker) = name ^ "'")
          val _ = require (label ^ ": original atom became private")
            (not (P.is_cpc_fp_private_marker ordinary) andalso
             not (Term.aconv marker ordinary))
          val _ = require (label ^ ": source captured the private marker")
            (not (Term.free_in marker source))
          val _ = require (label ^ ": original source scope changed")
            (if bound then
               let
                 val abstraction = HolKernel.find_term Term.is_abs source
                 val (variable, body) = Term.dest_abs abstraction
               in Term.aconv variable ordinary andalso
                  Term.aconv body ordinary andalso
                  not (Term.free_in ordinary source)
               end
             else Term.free_in ordinary source)
        in exact_registry
          ([{marker = marker, kind = "@fp.SIGN", source = source}], []) end
      fun var name = "(@var \"" ^ name ^ "\" (_ BitVec 1))"
      val fp = "(fp @var_word #b000 #b0000)"
    in
      List.app check
        [("definition @var", fn name =>
            "(define @var_word () " ^ var name ^ ") " ^
            "(define @s () " ^ fp ^ ") ", "@s", false),
         ("inline @var", fn name =>
            "(define @s () (lambda (@list " ^ var name ^ ") " ^
            var name ^ ")) (define @var_word () (_ @s #b0)) ", fp, true),
         ("parser binder", fn name =>
            "(define @s () (lambda ((" ^ name ^ " (_ BitVec 1))) " ^
            name ^ ")) (define @var_word () (_ @s #b0)) ", fp, true)]
    end

  (* Reverse declaration order: an ordinary descriptor can arrive after
     private allocation. Repeated @var/declaration/binder occurrences must
     agree, but cannot acquire private identity, nor alias another ordinary
     descriptor via the collision's renamed image. *)
  fun later_source_freshness () =
    let
      fun check mode =
        let
          val prefix = "%%genvar%%"
          val probe = #1 (Term.dest_var (Term.genvar ``:word1``))
          val serial = valOf (Int.fromString
            (String.extract (probe, String.size prefix, NONE)))
          val name = prefix ^ Int.toString (serial + 1)
          fun var name = "(@var \"" ^ name ^ "\" (_ BitVec 1))"
          val declaration = if mode = "declaration" then
              "(declare-const " ^ name ^ " (_ BitVec 1)) " else ""
          val ordinary = if mode = "declaration" then name else var name
          val binder = if mode = "binder" then
              "(lambda ((" ^ name ^ " (_ BitVec 1))) " ^ name ^ ")"
            else "(lambda (@list " ^ var name ^ ") " ^ var name ^ ")"
          val proof = parse_cpc_proof_string
            ("((declare-const x (_ FloatingPoint 3 5)) " ^
             "(define @private () (@fp.SIGN (_ BitVec 1) x)) " ^
             declaration ^
             "(define @ordinary () " ^ ordinary ^ ") " ^
             "(define @again () " ^ ordinary ^ ") " ^
             "(define @different () " ^ var (name ^ "'") ^ ") " ^
             "(define @identity () " ^ binder ^ ") " ^
             "(assume @p1 (= @private @private)) " ^
             "(assume @p2 (= @ordinary @again)) " ^
             "(assume @p3 (= @different @different)) " ^
             "(assume @p4 (= @identity @identity)))")
          fun equation (CPC_Proof.ASSUME (_, {term,...})) =
                boolSyntax.dest_eq term
            | equation _ = raise Fail "missing late ordinary ASSUME"
          val (marker, ordinary, different, abstraction) =
            case CPC_Proof.proof_commands proof of
              [first,second,third,fourth] =>
                let val (left,right) = equation second
                in require "repeated late descriptor changed identity"
                     (Term.aconv left right);
                   (reflexive_marker first,left,#1 (equation third),
                    #1 (equation fourth)) end
            | _ => raise Fail "wrong late descriptor command count"
          val _ = require "late collision fixture missed private name"
            (#1 (Term.dest_var marker) = name)
          val _ = require "later ordinary descriptor aliases private marker"
            (not (Term.aconv marker ordinary) andalso
             not (P.is_cpc_fp_private_marker ordinary))
          val _ = require "renamed ordinary aliases a later descriptor"
            (not (Term.aconv ordinary different) andalso
             not (P.is_cpc_fp_private_marker different))
          val (bound,body) = Term.dest_abs abstraction
        in require "late binder lost ordinary identity or binding"
             (Term.aconv bound ordinary andalso Term.aconv body ordinary
              andalso not (Term.free_in ordinary abstraction)) end
    in List.app check ["@var", "declaration", "binder"] end

  (* Same TASK19 construction as the resource tests: on the standard
     kernel, insert the shared residue lazily using a tiny Beta theorem.
     Never open, FVL, or structurally compare the resulting large binder. *)
  fun binder_source_freshness () =
    Timeout.apply (Time.fromSeconds 10) (fn () =>
      let
        val x = Term.mk_var ("task46_binder_source_x", Type.bool)
        val y = Term.mk_var ("task46_binder_source_y", Type.bool)
        fun shared 0 term = term
          | shared depth term =
              shared (depth - 1) (boolSyntax.mk_conj (term, term))
        val shared20 = shared 20 x
        val inserter = Term.mk_abs (x, Term.mk_abs (y, x))
        val large_binder =
          if Thm.kernelid = "expknl" then Term.mk_abs (y, shared20)
          else boolSyntax.rhs (Thm.concl (Thm.Beta (Thm.REFL
            (Term.mk_comb (inserter, shared20)))))
        val ordinary_text =
          "((step @p (= true true) :rule refl :args (true)))"
        val private_text =
          "((define @t1 () (@fp.INF (_ BitVec 1))) \
          \(assume @p1 (= @t1 @t1)))"
        fun ordinary () =
          let val proof = parse_cpc_proof_string ordinary_text in
            require "ordinary binder-source parse changed commands"
              (case CPC_Proof.proof_commands proof of
                 [CPC_Proof.STEP {id = "@p", conclusion = SOME {term, ...},
                    args = [{term = argument, ...}], premises = [], ...}] =>
                   Term.aconv term (boolSyntax.mk_eq
                     (boolSyntax.T, boolSyntax.T)) andalso
                   Term.aconv argument boolSyntax.T
               | _ => false);
            exact_registry ([], [])
          end
        val _ = P.with_cpc_fp_private_source_terms [large_binder]
          ordinary ()
        val expected = SmtResource.term_size_diagnostic_for
          "BitVector" "binder-opening"
          (SmtResource.max_bv_replay_term_nodes + 1)
        val outcome = Exn.capture
          (P.with_cpc_fp_private_source_terms [large_binder]
            (fn () => ignore (parse_cpc_proof_string private_text))) ()
        val _ = require "freshness bypassed the legacy binder-opening gate"
          (case outcome of
             Exn.Exn (Feedback.HOL_ERR detail) =>
               SmtResource.is_resource_gate detail andalso
               Feedback.top_function_of detail = "check_term_size" andalso
               Feedback.message_of detail = expected
           | _ => false)
        val _ = exact_registry ([], [])
        (* A successful allocation, not just an ordinary lazy parse, proves
           that the failed scope's source thunk was actually restored. *)
        val proof = parse_cpc_proof_string private_text
        val marker = case CPC_Proof.proof_commands proof of
            [command] => reflexive_marker command
          | _ => raise Fail "wrong post-binder-failure command count"
        val _ = exact_registry ([], [(marker, "@fp.INF")])
      in ordinary () end) ()

  (* The newer binding's operand contains the older private component.
     One simultaneous INST with unnormalized residues leaks the inner
     marker even though each replacement is individually well-typed. *)
  fun nested_explicit () =
    let
      val proof = parse_cpc_proof_string
        "((declare-const x (_ FloatingPoint 3 5)) \
        \(define @inner () (@fp.SIGN (_ BitVec 1) x)) \
        \(define @outer () \
        \  (@fp.SIGN (_ BitVec 1) (fp @inner #b000 #b0000))) \
        \(assume @p1 (= @outer @outer)))"
      val outer = case CPC_Proof.proof_commands proof of
          [command] => reflexive_marker command
        | _ => raise Fail "wrong nested marker fixture command count"
      val (outer_source, inner, inner_source) =
        case P.cpc_fp_private_bindings () of
          [{marker, kind = "@fp.SIGN", source = outer_source},
           {marker = inner, kind = "@fp.SIGN", source = inner_source}] =>
            (require "nested bindings are not newest first"
               (Term.aconv marker outer);
             (outer_source, inner, inner_source))
        | _ => raise Fail "wrong nested explicit binding registry"
      val _ = require "nested fixture has no inner marker in outer operand"
        (Term.free_in inner outer_source andalso
         null (P.cpc_fp_private_unbound_markers ()))
      fun sign source = ``(smtfp_rep ^source).Sign``
      val inner_replacement = sign inner_source
      val normalized_source = Term.subst
        [{redex = inner, residue = inner_replacement}] outer_source
      val replacement = sign normalized_source
      val expected = boolSyntax.mk_eq (replacement, replacement)
      val original = boolSyntax.mk_eq (outer, outer)
      val source = Thm.ASSUME original
      (* Independent sequential kernel substitution is the specification;
         do not use the production replacement builder as the oracle. *)
      val sequential = Thm.INST
        [{redex = inner, residue = inner_replacement}]
        (Thm.INST [{redex = outer, residue = sign outer_source}] source)
      val _ = exact expected [expected] sequential
      val theorem = R.discharge_private_fp_for_test source
      val _ = exact expected [] theorem
      val _ = no_private theorem
      val _ = exact original [original] source
      (* Isolate the input INST count from deferred-hypothesis proving. *)
      val (reflexive, statistics) = R.with_operation_statistics (fn () =>
        R.discharge_private_fp_for_test (Thm.REFL outer))
    in exact expected [] reflexive; no_private reflexive;
       require "nested explicit elimination did not use one input INST"
         (#inst_calls statistics = 1) end

  (* Exercise the normalization API without kernel INST or FP lowering:
     either would obscure whether the witness builder itself unfolds an
     actual shared operand. Count only bounded DAG observations, never the
     exponentially large printed term or an unfolded equality comparison. *)
  fun shared_witness_normalization dependent () =
    let
      val x = ``task46_shared_x : (3,5) smtfp``
      val y = ``task46_shared_y : (3,5) smtfp``
      val inner = Term.genvar ``:word1``
      val outer = Term.genvar ``:word1``
      val leaf = if dependent then
          ``smtfp_bits ^inner 0w 0w : (3,5) smtfp``
        else y
      val add = Term.rator (Term.rator ``smtfp_add RNE ^y ^y``)
      fun shared 0 = leaf
        | shared n = let val child = shared (n - 1)
                     in Term.mk_comb (Term.mk_comb (add, child), child) end
      val operand = shared 24
      val bindings : P.cpc_fp_private_binding list =
        [{marker=outer,kind="@fp.INF",source=operand},
         {marker=inner,kind="@fp.SIGN",source=x}]
      val substitutions = Timeout.apply (Time.fromSeconds 10)
        R.cpc_fp_private_substitutions bindings
      val (outer_image, inner_image) = case substitutions of
          [{redex=first,residue=left},{redex=second,residue=right}] =>
            (require "witness normalization reordered assignments"
               (Term.aconv first outer andalso Term.aconv second inner);
             (left, right))
        | _ => raise Fail "wrong shared witness substitution count"
      val _ = require "wrong older witness in shared normalization"
        (Term.aconv inner_image ``(smtfp_rep ^x).Sign``)
      val retained = ref false
      val remaining = ref false
      val additions = ref 0
      val normalized_leaf = ref false
      val expected_leaf = if dependent then
          ``smtfp_bits ^inner_image 0w 0w : (3,5) smtfp`` else y
      fun inspect term =
        (if Portable.pointer_eq (term, operand) then retained := true else ();
         if Term.is_var term andalso Term.aconv term inner then
           remaining := true else ();
         if Term.is_comb term andalso
            Term.aconv (Term.rator term) add then
           additions := !additions + 1 else ();
         (* Only compare at the constant-size leaf, not at shared roots. *)
         if Term.is_var term then
           (if Term.aconv term expected_leaf then normalized_leaf := true
            else ())
         else if Term.is_comb term then
           let val (head, arguments) = boolSyntax.strip_comb term in
             if Term.is_const head andalso
                #Name (Term.dest_thy_const head) = "smtfp_bits" andalso
                length arguments = 3 andalso Term.aconv term expected_leaf
             then normalized_leaf := true else ()
           end
         else ())
      val scan = SmtResource.bounded_structure_with_inspector inspect
        200 outer_image
    in
      require "shared witness normalization expanded the source DAG"
        (#complete scan andalso
         SmtResource.dag_nodes_up_to 200 outer_image <= 200);
      require "shared normalization lost its source or leaf"
        (!normalized_leaf andalso !additions = 24);
      require "shared normalization left an older marker" (not (!remaining));
      require "unrelated normalization rebuilt the original source"
        (dependent orelse !retained)
    end

  fun binder_witness_normalization () =
    let
      val x = ``task46_capture_x : (3,5) smtfp``
      val y = ``task46_capture_y : (3,5) smtfp``
      val inner = Term.genvar ``:word1``
      val outer = Term.genvar ``:word1``
      val bits = ``smtfp_bits ^inner 0w 0w : (3,5) smtfp``
      val image = ``(smtfp_rep ^x).Sign``
      fun normalized operand =
        case R.cpc_fp_private_substitutions
          [{marker=outer,kind="@fp.INF",source=operand},
           {marker=inner,kind="@fp.SIGN",source=x}] of
          [{redex=_,residue=result}, _] => result
        | _ => raise Fail "wrong binder witness substitution count"
      (* The older image introduces free x underneath a source binder x.
         Comparison is against an independently built, tiny expected term. *)
      val operand = Term.mk_comb (Term.mk_abs (x, bits), y)
      val fresh = Term.genvar (Term.type_of x)
      val expected = Term.mk_comb
        (Term.mk_abs (fresh,
          ``smtfp_bits ^image 0w 0w : (3,5) smtfp``), y)
      val _ = require "witness normalization captured a free source variable"
        (Term.aconv (normalized operand) (witness expected))
      (* An occurrence bound by the same descriptor is not a dependency. *)
      val shadowed = Term.mk_comb
        (Term.mk_abs (inner, bits), ``0w : word1``)
      val _ = require
        "witness normalization substituted a bound marker descriptor"
        (Term.aconv (normalized shadowed) (witness shadowed))
      (* The selected binder adapter admits full output before native
         closure. Check a shared image within the unchanged legacy bound;
         large application-only images have no such raw binder bound. *)
      val add = Term.rator (Term.rator ``smtfp_add RNE ^y ^y``)
      fun shared 0 = y
        | shared n = let val child = shared (n - 1)
                     in Term.mk_comb (Term.mk_comb (add, child), child) end
      val large = shared 8
      val bindings : P.cpc_fp_private_binding list =
        [{marker=outer,kind="@fp.INF",source=operand},
         {marker=inner,kind="@fp.SIGN",source=large}]
      val images = Timeout.apply (Time.fromSeconds 10)
        R.cpc_fp_private_substitutions bindings
      val (image, older) = case images of
          [{redex=_,residue=result},{redex=_,residue=older}] =>
            (result, older)
        | _ => raise Fail "missing binder-sharing witness"
      val retained = ref false
      val scan = SmtResource.bounded_structure_with_inspector
        (fn term => if Portable.pointer_eq (term, large) then
          retained := true else ()) 200 older
      (* The normalization timeout above is the binder cost assertion.
         Do NOT open its result to diagnose sharing: stock dest_abs itself
         unfolds a large raw body. Inspect that boundary opaquely. *)
      val has_binder = ref false
      val outer_scan = SmtResource.bounded_structure_with_children
        (fn term => if Term.is_comb term then
           let val (left,right) = Term.dest_comb term in [left,right] end
         else [])
        (fn term => if Term.is_abs term then has_binder := true else ())
        200 image
      val exhausted = Timeout.apply (Time.fromSeconds 10) (fn () =>
        Exn.capture R.cpc_fp_private_substitutions
          [{marker=outer,kind="@fp.INF",source=operand},
           {marker=inner,kind="@fp.SIGN",source=shared 20}]) ()
      val expected_diagnostic = SmtResource.term_size_diagnostic_for
        "BitVector" "binder-opening"
        (SmtResource.max_bv_replay_term_nodes + 1)
      val _ = require "binder output lost the legacy first diagnostic"
        (case exhausted of Exn.Exn (Feedback.HOL_ERR detail) =>
           SmtResource.is_resource_gate detail andalso
           Feedback.top_function_of detail = "check_term_size" andalso
           Feedback.message_of detail = expected_diagnostic
         | _ => false)
    in require "binder closing expanded an inserted shared witness"
         (#complete scan andalso !retained andalso
          #complete outer_scan andalso !has_binder) end

  fun unused_opaque_witness () =
    Timeout.apply (Time.fromSeconds 10) (fn () =>
      let
        val x = Term.mk_var ("task46_unused_x", Type.bool)
        val y = Term.mk_var ("task46_unused_y", Type.bool)
        fun shared 0 = x
          | shared n = let val child = shared (n - 1)
                       in boolSyntax.mk_conj (child,child) end
        val body = shared 24
        val binder = if Thm.kernelid = "expknl" then Term.mk_abs (y,body)
          else boolSyntax.rhs (Thm.concl (Thm.Beta (Thm.REFL
            (Term.mk_comb (Term.mk_abs (x,Term.mk_abs (y,x)),body)))))
        val unused = Term.genvar ``:word1``
        val used = Term.genvar ``:word1``
        val source = ``task46_used_x : (3,5) smtfp``
        (* An unused explicit operand need not even be a supported FP
           source: it must not be inspected or have a witness constructed. *)
        val bindings : P.cpc_fp_private_binding list =
          [{marker=unused,kind="@fp.SIGN",source=binder},
           {marker=used,kind="@fp.INF",source=source}]
        val theorem = R.instantiate_cpc_fp_private_bindings bindings
          (Thm.REFL used)
        val image = witness source
      in exact (boolSyntax.mk_eq (image,image)) [] theorem;
         exact boolSyntax.T []
           (R.instantiate_cpc_fp_private_bindings bindings boolTheory.TRUTH)
      end) ()

  (* Discovery, not just normalization, must respect a parsed private
     alias used as a binder. Its unused operand is correctly typed but
     cannot pass the raw binder-opening gate. This combines the previously
     separate shadowing and unused-opaque controls. *)
  fun bound_opaque_dependency () =
    Timeout.apply (Time.fromSeconds 30) (fn () =>
      let
        val fp = "(fp #b0 #b000 #b0000)"
        fun alias i = "@shared" ^ Int.toString i
        fun definitions 0 = "(define " ^ alias 0 ^ " () true) "
          | definitions n = definitions (n-1) ^ "(define " ^ alias n ^
              " () (and " ^ alias (n-1) ^ " " ^ alias (n-1) ^ ")) "
        val proof = parse_cpc_proof_string ("(" ^ definitions 21 ^
          "(define @y () (@var \"opaque_y\" Bool)) " ^
          "(define @huge () (forall (@list @y) " ^ alias 21 ^ ")) " ^
          "(define @inner () (@fp.SIGN (_ BitVec 1) " ^
            "(ite @huge " ^ fp ^ " " ^ fp ^ "))) " ^
          "(define @shadow () (forall (@list @inner) (= @inner @inner))) " ^
          "(define @outer () (@fp.INF (_ BitVec 1) " ^
            "(ite @shadow " ^ fp ^ " " ^ fp ^ "))) " ^
          "(assume @a (= @outer @outer)))")
        val outer = case CPC_Proof.proof_commands proof of
            [command] => reflexive_marker command
          | _ => raise Fail "wrong bound-dependency command count"
        val bindings = P.cpc_fp_private_bindings ()
        val needed = List.filter (fn {marker,...} =>
          Term.aconv marker outer) bindings
        val _ = require "bound dependency fixture lost a binding"
          (length bindings = 2 andalso length needed = 1)
        val reference = R.instantiate_cpc_fp_private_bindings needed
          (Thm.REFL outer)
        val theorem = R.instantiate_cpc_fp_private_bindings bindings
          (Thm.REFL outer)
        val _ = exact (Thm.concl reference) [] theorem
        (* Bound aliases in the actual input Goal/Hyp are not free either.
           No witness, normalization, or input INST is needed here. *)
        val inner = #marker (valOf (List.find (fn {marker,...} =>
          not (Term.aconv marker outer)) bindings))
        val closed = boolSyntax.mk_forall
          (inner,boolSyntax.mk_eq (inner,inner))
        val source = Thm.ASSUME closed
        val (unchanged,statistics) = R.with_operation_statistics (fn () =>
          R.instantiate_cpc_fp_private_bindings bindings source)
        (* The same operand MUST retain the original refusal when its
           marker really is free, rather than bound in the outer source. *)
        val refused = Exn.capture
          (R.instantiate_cpc_fp_private_bindings bindings) (Thm.REFL inner)
        val diagnostic = SmtResource.term_size_diagnostic_for
          "BitVector" "binder-opening"
          (SmtResource.max_bv_replay_term_nodes + 1)
      in exact closed [closed] unchanged;
         require "bound-only input caused a witness INST"
           (#inst_calls statistics = 0);
         require "required opaque dependency lost its original diagnostic"
           (case refused of Exn.Exn (Feedback.HOL_ERR detail) =>
              SmtResource.is_resource_gate detail andalso
              Feedback.top_function_of detail = "check_term_size" andalso
              Feedback.message_of detail = diagnostic
            | _ => false)
      end) ()

  (* An identical body can be reached both freely and under a shadowing
     binder. Neither visitation order may hide its free dependency; a
     different-typed namesake must not shadow it either. *)
  fun mixed_free_bound_dependencies () =
    let
      val inner = Term.genvar ``:word1``
      val outer = Term.genvar ``:word1``
      val x = ``task46_dependency_x : (3,5) smtfp``
      val bits = ``smtfp_bits ^inner 0w 0w : (3,5) smtfp``
      val shadowed = Term.mk_comb
        (Term.mk_abs (inner,bits), ``0w : word1``)
      val namesake = Term.mk_var (#1 (Term.dest_var inner),Type.bool)
      val typed = Term.mk_comb (Term.mk_abs (namesake,bits),boolSyntax.T)
      val nested = Term.mk_comb (Term.mk_abs (namesake,typed),boolSyntax.T)
      val add = Term.rator (Term.rator ``smtfp_add RNE ^x ^x``)
      fun check (left,right) =
        let
          val operand = Term.mk_comb (Term.mk_comb (add,left),right)
          val bindings : P.cpc_fp_private_binding list =
            [{marker=outer,kind="@fp.INF",source=operand},
             {marker=inner,kind="@fp.SIGN",source=x}]
          val image = ``(smtfp_rep ^x).Sign``
          val expected = witness (Term.subst
            [{redex=inner,residue=image}] operand)
          val theorem = R.instantiate_cpc_fp_private_bindings bindings
            (Thm.REFL outer)
          val hyp = boolSyntax.mk_eq (inner,inner)
          val source = Thm.CONJ (Thm.REFL outer) (Thm.ASSUME hyp)
          val expected_hyp = boolSyntax.mk_eq (image,image)
          val result = R.instantiate_cpc_fp_private_bindings bindings source
        in exact (boolSyntax.mk_eq (expected,expected)) [] theorem;
           exact (boolSyntax.mk_conj
             (boolSyntax.mk_eq (expected,expected),expected_hyp))
             [expected_hyp] result
        end
    in List.app check [(shadowed,bits),(bits,shadowed),
         (shadowed,typed),(shadowed,nested)] end

  fun bound_alias_names () =
    Timeout.apply (Time.fromSeconds 10) (fn () =>
      let
        val first = Term.mk_var ("task46_bound",``:word1``)
        val second = Term.mk_var ("task46_bound'",``:word1``)
        val free = Term.mk_var ("task46_bound''",Type.bool)
        val x = ``task46_dependency_x : (3,5) smtfp``
        val bindings : P.cpc_fp_private_binding list =
          [{marker=first,kind="@fp.SIGN",source=x},
           {marker=second,kind="@fp.SIGN",source=x}]
        fun wide 0 index =
              Term.mk_var ("task46_wide" ^ Int.toString index,Type.bool)
          | wide n index = boolSyntax.mk_conj
              (wide (n-1) (2*index),wide (n-1) (2*index+1))
        val body = boolSyntax.mk_conj
          (boolSyntax.mk_eq (first,first),boolSyntax.mk_conj
            (boolSyntax.mk_forall (second,
               boolSyntax.mk_eq (second,second)),
             boolSyntax.mk_conj (free,wide 11 0)))
        val goal = boolSyntax.mk_forall (first,body)
        val source = Thm.ASSUME goal
        val (theorem,statistics) = R.with_operation_statistics (fn () =>
          R.instantiate_cpc_fp_private_bindings bindings source)
      in exact goal [goal] theorem;
         require "alpha-opening selected an apostrophized declaration"
           (#inst_calls statistics = 0)
      end) ()

  fun bound_alias_sharing () =
    Timeout.apply (Time.fromSeconds 15) (fn () =>
      let
        val marker = Term.genvar ``:word1``
        val leaf = boolSyntax.mk_eq (marker,marker)
        fun shared 0 = leaf
          | shared n = let val child = shared (n-1)
                       in boolSyntax.mk_conj (child,child) end
        (* Standard dest_abs itself unfolds, so its original DAG admission
           has a smaller supported range. Experimental dest_abs retains
           this shared body; alpha-renaming it must not change admission. *)
        val depth = if Thm.kernelid = "expknl" then 17 else 10
        val goal = boolSyntax.mk_forall (marker,shared depth)
        val bindings : P.cpc_fp_private_binding list =
          [{marker=marker,kind="@fp.SIGN",
            source=``task46_dependency_x : (3,5) smtfp``}]
        val scan = SmtResource.bounded_structure
          SmtResource.max_bitblast_term_nodes goal
        val _ = require "shared binder fixture exceeds original admission"
          (#complete scan)
        val source = Thm.ASSUME goal
        val (theorem,statistics) = R.with_operation_statistics (fn () =>
          R.instantiate_cpc_fp_private_bindings bindings source)
      in exact goal [goal] theorem;
         require "shared bound alias selected its unused witness"
           (#inst_calls statistics = 0)
      end) ()

  fun raw_self () =
    let val target = ``task46_deferred_p:bool``
        val raw = Thm.ASSUME target
        val _ = exact target [target] raw
        val theorem = R.discharge_deferred_for_test [] [raw] raw
    in exact target [target] theorem end

  fun dependency_cycle () =
    let
      val first = ``task46_deferred_p:bool``
      val second = boolSyntax.mk_conj (first, boolSyntax.T)
      val forward = Thm.CONJUNCT1 (Thm.ASSUME second)
      val backward = Thm.CONJ (Thm.ASSUME first) boolTheory.TRUTH
      val _ = require "cycle collapsed to raw self"
        (not (Term.aconv first second))
      (* Both non-self edges are valid kernel theorems with REAL Hyp. *)
      val _ = exact first [second] forward
      val _ = exact second [first] backward
      val source = Thm.CONJ (Thm.ASSUME first) (Thm.ASSUME second)
      val theorem = R.discharge_deferred_for_test []
        [forward, backward] source
    in exact (boolSyntax.mk_conj (first, second))
         [first, second] theorem end

  fun acyclic_dependencies () =
    let
      val left = ``task46_deferred_p:bool``
      val right = ``task46_deferred_q:bool``
      val shared = boolSyntax.mk_conj (left, right)
      val original = boolSyntax.mk_conj (shared, boolSyntax.T)
      val left_proof = Thm.CONJUNCT1 (Thm.ASSUME shared)
      val right_proof = Thm.CONJUNCT2 (Thm.ASSUME shared)
      val shared_proof = Thm.CONJUNCT1 (Thm.ASSUME original)
      val _ = exact left [shared] left_proof
      val _ = exact right [shared] right_proof
      val _ = exact shared [original] shared_proof
      (* Ordinary cache lookup cannot return either endpoint: shared is NOT
         an allowed Source.  Dependency closure must close it independently;
         the second endpoint then reuses the same dependency memo. *)
      val source = Thm.CONJ (Thm.ASSUME left) (Thm.ASSUME right)
      val _ = exact shared [left, right] source
      val theorem = R.discharge_deferred_for_test [original]
        [left_proof, right_proof, shared_proof] source
    in exact shared [original] theorem end

  (* Projecting F must retain BOTH trust bridges in the actual kernel Hyp:
     and_intro uses CONJ, whose hypothesis union survives and_elim. Neither
     a syntactic root-F check nor a stand-alone bridge test closes this
     proof. *)
  fun full_private explicit () : unit =
    let
      fun operand name = if explicit then " " ^ name else ""
      val proof = parse_cpc_proof_string
        ("((declare-const x0 (_ FloatingPoint 3 5)) " ^
         "(declare-const x1 (_ FloatingPoint 3 5)) " ^
         "(define @b0 () (= (fp.isInfinite x0) " ^
         "  (= #b1 (@fp.INF (_ BitVec 1)" ^ operand "x0" ^ ")))) " ^
         "(define @b1 () (= (fp.isInfinite x1) " ^
         "  (= #b1 (@fp.INF (_ BitVec 1)" ^ operand "x1" ^ ")))) " ^
         "(assume @denied false) " ^
         "(step @bridge0 :rule trust :args (@b0)) " ^
         "(step @bridge1 :rule trust :args (@b1)) " ^
         "(step @pair (and false @b0 @b1) :rule and_intro " ^
         "  :premises (@denied @bridge0 @bridge1)) " ^
         "(step @done false :rule and_elim " ^
         "  :premises (@pair) :args (0)))")
      val (left, right, pair) = case CPC_Proof.proof_commands proof of
          [CPC_Proof.ASSUME ("@denied", _),
           CPC_Proof.STEP {id = "@bridge0", args = [left], ...},
           CPC_Proof.STEP {id = "@bridge1", args = [right], ...},
           CPC_Proof.STEP {id = "@pair", conclusion = SOME pair, ...},
           CPC_Proof.STEP {id = "@done", ...}] => (left, right, pair)
        | _ => raise Fail "wrong complete private certificate commands"
      fun expected name ({term, provenance} : CPC_Proof.located_term) =
        let
          val source = Term.rand (boolSyntax.lhs term)
          val marker = boolSyntax.rhs (boolSyntax.rhs term)
          val _ = require "complete bridge did not expand definition"
            (case provenance of CPC_Proof.EqualityProvenance _ => true
             | _ => false)
          val _ = require "complete bridge lost allocated marker"
            (P.is_cpc_fp_private_marker marker)
        in bridge (Term.mk_var (name, Term.type_of source)) marker end
      val b0 = expected "x0" left
      val b1 = expected "x1" right
      val _ = require "complete bridge has wrong expanded body"
        (Term.aconv (#term left) b0 andalso Term.aconv (#term right) b1)
      val _ = require "complete pair lost expanded definition provenance"
        (Term.aconv (#term pair)
           (boolSyntax.list_mk_conj [boolSyntax.F, b0, b1]) andalso
         #provenance pair = CPC_Proof.ConjunctionProvenance
           (CPC_Proof.ParsedConjunction,
            [CPC_Proof.AtomicProvenance,
             #provenance left, #provenance right]))
      val (bindings, unbound) = registry ()
      val _ = require "wrong complete private marker class/count"
        (if explicit then length bindings = 2 andalso null unbound
         else null bindings andalso length unbound = 2)
      (* Parse B before replay/check A: the public path must restore A's
         private authority, then restore B's ambient registry on return. *)
      val unrelated = retained_fixture "task46_full_unrelated"
      val saved_b = registry ()
      val raw = R.replay_root_for_test proof
      val _ = exact boolSyntax.F [boolSyntax.F, b0, b1] raw
      val _ = exact_registry saved_b
      val checked = R.check_proof ([], boolSyntax.T, proof)
      val _ = exact boolSyntax.F [boolSyntax.mk_neg boolSyntax.T] checked
      val _ = no_private checked
      val _ = exact_registry saved_b
      val theorem = Thm.CCONTR boolSyntax.T checked
      val _ = exact boolSyntax.T [] theorem
      val _ = no_private theorem
      (* The source theorem is immutable; closure must not erase its Hyp. *)
      val _ = exact boolSyntax.F [boolSyntax.F, b0, b1] raw
    in ignore (CPC_Proof.proof_commands unrelated) end

  fun run () =
    (test "CPC real two-marker checked FP infinity bridges" two_markers;
     test "CPC false private FP bridge rejects checked assignment"
       false_bridge;
     test "CPC unanchored private component cannot close" unanchored_leak;
     test "CPC checked private bridge cannot erase a foreign Hyp"
       foreign_hypothesis;
     test "CPC ordinary source-looking variable remains unchanged"
       source_looking_variable;
     test "CPC explicit private FP bridge closes" explicit_positive;
     test "CPC unbound marker excluded from original Source"
       (source_exclusion false);
     test "CPC explicit marker excluded before instantiation"
       (source_exclusion true);
     test "CPC mixed explicit/unbound checked marker elimination"
       mixed_markers;
     test "CPC parse A/parse B/GC/replay A restores exact private scopes"
       retained_registry;
     test "CPC private allocation avoids colliding original source names"
       source_name_collision;
     test "CPC shared source freshness stays lazy and DAG-linear"
       shared_source_freshness;
     test "CPC parsed @var and binder atoms cannot alias private markers"
       parsed_source_freshness;
     test "CPC later ordinary declarations and binders remain disjoint"
       later_source_freshness;
     test "CPC source freshness retains lazy legacy binder-opening gate"
       binder_source_freshness;
     test "CPC nested explicit replacements normalize before one input INST"
       nested_explicit;
     test "CPC unrelated private witness retains the actual shared operand"
       (shared_witness_normalization false);
     test "CPC nested private witness preserves dependency DAG sharing"
       (shared_witness_normalization true);
     test "CPC witness binders preserve capture/shadowing and shared images"
       binder_witness_normalization;
     test "CPC unused opaque witness is pruned before normalization"
       unused_opaque_witness;
     test "CPC bound private alias does not open its unused opaque operand"
       bound_opaque_dependency;
     test "CPC mixed free/bound dependencies preserve Goal/Hyp and types"
       mixed_free_bound_dependencies;
     test "CPC bound-alias opening avoids declaration/free names and width"
       bound_alias_names;
     test "CPC bound-alias discovery preserves original shared DAG admission"
       bound_alias_sharing;
     test "CPC raw-self deferred cache entry remains unclosed" raw_self;
     test "CPC genuine two-step deferred dependency cycle remains unclosed"
       dependency_cycle;
     test "CPC acyclic checked cached dependencies preserve actual Hyp/tags"
       acyclic_dependencies;
     test "CPC complete legacy unbound FP bridges close through check_proof"
       (full_private false);
     test "CPC complete legacy explicit FP bridges close through check_proof"
       (full_private true))
end
