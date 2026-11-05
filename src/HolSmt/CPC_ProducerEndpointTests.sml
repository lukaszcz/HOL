(* Producer-owned endpoint retention: a small checked schema must keep its
   large opaque operands, without enlarging TRANS's physical-DAG allowance. *)
structure CPC_ProducerEndpointTests =
struct
  open HolKernel
  structure R = CPC_ProofReplay
  structure Q = CPC_ProofParser
  fun require message yes = if yes then () else raise Fail message
  fun clean theorem =
    require "unexpected proof tags"
      (null (Tag.axioms_of (Thm.tag theorem)) andalso
       List.all (fn name => name = "DISK_THM")
         (#1 (Tag.dest_tag (Thm.tag theorem))))
  (* Flush BEFORE each operation: a timeout must identify the unfinished
     phase, including setup that precedes the first assertion. These times
     are diagnostic only; they neither grant work nor change any quota. *)
  fun phase label action =
    let
      fun report state =
        (print ("CPC endpoint " ^ state ^ " " ^ label ^ "\n");
         TextIO.flushOut TextIO.stdOut)
      val _ = report "begin"
      val timer = Timer.startRealTimer ()
      val outcome = Exn.capture action ()
      val state = case outcome of Exn.Res _ => "done" | Exn.Exn _ => "failed"
      val _ = report (state ^ " (" ^
        Time.toString (Timer.checkRealTimer timer) ^ "s)")
    in
      case outcome of Exn.Res result => result | Exn.Exn error => raise error
    end
  fun actual_hyp hypotheses theorem =
    (require "wrong actual Hyp" (HOLset.equal
       (Thm.hypset theorem,HOLset.addList (Term.empty_tmset,hypotheses)));
     clean theorem)
  fun exact expected hypotheses theorem =
    phase "exact theorem comparison" (fn () =>
      (require "wrong conclusion" (Term.aconv (Thm.concl theorem) expected);
       actual_hyp hypotheses theorem))
  fun same label actual expected = require label
    (Portable.pointer_eq (actual,expected))
  fun large_operand () =
    let
      fun tree 0 index = Term.mk_var
            ("task57_endpoint_" ^ Int.toString index,Type.bool)
        | tree depth index = boolSyntax.mk_conj
            (tree (depth-1) (2*index),tree (depth-1) (2*index+1))
      (* Distinct leaves are intentional. Interning must not collapse a
         repeated balanced tree into a tiny DAG. With a shared conjunction
         constant this has 4096 leaves + 8190 applications + 1 constant;
         its unfolded tree has only 16381 nodes, not exponential sharing. *)
      val raw = phase "construct tree12" (fn () => tree 12 0)
    in phase "intern tree12" (fn () => Q.intern_cpc_term raw) end
  fun shared_operand () =
    phase "construct uninterned shared depth45" (fn () =>
      let
        (* Seed only the tiny canonical leaf, then create a distinct equal
           occurrence. Recursive interning of the graph would replace this
           leaf and unfold 2^45 paths. Never intern this graph, even during
           setup; each caller gets a fresh fixture, not a warmed cache. *)
        val canonical = Q.intern_cpc_term (Term.genvar Type.bool)
        val leaf = Term.mk_var (Term.dest_var canonical)
        val _ = require "shared fixture leaf is already canonical"
          (not (Portable.pointer_eq (leaf,canonical)))
        val _ = require "shared fixture leaves differ"
          (Term.aconv leaf canonical)
        fun grow 0 child = child
          | grow depth child =
              grow (depth-1) (boolSyntax.mk_conj (child,child))
        val operand = grow 45 leaf
        val _ = require "shared fixture is not a small physical DAG"
          (SmtResource.dag_nodes_up_to 1000 operand < 1000)
      in operand end)
  fun test label action =
    (testutils.tprint label;TextIO.flushOut TextIO.stdOut;
     action ();testutils.OK ())
  fun fp_shared_substitution () =
    let
      val source = Term.genvar Type.bool
      val residue = Term.genvar Type.bool
      fun grow 0 term = term
        | grow n term = grow (n-1) (boolSyntax.mk_conj (term,term))
      val input = grow 45 source
      val result = R.cpc_fp_term_substitution
        [{redex=source,residue=residue}] input
      fun inspect 0 term = same "FP substitution lost its exact residue"
            term residue
        | inspect n term =
            let val (left,right) = boolSyntax.dest_conj term in
              same "FP substitution unfolded a shared application" left right;
              inspect (n-1) left
            end
      val _ = inspect 45 result
      val bound = Term.genvar Type.bool
      val scoped = Term.mk_comb
        (Term.mk_abs (bound,boolSyntax.mk_conj (bound,source)),boolSyntax.T)
      val substitutions = [{redex=source,residue=residue}]
      val actual = R.cpc_fp_term_substitution substitutions scoped
      val expected = Term.subst substitutions scoped
      val _ = require "FP substitution changed scoped syntax"
        (Term.aconv actual expected)
    in require "FP substitution expanded its physical DAG"
      (SmtResource.dag_nodes_up_to 1000 result < 1000) end
  fun fp_circuit_alias () =
    let
      val left = Term.genvar Type.bool
      val right = Term.mk_var (Term.dest_var left)
      fun grow 0 term = term
        | grow n term = grow (n-1) (boolSyntax.mk_conj (term,term))
      val operands = (grow 45 left,grow 45 right)
      val equality = boolSyntax.mk_eq operands
      fun check goal =
        let
          val theorem = Timeout.apply
            SmtResource.max_hypothesis_entailment_time
            R.prove_boolean_circuit goal
          val _ = same "FP circuit lost its exact source goal"
            (Thm.concl theorem) goal
        in actual_hyp [] theorem end
      val independent = Term.genvar Type.bool
      val false_goal = boolSyntax.mk_eq
        (grow 45 left,grow 45 independent)
      val _ =
        ((Timeout.apply SmtResource.max_hypothesis_entailment_time
            R.prove_boolean_circuit false_goal;
          raise Fail "FP circuit published a countermodel as a proof")
         handle HolSatLib.SAT_satisfiable _ => ())
    in List.app check
      [boolSyntax.mk_imp operands,equality,
       boolSyntax.mk_imp (boolSyntax.T,equality)] end
  fun fp_source_occurrences () =
    let
      val fp_type = Parse.Type [QUOTE ":(4,3) smtfp"]
      val source = Term.genvar fp_type
      (* An equal but physically distinct occurrence must not be renamed
         either. Native comparison of the independent depth135 shells would
         unfold exponentially if producer endpoints were not retained. *)
      val alias = Term.mk_var (Term.dest_var source)
      val independent = Term.genvar fp_type
      fun atom operand =
        let
          val predicate = Term.prim_mk_const
            {Thy="smtfloat",Name="smtfp_is_nan"}
          val (domain,_) = Type.dom_rng (Term.type_of predicate)
        in Term.mk_comb
          (Term.inst (Type.match_type domain fp_type) predicate,operand) end
      fun grow 0 term = term
        | grow n term = grow (n-1) (boolSyntax.mk_conj (term,term))
      val left = grow 135 (atom source)
      fun goal operand = boolSyntax.mk_eq (left,grow 135 (atom operand))
      val target = goal alias
      val observed = ref false
      fun observe schema =
        (same "FP bridge renamed an already opaque source occurrence"
           schema target;
         observed := true)
      val theorem = R.with_private_fp_bridge_observer_for_test observe
        (fn () =>
          case Timeout.apply SmtResource.max_hypothesis_entailment_time
              R.try_private_fp_bridge_for_test target of
            SOME theorem => theorem
          | NONE => raise Fail "equal FP source occurrences rejected")
      val _ = require "FP source occurrence bridge was bypassed" (!observed)
      val _ = same "FP bridge lost the actual source goal"
        (Thm.concl theorem) target
      val _ = actual_hyp [] theorem
    in
      case Timeout.apply SmtResource.max_hypothesis_entailment_time
          R.try_private_fp_bridge_for_test (goal independent) of
        NONE => ()
      | SOME _ => raise Fail "independent FP sources were identified"
    end
  fun fp_choice_source_law () =
    let
      val fp_type = Parse.Type [QUOTE ":(4,3) smtfp"]
      val source = Term.genvar fp_type
      val predicate = Term.prim_mk_const
        {Thy="smtfloat",Name="smtfp_is_nan"}
      val (domain,_) = Type.dom_rng (Term.type_of predicate)
      val atom = Term.mk_comb
        (Term.inst (Type.match_type domain fp_type) predicate,source)
      (* Only use the small law's formula to construct the test goal. The
         bridge must independently reconstruct its checked theorem. *)
      val formula = Thm.concl (SmtFpGraph.convert_atom atom)
      fun tree 0 n = Term.mk_var
            ("task57_choice_" ^ Int.toString n,Type.bool)
        | tree depth n = boolSyntax.mk_conj
            (tree (depth-1) (2*n),tree (depth-1) (2*n+1))
      val choice = boolSyntax.mk_select (Term.genvar fp_type,tree 9 0)
      val target = Term.subst [{redex=source,residue=choice}] formula
      val observed = ref false
      fun observe schema =
        (require "choice source body escaped into its local FP schema"
           (not (SmtResource.contains Term.is_abs schema));
         observed := true)
      val theorem = R.with_private_fp_bridge_observer_for_test observe
        (fn () =>
          case Timeout.apply SmtResource.max_hypothesis_entailment_time
              R.try_private_fp_bridge_for_test target of
            SOME theorem => theorem
          | NONE => raise Fail "valid opaque choice bridge rejected")
      val _ = require "choice bridge was bypassed" (!observed)
      val _ = same "choice bridge lost its actual source endpoint"
        (Thm.concl theorem) target
    in actual_hyp [] theorem end
  fun word_opaque_source_guard () =
    let
      val binder = Term.genvar Type.bool
      val atom = Term.genvar Type.bool
      val body = boolSyntax.mk_neg (boolSyntax.mk_neg atom)
      val source = boolSyntax.mk_select (binder,body)
      (* Equal syntax is not an exact occurrence stop. The second choice
         must still be normalized, even beside a stopped first occurrence. *)
      val other = boolSyntax.mk_select (binder,body)
      val _ = require "choice fixture accidentally shares its root"
        (not (Portable.pointer_eq (source,other)))
      val root = boolSyntax.mk_conj (source,other)
      val stopped_callbacks = ref 0
      fun conversion term =
        (if Portable.pointer_eq (term,source) then
           stopped_callbacks := !stopped_callbacks + 1 else ();
         Conv.FIRST_CONV (List.map Conv.REWR_CONV
           (Drule.CONJUNCTS boolTheory.NOT_CLAUSES)) term
           handle Feedback.HOL_ERR _ => raise Conv.UNCHANGED)
      val (theorem,metrics) =
        SmtWordGraph.normalize_with_node_conversion_stopping_and_metrics
          [source] conversion root
      val (left,right) = boolSyntax.dest_conj
        (boolSyntax.rhs (Thm.concl theorem))
      val _ = same "opaque word source was rebuilt" left source
      val _ = require "equal non-stopped choice was not normalized"
        (Term.aconv right (boolSyntax.mk_select (binder,atom)))
      val _ = require "opaque word source reached the callback"
        (!stopped_callbacks = 0)
      val _ = require "opaque stop hid original input metric"
        (#input_nodes metrics = SmtResource.dag_nodes_up_to
          SmtResource.max_skeleton_replay_dag_nodes root)
      val _ = same "opaque normalization lost original endpoint"
        (boolSyntax.lhs (Thm.concl theorem)) root
      val _ = actual_hyp [] theorem
      val _ = ignore (SmtWordGraph.normalize_with_node_conversion
        conversion source)
      val _ = require "old word adapter acquired an implicit stop"
        (!stopped_callbacks > 0)
      val oversized = large_operand ()
      val called = ref false
      fun forbidden _ = (called := true; raise Fail "callback before guard")
      val _ = case Exn.capture
          (SmtWordGraph.normalize_with_node_conversion_stopping
            [oversized] forbidden) oversized of
        Exn.Exn (Feedback.HOL_ERR error) =>
          require "opaque stop bypassed original input guard"
            (not (!called) andalso SmtResource.is_resource_gate error andalso
             String.isSubstring "word-graph-input"
               (Feedback.message_of error))
      | _ => raise Fail "oversized stopped source admitted"
      (* A separate graph boundary retains actual data before importing its
         operator program. This does NOT relax the term adapter's guard. *)
      val zero = Parse.Term [QUOTE "0w:word1"]
      val choice = boolSyntax.mk_select
        (Term.genvar (Term.type_of zero),oversized)
      val input = wordsSyntax.mk_word_add (choice,zero)
      val theorem =
        SmtWordGraph.normalize_retaining_sources_with_node_conversion
          [choice] conversion input
      val _ = same "retained word law lost its original left endpoint"
        (boolSyntax.lhs (Thm.concl theorem)) input
      val _ = same "retained word law descended into choice data"
        (boolSyntax.rhs (Thm.concl theorem)) choice
    in actual_hyp [] theorem end
  fun opaque_rounding_circuit () =
    let
      val formula = Parse.Term
        [QUOTE "(case smtfp_unpack_rounding (smtfp_pack_rounding mode) of\n\
          \ RNE => T | RNA => F | RTP => F | RTN => F | RTZ => F) =\n\
          \ (mode = RNE)"]
      val mode_type = Parse.Type [QUOTE ":smt_rounding"]
      val mode = Term.mk_var ("mode",mode_type)
      val source = boolSyntax.mk_select
        (Term.genvar mode_type,Term.genvar Type.bool)
      val independent = Term.genvar mode_type
      val target = Term.subst [{redex=mode,residue=source}] formula
      val theorem = R.prove_boolean_circuit_stopping_for_test [source] target
      val _ = exact target [] theorem
      val data = large_operand ()
      val first = boolSyntax.mk_select (Term.genvar mode_type,data)
      val second = boolSyntax.mk_select (Term.genvar mode_type,data)
      val constructor = boolSyntax.rhs (boolSyntax.rhs target)
      val alias_goal = boolSyntax.mk_eq
        (boolSyntax.mk_eq (first,constructor),
         boolSyntax.mk_eq (second,constructor))
      val _ = require "opaque alias fixture reused a binder pointer"
        (not (Portable.pointer_eq (Term.rand first,Term.rand second)))
      val alias_proof = R.prove_boolean_circuit_stopping_for_test
        [first,second] alias_goal
      val _ = exact alias_goal [] alias_proof
      val wrong = boolSyntax.mk_eq
        (boolSyntax.lhs target,Term.subst
          [{redex=source,residue=independent}] (boolSyntax.rhs target))
    in
      case Exn.capture
          (R.prove_boolean_circuit_stopping_for_test [source,independent])
          wrong of
        Exn.Exn (HolSatLib.SAT_satisfiable _) => ()
      | _ => raise Fail "independent opaque rounding mode was accepted"
    end
  fun fp_word_choice_source () =
    let
      val fp_type = Parse.Type [QUOTE ":(4,3) smtfp"]
      val variable = Term.genvar fp_type
      fun tree 0 n = Term.mk_var
            ("task57_word_choice_" ^ Int.toString n,Type.bool)
        | tree depth n = boolSyntax.mk_conj
            (tree (depth-1) (2*n),tree (depth-1) (2*n+1))
      val choice = boolSyntax.mk_select
        (Term.genvar fp_type,tree 12 0)
      val sum = Parse.Term
        [QUOTE "smtfp_add RNE (x:(4,3) smtfp) x"]
      val source = Term.subst
        [{redex=Term.mk_var ("x",fp_type),residue=choice}] sum
      val base = Drule.ISPECL [variable] (Drule.GEN_ALL
        smtfloatReplayRoundingTheory.smtfp_rep_canonical_fields)
      val beta = Conv.QCONV (Conv.TOP_DEPTH_CONV
        (Conv.FIRST_CONV
          [Conv.REWR_CONV boolTheory.LET_THM,Thm.BETA_CONV]))
        (Thm.concl base)
      val formula = Term.subst [{redex=variable,residue=source}]
        (boolSyntax.rhs (Thm.concl beta))
      (* Native INST can leave independently allocated alpha-equal source
         occurrences. Reproduce that DATA shape without changing the goal. *)
      val formula = Term.subst
        [{redex=Term.genvar Type.bool,residue=boolSyntax.T}] formula
      val zero = Parse.Term [QUOTE "0w:word1"]
      val one = Parse.Term [QUOTE "1w:word1"]
      val target = boolSyntax.mk_eq
        (one,boolSyntax.mk_cond (formula,one,zero))
      val theorem = Timeout.apply
        SmtResource.max_hypothesis_entailment_time
        R.replay_trust_for_test target
    in exact target [] theorem end
  fun fp_bridge_sequent_substitution () =
    let
      val marker = Term.genvar Type.bool
      val actual = Term.genvar Type.bool
      val parameter = Term.genvar Type.bool
      fun grow 0 term = term
        | grow n term = grow (n-1) (boolSyntax.mk_conj (term,term))
      fun prove 0 theorem = theorem
        | prove n theorem = prove (n-1) (Thm.CONJ theorem theorem)
      val bridge = grow 135 (boolSyntax.mk_eq (marker,marker))
      val proof = prove 135 (Thm.REFL actual)
      val negative = boolSyntax.mk_neg parameter
      val original = Drule.ADD_ASSUM bridge
        (Thm.MP (Thm.NOT_ELIM (Thm.ASSUME negative))
          (Thm.ASSUME parameter))
      val theorem = Timeout.apply
        SmtResource.max_hypothesis_entailment_time
        (fn () => R.instantiate_cpc_fp_bridge_instances_for_test
          [{redex=marker,residue=actual}] [(bridge,proof)] original) ()
      val _ = exact boolSyntax.F [parameter,negative] theorem
    in
      case Exn.capture (fn () =>
          R.instantiate_cpc_fp_bridge_instances_for_test
            [{redex=marker,residue=actual}]
            [(bridge,Thm.REFL actual)] original) () of
        Exn.Exn (Feedback.HOL_ERR _) => ()
      | _ => raise Fail "unrelated private bridge instance was accepted"
    end
  fun fp_first_resource_gate () =
    let
      val fp_type = Parse.Type [QUOTE ":(4,3) smtfp"]
      val source = Term.genvar fp_type
      val predicate = Term.prim_mk_const
        {Thy="smtfloat",Name="smtfp_is_nan"}
      val (domain,_) = Type.dom_rng (Term.type_of predicate)
      val atom = Term.mk_comb
        (Term.inst (Type.match_type domain fp_type) predicate,source)
      fun grow 0 term = term
        | grow n term = grow (n-1) (boolSyntax.mk_conj (term,term))
      val target = boolSyntax.mk_eq (grow 135 atom,grow 135 atom)
      val maximum = SmtResource.max_skeleton_replay_dag_nodes
      fun refuse _ = SmtResource.check_dag_size_with_limit "Skeleton"
        "task57-fp-first-gate" maximum (maximum+1)
      val _ = require "FP bridge timeout cap changed"
        (Time.compare (SmtResource.max_hypothesis_entailment_time,
           Time.fromSeconds 10) = EQUAL)
    in
      case Exn.capture (fn () =>
          R.with_private_fp_bridge_observer_for_test refuse (fn () =>
            R.try_private_fp_bridge_for_test target)) () of
        Exn.Exn (Feedback.HOL_ERR error) =>
          require "FP fallback replaced the first resource diagnostic"
            (SmtResource.is_resource_gate error andalso
             String.isSubstring "task57-fp-first-gate"
               (Feedback.message_of error))
      | _ => raise Fail "FP resource gate published or deferred a proof"
    end
  fun fp_encoding_source_cut () =
    let
      val fp_type = Parse.Type [QUOTE ":(4,3) smtfp"]
      fun tree 0 name = Term.mk_var (name,Type.bool)
        | tree depth name = boolSyntax.mk_conj
            (tree (depth-1) (name ^ "l"),tree (depth-1) (name ^ "r"))
      fun source name = boolSyntax.mk_select
        (Term.mk_var (name,fp_type),tree 7 (name ^ "_predicate"))
      val left = source "task57_fp_cut_left"
      val right = source "task57_fp_cut_right"
      fun app theory name arguments = List.foldl
        (fn (argument,function) =>
          let
            val (domain,_) = Type.dom_rng (Term.type_of function)
          in Term.mk_comb
            (Term.inst (Type.match_type domain (Term.type_of argument))
              function,argument) end)
        (Term.prim_mk_const {Thy=theory,Name=name}) arguments
      val mode = Term.mk_var ("task57_fp_cut_mode",
        Type.mk_thy_type {Thy="smtfloat",Tyop="smt_rounding",Args=[]})
      val sum = app "smtfloat" "smtfp_add" [mode,left,left]
      val atom = app "smtfloat" "smtfp_is_nan" [sum]
      val representation = app "smtfloat" "smtfp_rep" [right]
      val sign = app "binary_ieee" "recordtype.float.seldef.Sign"
        [representation]
      val zero = Parse.Term [QUOTE "0w:word1"]
      val target = boolSyntax.mk_eq (atom,boolSyntax.mk_eq (sign,zero))
      exception Captured
      fun observe schema =
        (require "FP encoding-only source was opened or left concrete"
           (not (SmtResource.contains Term.is_abs schema));
         require "FP encoding-only source was not a separate parameter"
           (List.length (List.filter (fn variable =>
             Type.compare (Term.type_of variable,fp_type) = EQUAL)
             (Term.free_vars schema)) = 2);
         raise Captured)
      val concrete = Term.subst [{redex=mode,residue=
        Term.prim_mk_const {Thy="smtfloat",Name="RNE"}}] target
    in
      (case Exn.capture (fn () =>
        R.with_private_fp_bridge_observer_for_test observe (fn () =>
          Timeout.apply SmtResource.max_hypothesis_entailment_time
            R.replay_trust_for_test target)) () of
         Exn.Exn Captured => ()
       | Exn.Exn error => raise error
       | _ => raise Fail "FP producer schema observer was not reached");
      case Timeout.apply SmtResource.max_hypothesis_entailment_time
          R.try_private_fp_bridge_for_test concrete of
        NONE => ()
      | SOME _ => raise Fail "invalid FP binding published a theorem"
    end
  fun run () =
    let
      val operand = large_operand ()
      val quota = SmtResource.max_skeleton_replay_dag_nodes
      val _ = phase "physical quota check" (fn () =>
        let val nodes = SmtResource.dag_nodes_up_to quota operand
        in
          print ("CPC endpoint bounded physical nodes=" ^
            Int.toString nodes ^ " quota=" ^ Int.toString quota ^ "\n");
          require "fixture no longer exceeds original physical quota"
            (nodes > quota)
        end)
      val (true_operand,operand_true) = phase "intern endpoint shells"
        (fn () =>
          (Q.intern_cpc_term (boolSyntax.mk_eq (boolSyntax.T,operand)),
           Q.intern_cpc_term (boolSyntax.mk_eq (operand,boolSyntax.T))))
      val (one,zero) = phase "parse word1 literals"
        (fn () => (Parse.Term `1w:word1`,Parse.Term `0w:word1`))
      val word_equality = phase "construct word equality" (fn () =>
        boolSyntax.mk_eq (one,boolSyntax.mk_cond (operand,one,zero)))
      val target = phase "intern producer target" (fn () =>
        Q.intern_cpc_term (boolSyntax.mk_eq (word_equality,true_operand)))
      val word_equality = boolSyntax.lhs target
      val bit_proof = phase "replay bv_poly_norm" (fn () =>
        R.replay_bv_poly_norm_for_test [target])
      val symmetry = phase "replay eq-symm" (fn () =>
        R.replay_rare_rewrite_for_test "eq-symm" [boolSyntax.T,operand])
      val assumption = Term.mk_var ("task57_endpoint_hyp",Type.bool)
      fun retain theorem = Thm.CONJUNCT1
        (Thm.CONJ theorem (Thm.ASSUME assumption))
      fun chain first second = R.replay_shared_trans_for_test
        [retain first,second]
      val expected = boolSyntax.mk_eq (word_equality,operand_true)
    in
      test "CPC bit producer keeps exact parsed conclusion" (fn () =>
        (same "producer rebuilt its target" (Thm.concl bit_proof) target;
         same "producer lost its exact right endpoint"
           (boolSyntax.rhs (Thm.concl bit_proof)) true_operand;
         exact target [] bit_proof));
      test "CPC symmetry producer retains canonical endpoint shells"
        (fn () =>
          (same "symmetry lost its left endpoint"
             (boolSyntax.lhs (Thm.concl symmetry)) true_operand;
           same "symmetry lost its right endpoint"
             (boolSyntax.rhs (Thm.concl symmetry)) operand_true;
           exact (boolSyntax.mk_eq (true_operand,operand_true)) [] symmetry));
      test "CPC symmetry does not replace an equal input using metadata"
        (fn () =>
          let
            val copy = Term.mk_comb (Term.rator operand,Term.rand operand)
            val proof = R.replay_rare_rewrite_for_test "eq-symm"
              [boolSyntax.T,copy]
            val (left,right) = boolSyntax.dest_eq (Thm.concl proof)
          in
            require "fixture accidentally shares its root"
              (not (Portable.pointer_eq (copy,operand)));
            same "symmetry replaced the original left input"
              (boolSyntax.rhs left) copy;
            same "symmetry replaced the original right input"
              (boolSyntax.lhs right) copy;
            exact (boolSyntax.mk_eq
              (boolSyntax.mk_eq (boolSyntax.T,copy),
               boolSyntax.mk_eq (copy,boolSyntax.T))) [] proof
          end);
      test "CPC symmetry keeps noncanonical shared DAG operands opaque"
        (fn () =>
          let
            val shared = shared_operand ()
            val theorem = phase "eq-symm uninterned shared depth45"
              (fn () => R.replay_rare_rewrite_for_test "eq-symm"
                [boolSyntax.T,shared])
            val (left,right) = boolSyntax.dest_eq (Thm.concl theorem)
            val (left_first,left_second) = boolSyntax.dest_eq left
            val (right_first,right_second) = boolSyntax.dest_eq right
          in
            (* Do not call exact/aconv on an expected huge unfolded tree. *)
            require "symmetry changed its small left input"
              (Term.aconv left_first boolSyntax.T);
            same "symmetry replaced its opaque left operand"
              left_second shared;
            same "symmetry replaced its opaque right operand"
              right_first shared;
            require "symmetry changed its small right input"
              (Term.aconv right_second boolSyntax.T);
            actual_hyp [] theorem
          end);
      test "CPC schematic XOR identity retains its exact source shell"
        (fn () =>
          let
            val shared = shared_operand ()
            val head = Q.intern_cpc_shell (Term.prim_mk_const
              {Thy="HolSmt",Name="xor"})
            val false_tm = Q.intern_cpc_shell boolSyntax.F
            val source = Q.intern_cpc_shell (Term.mk_comb
              (Q.intern_cpc_shell (Term.mk_comb (head,shared)),false_tm))
            val theorem = phase "XOR identity uninterned shared depth45"
              (fn () => R.replay_rare_rewrite_for_test "bool-xor-false"
                [shared])
            val (left,right) = boolSyntax.dest_eq (Thm.concl theorem)
          in
            same "XOR identity rebuilt its source shell" left source;
            same "XOR identity changed its opaque operand" right shared;
            actual_hyp [] theorem
          end);
      test "CPC flat nary keeps noncanonical shared DAG operands opaque"
        (fn () =>
          let
            val shared = shared_operand ()
            val head = Q.intern_cpc_term (Term.genvar
              (Type.mk_type ("fun",[Type.bool,Type.bool])))
            (* Canonicalize just the outer shell, NEVER its opaque child. *)
            val source = Q.intern_cpc_shell (Term.mk_comb (head,shared))
            val premise = retain (Thm.REFL shared)
            val theorem = phase "nary uninterned shared depth45"
              (fn () => R.replay_nary_cong_for_test source [premise])
            val (left,right) = boolSyntax.dest_eq (Thm.concl theorem)
          in
            same "nary replaced its exact source shell" left source;
            same "nary rebuilt its canonical result shell" right source;
            same "nary replaced its opaque source operand"
              (Term.rand left) shared;
            same "nary replaced its opaque result operand"
              (Term.rand right) shared;
            actual_hyp [assumption] theorem
          end);
      test "CPC lifted congruence retains each nested application shell"
        (fn () =>
          let
            val shared = shared_operand ()
            val variable = Q.intern_cpc_term (Term.genvar Type.bool)
            val inner_head = Q.intern_cpc_term (Term.genvar
              (Type.mk_type ("fun",[Type.bool,
                Type.mk_type ("fun",[Type.bool,Type.bool])])))
            val outer_head = Q.intern_cpc_term (Term.genvar
              (Type.mk_type ("fun",[Type.bool,Type.bool])))
            fun shell term = Q.intern_cpc_shell term
            fun result value = shell (Term.mk_comb (outer_head,
              shell (Term.mk_comb
                (shell (Term.mk_comb (inner_head,shared)),value))))
            val source = result variable
            val destination = result boolSyntax.T
            val target = shell (boolSyntax.mk_eq (source,destination))
            val premise = Drule.EQT_INTRO (Thm.ASSUME variable)
            val _ = same "EQT_INTRO changed the source variable"
              (boolSyntax.lhs (Thm.concl premise)) variable
            fun check_target conclusion =
              let
                val theorem = phase
                  (case conclusion of NONE => "cong sequential depth45"
                   | SOME _ => "cong targeted depth45")
                  (fn () => R.replay_cong_for_test conclusion
                    [source] [premise])
                val (left,right) = boolSyntax.dest_eq (Thm.concl theorem)
              in
                same "cong replaced source" left source;
                same "cong rebuilt nested result" right destination;
                actual_hyp [variable] theorem
              end
          in check_target NONE;check_target (SOME target) end);
      test "CPC retention declines binder templates before opening them"
        (fn () =>
          let
            val variable = Term.genvar Type.bool
            val binder = Term.mk_abs (variable,variable)
            val theorem = Thm.REFL binder
            val target = Thm.concl theorem
            val retained = R.retain_producer_conclusion_for_test
              target [] target theorem
          in
            require "binder template was not declined"
              (Portable.pointer_eq (retained,theorem));
            actual_hyp [] retained
          end);
      test "CPC abstract-dimension word congruence retains actual Hyp"
        (fn () =>
          let
            val word_type = wordsSyntax.mk_word_type (Type.mk_vartype "'a")
            val head = Term.genvar
              (Type.mk_type ("fun",[word_type,word_type]))
            val left = Term.genvar word_type
            val right = Term.genvar word_type
            val source = Term.mk_comb (head,left)
            val destination = Term.mk_comb (head,right)
            val hypothesis = boolSyntax.mk_eq (left,right)
            (* Optional candidate/type admission may decline with UNCHANGED;
               it must not turn an already valid congruence into a refusal. *)
            val theorem = R.replay_nary_cong_for_test source
              [Thm.ASSUME hypothesis]
            val identity = R.replay_nary_cong_for_test source
              [retain (Thm.REFL left)]
          in
            exact (boolSyntax.mk_eq (source,destination))
              [hypothesis] theorem;
            exact (boolSyntax.mk_eq (source,source)) [assumption] identity
          end);
      test "CPC producer retention leaves the 8192 whole-DAG gate intact"
        (fn () =>
          (case Exn.capture
              (SmtSkeletonProve.bounded_nodewise_equality quota true_operand)
              true_operand of
             Exn.Exn SmtSkeletonProve.REANCHOR_LIMIT => ()
           | _ => raise Fail "original whole-DAG gate changed"));
      test "CPC retained endpoints compose right-left with actual Hyp"
        (fn () => exact expected [assumption] (chain bit_proof symmetry));
      test "CPC retained endpoints compose right-right with actual Hyp"
        (fn () => exact expected [assumption]
          (chain bit_proof (Thm.SYM symmetry)));
      test "CPC retained endpoints compose left-left with actual Hyp"
        (fn () => exact expected [assumption]
          (chain (Thm.SYM bit_proof) symmetry));
      test "CPC retained endpoints compose left-right with actual Hyp"
        (fn () => exact expected [assumption]
          (chain (Thm.SYM bit_proof) (Thm.SYM symmetry)));
      test "CPC DAG congruence prefers a forward occurrence globally"
        (fn () =>
          let
            fun variable () = Q.intern_cpc_term (Term.genvar Type.bool)
            val a = variable ()
            val b = variable ()
            val c = variable ()
            val d = variable ()
            val source = Q.intern_cpc_term
              (boolSyntax.mk_disj (a,boolSyntax.mk_disj (b,c)))
            val destination = Q.intern_cpc_term
              (boolSyntax.mk_disj (a,boolSyntax.mk_disj (a,d)))
            val hypotheses = [boolSyntax.mk_eq (b,a),boolSyntax.mk_eq (c,d)]
            val theorem = R.replay_direct_nary_cong_for_test source
              (List.map Thm.ASSUME hypotheses)
            val (left,right) = boolSyntax.dest_eq (Thm.concl theorem)
          in
            same "DAG congruence changed source" left source;
            same "DAG congruence rewrote a reverse occurrence first"
              right destination;
            exact (boolSyntax.mk_eq (source,destination)) hypotheses theorem
          end);
      test "CPC ordinary CONG prefers exact operands to a context match"
        (fn () =>
          let
            fun variable () = Q.intern_cpc_term (Term.genvar Type.bool)
            val a = variable ()
            val b = variable ()
            val c = variable ()
            val source = Q.intern_cpc_term (boolSyntax.mk_disj (a,b))
            val destination = Q.intern_cpc_term (boolSyntax.mk_disj (source,c))
            val hypotheses = [boolSyntax.mk_eq (a,source),
                              boolSyntax.mk_eq (b,c)]
            fun located term = {term=term,
              provenance=CPC_Proof.AtomicProvenance}
            fun assumption (id,term) = CPC_Proof.ASSUME
              (id,{term=term,provenance=CPC_Proof.EqualityProvenance
                (CPC_Proof.AtomicProvenance,CPC_Proof.AtomicProvenance)})
            val proof = {cvc_version="1.3.4",commands=
              List.map assumption (ListPair.zip (["a","b"],hypotheses)) @
              [CPC_Proof.STEP {id="result",conclusion=NONE,
                rule=CPC_Proof.mk_rule CPC_Proof.ProofRule ("cong","cong"),
                premises=["a","b"],args=[located source]}]}
            val theorem = R.replay_root_for_test proof
            val (left,right) = boolSyntax.dest_eq (Thm.concl theorem)
          in
            same "ordinary congruence rewrote its enclosing source"
              left source;
            same "ordinary congruence lost a declared operand"
              right destination;
            exact (boolSyntax.mk_eq (source,destination)) hypotheses theorem
          end);
      test "CPC nary operand cuts do not rewrite an enclosing context"
        (fn () =>
          let
            fun variable () = Q.intern_cpc_term (Term.genvar Type.bool)
            val a = variable ()
            val b = variable ()
            val c = variable ()
            val d = variable ()
            val false_tm = Q.intern_cpc_term boolSyntax.F
            val source = Q.intern_cpc_term
              (boolSyntax.mk_disj (a,boolSyntax.mk_disj (b,c)))
            val destination = Q.intern_cpc_term
              (boolSyntax.mk_disj
                (source,boolSyntax.mk_disj (d,false_tm)))
            val hypotheses = [boolSyntax.mk_eq (a,source),
              boolSyntax.mk_eq (b,d),boolSyntax.mk_eq (c,false_tm)]
            val theorem = R.replay_nary_cong_for_test source
              (List.map Thm.ASSUME hypotheses)
            val (left,right) = boolSyntax.dest_eq (Thm.concl theorem)
          in
            same "nary replaced the entire context" left source;
            same "nary did not consume the declared operand premises"
              right destination;
            exact (boolSyntax.mk_eq (source,destination)) hypotheses theorem
          end);
      test "CPC recursive nary producer retains nested opaque endpoints"
        (fn () =>
          let
            val a = Term.mk_var ("task57_nary_a",Type.bool)
            val b = Term.mk_var ("task57_nary_b",Type.bool)
            val source = Q.intern_cpc_term
              (boolSyntax.mk_disj (a,boolSyntax.mk_disj (b,operand)))
            val destination = Q.intern_cpc_term
              (boolSyntax.mk_disj
                (boolSyntax.T,boolSyntax.mk_disj (boolSyntax.F,operand)))
            val expected = Q.intern_cpc_term
              (boolSyntax.mk_eq (source,destination))
            val theorem = R.replay_nary_cong_for_test source
              [Drule.EQT_INTRO (Thm.ASSUME a),
               Drule.EQF_INTRO (Thm.ASSUME (boolSyntax.mk_neg b)),
               Thm.REFL operand]
            val _ = same "nary producer rebuilt nested right endpoint"
              (boolSyntax.rhs (Thm.concl theorem)) destination
          in exact expected [a,boolSyntax.mk_neg b]
            (R.replay_shared_trans_for_test
              [theorem,Thm.REFL destination]) end);
      test "CPC unequal producer endpoints are not identified" (fn () =>
        let
          val unrelated = Thm.REFL
            (Term.mk_var ("task57_endpoint_unrelated",Type.bool))
          val small = Thm.REFL
            (Term.mk_var ("task57_endpoint_other",Type.bool))
        in
          case Exn.capture (fn () => chain small unrelated) () of
            Exn.Exn (Feedback.HOL_ERR _) => ()
          | _ => raise Fail "unrelated endpoints composed"
        end);
      test "FP candidate substitution preserves shared depth45"
        fp_shared_substitution;
      test "FP circuit aligns equal noncanonical shared depth45"
        fp_circuit_alias;
      test "FP bridge retains actual opaque variable occurrences"
        fp_source_occurrences;
      test "FP bridge specializes choice sources in small local laws"
        fp_choice_source_law;
      test "opaque word stops preserve occurrences and original input guard"
        word_opaque_source_guard;
      test "opaque rounding cases retain checked source identity"
        opaque_rounding_circuit;
      test "FP word circuit keeps canonical choice sources opaque"
        fp_word_choice_source;
      test "FP witness sequent cuts shared bridges before native INST"
        fp_bridge_sequent_substitution;
      test "FP bridge preserves original caps and first resource error"
        fp_first_resource_gate;
      test "FP bridge cuts encoding-only opaque sources"
        fp_encoding_source_cut;
      test "CPC false one-bit producer still rejects" (fn () =>
        let
          val small = Term.mk_var ("task57_endpoint_false",Type.bool)
          val wrong = boolSyntax.mk_eq
            (boolSyntax.mk_eq
               (one,boolSyntax.mk_cond (small,one,zero)),
             boolSyntax.mk_neg small)
        in
          case Exn.capture R.replay_bv_poly_norm_for_test [wrong] of
            Exn.Exn (Feedback.HOL_ERR _) => ()
          | _ => raise Fail "false one-bit schema accepted"
        end)
    end
end
