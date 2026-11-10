(* Selected Z3 bounded dispatch/discovery regressions. Theory producers,
   Definition elimination and opt-in Value programmes have separate tests. *)
structure Z3_CompactReplayTests =
struct
  open HolKernel Parse boolLib bossLib
  structure G = SmtReplayGraph
  structure F = SmtLib_GraphFrontend
  structure Z = Z3_GraphProofParser
  structure Q = SmtLib_GraphProof
  structure R = Z3_GraphProofReplay
  structure W = SmtReplayInvocationWork
  structure GP = SmtLib_GraphPreprocess
  val maximum = 10000
  fun require message yes = if yes then () else raise Fail message
  fun clean theorem =
    let val (tags,_) = Tag.dest_tag (Thm.tag theorem)
    in require "unexpected proof tags"
      (List.all (fn tag => tag = "DISK_THM") tags andalso
       null (Tag.axioms_of (Thm.tag theorem))) end
  fun exact expected hypotheses theorem =
    (require ("wrong endpoint: " ^ term_to_string (Thm.concl theorem) ^
       " expected " ^ term_to_string expected)
       (Term.aconv (Thm.concl theorem) expected);
     require "wrong canonical Hyp" (HOLset.equal
       (Thm.hypset theorem,HOLset.addList (Term.empty_tmset,hypotheses)));
     clean theorem)
  fun options graph scope sources : F.options =
    {graph=graph,scope=scope,logic="ALL",sources=sources,
     sorts=Redblackmap.mkDict String.compare,binder_lists=[],
     import_limit=maximum,literal_limit=maximum,binder_limit=maximum,
     recipe_limits={template_limit=maximum,index_limit=maximum,
       operand_limit=maximum,token_limit=maximum},
     special=fn _ => fn _ => NONE,
     ascribed=fn _ => fn _ => fn _ => NONE}
  fun with_proof sources text action =
    let
      val graph = G.new () val scope = G.root_scope graph
      val stream = TextIO.openString text
      val packet = Z.create_packet (options graph scope sources)
        "4.15.3" stream
      fun close () = (Q.close packet;TextIO.closeIn stream;
        G.close_scope graph scope)
      val outcome = Exn.capture (fn () => action graph scope
        (Q.proof packet)) ()
      val cleanup = Exn.capture close ()
    in case outcome of Exn.Exn primary => raise primary
      | Exn.Res result => (Exn.release cleanup;result) end
  fun replay graph scope proof limit local_law =
    R.replay_with_sources_using [] graph scope
      {proof=proof,template_limit=limit,local_law=local_law,
       nnf=Z3_ProofReplay.graph_bounded_nnf graph}
  fun owned_replay graph scope proof target assumptions local_law =
    let
      val sources = SmtReplaySource.new graph scope maximum
        {goal=target,assumptions=assumptions}
      val work = W.begin graph scope sources
        {limits={input_limit=maximum,output_limit=maximum,
          template_limit=maximum},work_limit=100000000}
      val preprocessing = GP.discover_from_sources graph scope sources
        {import_limit=maximum,revisit=false,check_type=fn _ => (),
         conversion=fn _ => NONE}
      val outcome = Exn.capture (fn () =>
        R.replay_with_preprocessed_sources_with_work_using
          work graph scope {sources=sources,preprocessing=preprocessing,
            proof=proof,template_limit=maximum,local_law=local_law,
            nnf=Z3_ProofReplay.graph_bounded_nnf graph}) ()
      val _ = W.close work
    in Exn.release outcome end
  fun fixed graph proof = Z3_ProofReplay.graph_bounded_local_law
    graph [] proof
  fun calls name =
    case List.find (fn (key,_) => key=name) (Profile.results ()) of
      SOME (_,data) => #n data | NONE => 0
  fun refuses action =
    (action ();false) handle Feedback.HOL_ERR _ => true
      | HolSatLib.SAT_cex _ => true
  (* Inspect constructors, not compact variable spelling. Boolean result
     types alone cannot identify these theory families. *)
  fun has_constant graph theory node = List.exists (fn child =>
    case G.view graph child of G.Constant _ =>
      #Thy (Term.dest_thy_const (G.representative graph child)) = theory
    | _ => false)
    (G.block_reachable graph [node])
  fun theory_case theory profile expected text =
    with_proof [("x",``x:word8``)] text
    (fn graph => fn scope => fn proof =>
      let
        val count = ref 0
        fun producer (request:R.local_request) =
          (count := !count+1;
           require "selected constructor lost its theory"
             (has_constant graph theory (#target request));
           fixed graph proof request)
        val _ = Profile.reset_all ()
        val theorem = replay graph scope proof maximum producer
        val _ = exact expected [] theorem
        val _ = require "law discovery was repeated or skipped" (!count=1)
      in require ("missing selected profile " ^ profile) (calls profile>0) end)
  val word_text = "((proof (let ((w (bvadd x #x00))) " ^
    "(let ((@law (rewrite (= w x)))) @law))))"
  val word_expected = ``(x:word8) + 0w = x``
  val fp_text = "((proof (rewrite " ^
    "(= (fp.isNaN (_ NaN 4 3)) true))))"
  val fp_expected = ``smtfp_is_nan (smtfp_nan:(2,4) smtfp) = T``
  fun retained_premise () =
    let val p = ``task36_p:bool`` val q = ``task36_q:bool``
        val hypothesis = boolSyntax.mk_eq (boolSyntax.mk_neg p,q)
        val expected = boolSyntax.mk_eq
          (boolSyntax.mk_imp (p,boolSyntax.F),q)
    in with_proof [("p",p),("q",q)]
      "((proof (nnf-pos (asserted (= (not p) q)) \
      \(= (implies p false) q))))"
      (fn graph => fn scope => fn proof =>
        let val count = ref 0
            fun producer request =
              (count := !count+1;fixed graph proof request)
            val theorem = replay graph scope proof maximum producer
        in exact expected [hypothesis] theorem;
           require "conditional law was not retained once" (!count=1) end)
    end
  fun unused_premise owned () = with_proof [("p",``task36_unused:bool``)]
    "((proof (nnf-neg (asserted p) \
    \(= (not (forall ((b Bool)) false)) (exists ((b Bool)) true)))))"
    (fn graph => fn scope => fn proof =>
      let val target = ``~(!b:bool. F) = (?b:bool. T)``
          val initial = Z3_Proof.empty_proof "4.15.3"
          val ordinary = Z3_Proof.update_proof_steps initial
            (Redblackmap.insert (Z3_Proof.proof_steps initial,0,
              Z3_Proof.NNF_NEG
                ([Z3_Proof.THEOREM (Thm.ASSUME ``task36_unused:bool``)],
                 target)))
          val native = Z3_ProofReplay.replay_root_for_test ordinary
          val _ = require "ordinary unused premise gained a Hyp"
            (null (Thm.hyp native))
          fun run () = if not owned then
              replay graph scope proof maximum (fixed graph proof)
            else owned_replay graph scope proof target
              [``task36_unused:bool``] (fixed graph proof)
      in exact target (Thm.hyp native) (run ()) end)
  fun partial_premises () =
    let val p = ``task36_p:bool`` val q = ``task36_q:bool``
        val r = ``task36_r:bool``
        val expected = boolSyntax.mk_eq
          (boolSyntax.mk_imp (p,boolSyntax.F),q)
    in with_proof [("p",p),("q",q),("r",r)]
      "((proof (nnf-pos (asserted r) (asserted (= (not p) q)) \
      \(= (implies p false) q))))"
      (fn graph => fn scope => fn proof =>
        exact expected [boolSyntax.mk_eq (boolSyntax.mk_neg p,q)]
          (replay graph scope proof maximum (fixed graph proof)))
    end
  val quantified = ``~(!b:bool. F) = (?b:bool. T)``
  val quantified_text =
    "(= (not (forall ((b Bool)) false)) (exists ((b Bool)) true))"
  fun local_discharge canonical owned () = with_proof []
    ("((proof (let ((g " ^ quantified_text ^ ")) " ^
     "(lemma (unit-resolution (nnf-neg (hypothesis (not g)) g) " ^
     "(hypothesis (not g)) false) g)))))")
    (fn graph => fn scope => fn proof =>
      exact quantified [] (if owned then
        owned_replay graph scope proof quantified [] (fixed graph proof)
      else
        let val sources = if not canonical then [] else
              List.mapPartial (fn (_,Z.Rule {rule,conclusion,...}) =>
                if #replay_handler rule = "hypothesis" then
                  SOME (#node conclusion) else NONE
                | _ => NONE) (Redblackmap.listItems (#steps proof))
        in R.replay_with_sources_using sources graph scope
          {proof=proof,template_limit=maximum,local_law=fixed graph proof,
           nnf=Z3_ProofReplay.graph_bounded_nnf graph} end))
  fun open_import () =
    let
      val p = ``task36_p:bool`` val q = ``task36_q:bool``
      val r = ``task36_r:bool`` val s = ``task36_s:bool``
      val equation = boolSyntax.mk_eq (p,q)
      val lifted = ``(!a:bool. task36_p) = (!b:bool. task36_q)``
      val clause = boolSyntax.list_mk_disj
        [boolSyntax.mk_neg lifted,boolSyntax.mk_neg quantified,s]
      val text = "((proof (let ((g1 (= (forall ((a Bool)) p) " ^
        "(forall ((b Bool)) q)))) (let ((g2 " ^ quantified_text ^ ")) " ^
        "(unit-resolution (asserted (or (not g1) (not g2) s)) " ^
        "(quant-intro (proof-bind (lambda ((x Bool)) " ^
        "(asserted (= p q)))) g1) (nnf-neg (asserted r) g2) " ^
        "(asserted (not s)) false))))))"
    in with_proof [("p",p),("q",q),("r",r),("s",s)] text
      (fn graph => fn scope => fn proof =>
        exact boolSyntax.F [equation,clause,boolSyntax.mk_neg s]
          (replay graph scope proof maximum (fixed graph proof)))
    end
  fun duplicate_ports owned () =
    let val p = ``task36_p:bool`` val q = ``task36_q:bool``
        val z = ``task36_z:bool``
        val equation = boolSyntax.mk_eq (p,q)
        val clause = boolSyntax.mk_disj (equation,boolSyntax.mk_neg z)
    in with_proof [("p",p),("q",q),("z",z)]
      "((proof (let ((e (= p q))) (nnf-pos (asserted e) \
      \(unit-resolution (asserted (or e (not z))) (asserted z) e) e))))"
      (fn graph => fn scope => fn proof => exact equation [equation]
        (if owned then owned_replay graph scope proof equation
          [equation,clause,z] (fixed graph proof)
         else replay graph scope proof maximum (fixed graph proof)))
    end
  fun unused_closed_image checked () = with_proof []
    "((declare-fun z () Bool) (proof (nnf-pos (asserted (= z true)) \
    \(rewrite (= (and z true) (and true z))) (= true true))))"
    (fn graph => fn scope => fn proof =>
      exact ``T = T`` []
        ((if checked then R.replay_with_checked_variable_definitions_using
          else R.replay_with_closed_definition_sources_using) [] graph scope
          {proof=proof,template_limit=maximum,local_law=fixed graph proof,
           nnf=Z3_ProofReplay.graph_bounded_nnf graph}))
  fun compact_cap () =
    let
      (* The compact Source/template bound is NOT the fixed ordinary
         worker's unfolded-term bound. This shared non-propositional law
         fits the latter and must not acquire a new template-based refusal. *)
      fun nest i = if i=10 then "(rewrite (= s9 x))" else
        "(let ((s" ^ Int.toString i ^ " (bvand s" ^ Int.toString (i-1) ^
        " s" ^ Int.toString (i-1) ^ "))) " ^ nest (i+1) ^ ")"
      fun tree 0 = ``x:word8``
        | tree n = let val child=tree (n-1)
                   in Term.list_mk_comb (``$&& : word8 -> word8 -> word8``,
                        [child,child]) end
    in with_proof [("x",``x:word8``)]
      ("((proof (let ((s0 x)) " ^ nest 1 ^ "))))")
      (fn graph => fn scope => fn proof =>
        let val count = ref 0
            fun producer (request:R.local_request) =
              (count := !count+1;
               require "fixture no longer exceeds the unfolded cap"
                 (case G.unfolded_nodes graph G.RawNodes 1000 (#law request)
                    of SOME n => n>1000 | NONE => true);
               fixed graph proof request)
            val theorem = replay graph scope proof 1000 producer
        in exact (boolSyntax.mk_eq (tree 9,``x:word8``)) [] theorem;
           require "shared theory law was not retained once" (!count=1) end)
    end
  fun rejected_laws () = with_proof [("x",``x:word8``)] word_text
    (fn graph => fn scope => fn proof =>
      let
        fun reject producer = require "unchecked local law accepted"
          (refuses (fn () => ignore
            (replay graph scope proof maximum producer)))
      in reject (fn _ => SOME boolTheory.TRUTH);
         reject (fn request => SOME
           (Thm.ASSUME (G.representative graph (#law request))));
         reject (fn request => SOME (Thm.DISCH boolSyntax.F
           (Option.valOf (fixed graph proof request)))) end)
  fun propositional_fp () = with_proof [("x",``x:(2,4) smtfp``)]
    "((proof (rewrite (= (implies (fp.isNaN x) true) true))))"
    (fn graph => fn scope => fn proof =>
      let val _ = Profile.reset_all ()
          val theorem = replay graph scope proof maximum (fixed graph proof)
      in exact ``(smtfp_is_nan (x:(2,4) smtfp) ==> T) = T`` [] theorem;
         require "FP tautology dispatched to theory worker"
           (calls "rewrite(4)(fp)"=0) end)
  fun terminal () = with_proof [("x",``x:word8``)] word_text
    (fn graph => fn scope => fn proof =>
      let
        val primary = Feedback.mk_HOL_ERR "Task36" "producer" "primary"
        fun run error =
          let val count = ref 0
              val result = Exn.capture (fn () => replay graph scope proof
                maximum (fn _ => (count := !count+1;raise error))) ()
          in require "producer retried after terminal error" (!count=1);
             case result of Exn.Exn held => require "changed first error"
               (General.exnMessage held=General.exnMessage error)
             | _ => raise Fail "terminal producer error was swallowed" end
      in run primary;run (Fail "terminal producer failure");
         run Thread.Interrupt end)
  fun nnf_fallback () =
    let
      val target = ``(!x:num. task36_P x) ==> task36_P 0``
      val initial = Z3_Proof.empty_proof "4.15.3"
      val proof = Z3_Proof.update_proof_steps initial
        (Redblackmap.insert (Z3_Proof.proof_steps initial,0,
          Z3_Proof.NNF_POS ([],target)))
      val _ = Profile.reset_all ()
      val theorem = Z3_ProofReplay.replay_root_for_test proof
    in exact target [] theorem;
       require "ordinary NNF decline lost checked METIS fallback"
         (calls "nnf[metis-fallback]">0) end
  fun nnf_gate () =
    let
      val leaves = List.tabulate
        (SmtResource.max_term_nodes_for "Skeleton" div 2+10,fn i =>
        Term.mk_var ("task36_nnf_" ^ Int.toString i,Type.bool))
      fun balanced [term] = term
        | balanced terms =
            let val half = List.length terms div 2
                val (left,right) = (List.take (terms,half),
                  List.drop (terms,half))
            in boolSyntax.mk_conj (balanced left,balanced right) end
      val target = boolSyntax.mk_imp (balanced leaves,boolSyntax.T)
      val _ = Profile.reset_all ()
      val initial = Z3_Proof.empty_proof "4.15.3"
      val proof = Z3_Proof.update_proof_steps initial
        (Redblackmap.insert (Z3_Proof.proof_steps initial,0,
          Z3_Proof.NNF_POS ([],target)))
      val outcome = Exn.capture Z3_ProofReplay.replay_root_for_test proof
      val _ = require "NNF gate fell through to METIS"
        (calls "nnf[metis-fallback]"=0)
    in case outcome of Exn.Exn (Feedback.HOL_ERR holerr) =>
         require "NNF changed its Skeleton resource diagnostic"
           (SmtResource.is_resource_gate holerr andalso
            String.isSubstring "z3-nnf-taut" (Feedback.message_of holerr))
       | _ => raise Fail "NNF swallowed its resource gate" end
  fun run () =
    let
      fun test label action =
        (testutils.tprint ("Z3 compact " ^ label);action ();testutils.OK ())
      fun negative text = with_proof [] text
        (fn graph => fn scope => fn proof =>
          require "false certificate accepted" (refuses (fn () => ignore
            (replay graph scope proof maximum (fixed graph proof)))))
    in
      test "named BV rewrite retains checked law" (fn () =>
        theory_case "words" "rewrite(16)(WORD_ARITH_CONV)"
          word_expected word_text);
      test "named FP constructor dispatch" (fn () =>
        theory_case "smtfloat" "rewrite(4)(fp)" fp_expected fp_text);
      test "indexed BV metadata dispatch" (fn () =>
        with_proof [("x",``x:word8``)]
        "((proof ((_ th-lemma bv bit-blast 1) (= (bvadd x #x00) x))))"
        (fn graph => fn scope => fn proof =>
          let val seen = ref false
              fun producer (request:R.local_request) =
                (seen := Option.isSome (#metadata request);
                 fixed graph proof request)
              val theorem = replay graph scope proof maximum producer
          in exact word_expected [] theorem;
             require "theory metadata lost" (!seen) end));
      test "conditional exact Source Hyp" retained_premise;
      test "unused local premise does not become a Source dependency"
        (unused_premise false);
      test "owned sparse law excludes unused Source"
        (unused_premise true);
      test "only the actual second premise survives" partial_premises;
      test "pruned lemma-local discharge" (local_discharge false false);
      test "canonical Source beside lemma-local discharge"
        (local_discharge true false);
      test "owned pruned lemma-local discharge" (local_discharge false true);
      test "open quant-intro import beside a pruned law" open_import;
      test "duplicate endpoint keeps its first actual port"
        (duplicate_ports false);
      test "owned duplicate endpoint keeps its first port"
        (duplicate_ports true);
      test "unused changed closed-source image"
        (unused_closed_image false);
      test "unused checked-variable closed-source image"
        (unused_closed_image true);
      test "propositional FP precedes theory dispatch" propositional_fp;
      test "wrong endpoint/open local laws reject" rejected_laws;
      test "compact cap preserves bounded shared theory law" compact_cap;
      test "terminal discovery exceptions" terminal;
      test "NNF ordinary checked fallback" nnf_fallback;
      test "NNF first resource error" nnf_gate;
      test "false BV certificate" (fn () => negative
        "((declare-fun x () (_ BitVec 8)) \
        \(proof (rewrite (= (bvadd x #x01) x))))");
      test "false FP certificate" (fn () => negative
        "((proof (rewrite (= (fp.isNaN (_ NaN 4 3)) false))))");
      test "false propositional certificate" (fn () => negative
        "((proof (rewrite (= true false))))")
    end
end
