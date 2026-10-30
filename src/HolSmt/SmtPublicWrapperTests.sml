(* Copyright (c) 2026 The HOL4 contributors.
 * Selected original-Source wrappers, including their actual tactic return.
 * run requires installed Z3 and cvc5; missing engines are not skipped.
 * No local theorem/certificate substitutes for a public positive below.
 *)
structure SmtPublicWrapperTests =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure C = SmtReplayCanonGraph
  structure GP = SmtLib_GraphPreprocess
  structure WS = SmtReplayWrapperSession
  structure CG = SmtCheckedGraph
  structure U = SmtReplayUnify

  val cap = 10000
  fun require message yes = if yes then () else testutils.die message
  fun ptr left right = Portable.pointer_eq (left,right)
  fun test label action =
    (testutils.tprint label; action (); testutils.OK ())
  fun clean theorem =
    let val (tags,_) = Tag.dest_tag (Thm.tag theorem)
    in null (Tag.axioms_of (Thm.tag theorem)) andalso
       List.all (fn tag => tag = "DISK_THM") tags end
  fun refusal action =
    (action (); NONE)
    handle Feedback.HOL_ERR detail => SOME (Feedback.message_of detail)

  val limits : CG.limits =
    {import_limit=cap,literal_limit=200000,binder_limit=200000,
     recipe_limits={template_limit=200000,index_limit=1024,
       operand_limit=1024,token_limit=4096}}

  (* Same fixed closed law as replay_processed_goal_transport_success.
     Bottom-up GP traversal applies it twice for ((p /\ T) /\ T),
     retaining both the child congruence and the outer schema edge. *)
  fun preprocessing graph scope sources =
    let
      val hole = Term.mk_var ("public_wrapper_hole",Type.bool)
      val law = Thm.CONJUNCT1 (Thm.CONJUNCT2
        (Thm.SPEC hole boolTheory.AND_CLAUSES))
      val conjunction = G.constant graph scope boolSyntax.conjunction
      val truth = G.constant graph scope boolSyntax.T
      fun propose node = case G.view graph node of
          G.Application (inner,right) =>
            (case G.view graph inner of
               G.Application (head,left) =>
                 if head = conjunction andalso right = truth then
                   SOME (C.checked_graph_schema graph scope
                     {theorem=law,holes=[hole],operands=[left],
                      template_limit=cap})
                 else NONE
             | _ => NONE)
        | _ => NONE
    in C.with_schema_statistics graph scope (fn () =>
      GP.discover_from_sources graph scope sources
        {import_limit=cap,revisit=false,check_type=fn _ => (),
         conversion=propose}) end

  datatype engine = Z3Engine | CVCEngine
  fun engine_name Z3Engine = "Z3"
    | engine_name CVCEngine = "cvc5"
  fun nest 0 term = term
    | nest depth term = boolSyntax.mk_conj (nest (depth-1) term,boolSyntax.T)

  (* A fresh original Source, finite GP validation and tactic context on
     EVERY call. Retain pointer expectations while the Source is live:
     neither Source nor graph getters may be reopened after solver close. *)
  fun public_case engine depth =
    let
      val p = Term.mk_var ("public_wrapper_p",Type.bool)
      val original = nest depth p
      val goal = ([original,original],original)
      val held = ref (NONE :
        (G.graph * G.scope * Term.term list) option)
      val discoveries = ref 0
      fun discover sources =
        let
          val _ = discoveries := !discoveries + 1
          val graph = S.owning_graph sources
          val scope = S.owning_scope sources
          val canonical = List.map (G.representative graph)
            (S.assumption_nodes sources)
          val (validation,stats) = preprocessing graph scope sources
          val (assumptions,processed) = GP.processed_goal validation
          val _ = require "GP changed its original occurrence portfolio"
            (ptr (GP.original_sources validation) sources andalso
             GP.source_nodes validation = S.assumption_nodes sources @
               [S.denied_goal_node sources] andalso
             length canonical = 2 andalso
             ptr (hd canonical) (List.nth (canonical,1)))
          val _ = require "GP did not perform the requested checked chain"
            (Term.aconv processed p andalso length assumptions = 2 andalso
             List.all (fn term => Term.aconv term p) assumptions andalso
             (case depth of
                0 => #created_schemas stats = 0 andalso
                     #schema_raw_nodes stats = 0
              | 1 => #created_schemas stats = 3 andalso
                     #schema_raw_nodes stats = 27
              | 2 => #created_schemas stats = 6 andalso
                     #schema_raw_nodes stats = 54
              | _ => false) andalso
             (if depth = 0 then Term.aconv original processed else
                not (Term.aconv original processed)))
          val _ = held := SOME (graph,scope,canonical)
        in validation end
      (* These Boolean proofs need no additional Z3 local/NNF laws.
         CPC uses its existing bounded reconstruction worker. *)
      val solver = case engine of
          Z3Engine => Z3.Z3_SMT_Original_Source_Prover
            {limits=limits,discover=discover,
             local_law=fn _ => NONE,nnf=fn _ => NONE}
        | CVCEngine => CVC.CVC_SMT_Original_Source_Prover
            {limits=limits,discover=discover,ordinary_limit=cap,
             worker=CPC_ProofReplay.graph_bounded_worker [],
             force_worker=NONE}
      val context = Context.snapshot ()
      val (subgoals,justify) = HolSmtLib.GENERIC_SMT_TAC solver goal context
      val _ = require "public checked tactic left subgoals" (null subgoals)
      (* Inspect THIS theorem, not a lower-level replay result or TAC_PROOF
         reconstruction which could hide a conclusion/Hyp transport. *)
      val theorem = justify []
      val (graph,scope,canonical) = valOf (!held)
      val hypotheses = Thm.hyp theorem
      val _ = require "tactic justification lost exact original Goal/Hyp"
        (ptr (Thm.concl theorem) original andalso
         length hypotheses = 1 andalso ptr (hd hypotheses) (hd canonical)
         andalso Term.aconv (hd hypotheses) original andalso
         (depth = 0 orelse not (Term.aconv (hd hypotheses) p)))
      val _ = require "tactic justification returned dirty full tags"
        (clean theorem)
      val _ = Library.check_oracle_tags
        "SmtPublicWrapperTests" "public_case" theorem
    in require "public invocation was reused or did not retire its owner"
      (!discoveries = 1 andalso
       Option.isSome (refusal (fn () => G.validate_scope graph scope))) end

  (* Raw negative controls ONLY. Kernel theorems here deliberately attack
     the Source/session receiver; none are fed to GENERIC_SMT_TAC. *)
  fun with_session original action =
    let
      val graph = G.new ()
      val scope = G.root_scope graph
      val goal = ([original,original],original)
      val sources = S.new graph scope cap
        {goal=original,assumptions= #1 goal}
      val session = WS.start sources goal
      fun exercise () =
        let
          val _ = WS.discover session (fn same =>
            #1 (preprocessing graph scope same))
          val _ = WS.begin_replay session
          val canonical = S.canonical_goal sources
          val good = Thm.EQ_MP (Thm.SYM (S.goal_bridge sources))
            (Thm.ASSUME canonical)
          val _ = S.check_goal sources good
        in action (graph,scope,sources,session,goal,good) end
      val outcome = Exn.capture exercise ()
      val cleanup = Exn.capture WS.close session
    in case outcome of Exn.Exn primary => raise primary
      | Exn.Res result => (Exn.release cleanup;result) end

  fun reject_candidate expected session goal graph scope theorem =
    let val denied = refusal (fn () => WS.accept session theorem)
    in require "raw candidate bypassed Source fence or failed elsewhere"
      (denied = SOME expected andalso
       Option.isSome (refusal (fn () => G.validate_scope graph scope))
       andalso refusal (fn () => WS.audit session goal theorem) =
         SOME "solver result has not been Source-checked") end

  fun add_hyp hypothesis theorem =
    Thm.CONJUNCT1 (Thm.CONJ theorem (Thm.ASSUME hypothesis))

  fun raw_negatives () =
    let
      fun changed () = boolSyntax.mk_conj
        (Term.mk_var ("public_wrapper_raw_p",Type.bool),boolSyntax.T)
      fun check label expected candidate = test label (fn () =>
        with_session (changed ())
          (fn (graph,scope,sources,session,goal,good) =>
            reject_candidate expected session goal graph scope
              (candidate graph scope sources good)))
      val _ = check "Source session rejects an unrelated conclusion"
        "source conclusion was not retained exactly"
        (fn _ => fn _ => fn _ => fn _ =>
          Thm.ASSUME (Term.mk_var ("public_wrapper_wrong",Type.bool)))
      val _ = check "Source session rejects semantic-only Goal transport"
        "source conclusion was not retained exactly"
        (fn _ => fn _ => fn _ => Thm.CONJUNCT1)
      val _ = check "Source session rejects an extra ordinary Hyp"
        "hypothesis is not a retained permitted source"
        (fn _ => fn _ => fn _ => add_hyp
          (Term.mk_var ("public_wrapper_extra",Type.bool)))
      val _ = check "Source session rejects a solver-private Hyp leak"
        "hypothesis is not a retained permitted source"
        (fn graph => fn scope => fn sources => fn good =>
          let
            val p = #1 (boolSyntax.dest_conj (Thm.concl good))
            val private = G.representative graph
              (G.fresh_flexible_variable graph scope p)
            val _ = require "private-leak control did not allocate privately"
              (not (Term.aconv private p) andalso
               not (ptr private (S.canonical_goal sources)))
          in add_hyp private good end)
      val _ = check "Source session rejects oracle-contaminated full tags"
        "unexpected replay tags"
        (fn _ => fn _ => fn _ => fn good =>
          Thm.mk_oracle_thm "SmtPublicWrapperTests-negative"
            (Thm.hyp good,Thm.concl good))
      val _ = check "Source session rejects axiom-contaminated full tags"
        "unexpected replay tags"
        (fn _ => fn _ => fn _ => fn good =>
          Thm.add_tag (Tag.ax_tag
            (Nonce.mk "SmtPublicWrapperTests-negative-axiom"),good))
      val _ = test "Source session requires exact Goal even for alpha"
        (fn () =>
          let
            val x = Term.mk_var ("public_wrapper_x",Type.bool)
            val y = Term.mk_var ("public_wrapper_y",Type.bool)
            val original = boolSyntax.mk_forall (x,x)
            val renamed = boolSyntax.mk_forall (y,y)
          in with_session original
            (fn (graph,scope,_,session,goal,good) =>
              let val candidate = Thm.EQ_MP
                    (Thm.ALPHA original renamed) good
                  val _ = require "alpha negative was not alpha-only"
                    (Term.aconv original (Thm.concl candidate) andalso
                     not (ptr original (Thm.concl candidate)))
              in reject_candidate "source conclusion was not retained exactly"
                session goal graph scope candidate end)
          end)
      val _ = test "Retired audit rejects a substituted return theorem"
        (fn () => with_session (changed ())
          (fn (_,_,_,session,goal,good) =>
            let
              val _ = WS.accept session good
              val _ = WS.close session
              val _ = WS.audit session goal good
              val other = add_hyp
                (Term.mk_var ("public_wrapper_late_private",Type.bool)) good
            in require "retired audit accepted a replaced checked result"
              (not (ptr other good) andalso
               refusal (fn () => WS.audit session goal other) =
                 SOME "solver returned a different theorem") end))
      val _ = test "Retired audit keeps duplicate original occurrences"
        (fn () => with_session (changed ())
          (fn (_,_,_,session,(assumptions,goal),good) =>
            let
              val _ = WS.accept session good
              val _ = WS.close session
            in require "retired audit accepted a changed source portfolio"
              (refusal (fn () => WS.audit session
                ([hd assumptions],goal) good) =
                  SOME "solver invocation original goal differs") end))
      val _ = test "Checked semantic equality cannot be alpha alignment"
        (fn () => with_session (changed ())
          (fn (graph,scope,sources,_,_,_) =>
            let
              val source = S.goal_source sources
              val (left,_) = boolSyntax.dest_conj (#original source)
              val law = Thm.CONJUNCT1 (Thm.CONJUNCT2
                (Thm.SPEC left boolTheory.AND_CLAUSES))
              val parsed = #node (G.import graph scope cap left)
              val denied = refusal (fn () => ignore
                (SmtReplaySourceBinderAlignment.discover graph scope
                  {source= #node source,parsed=parsed,
                   admit_binder=fn _ => NONE,check_type=fn _ => ()}))
            in require "semantic law acquired alpha alignment authority"
              (clean law andalso null (Thm.hyp law) andalso
               Term.aconv (boolSyntax.lhs (Thm.concl law))
                 (#original source) andalso
               Term.aconv (boolSyntax.rhs (Thm.concl law)) left andalso
               not (Term.aconv (#original source) left) andalso
               denied = SOME "source/parser declarations or shapes differ")
            end))
      val _ = test "Original Source variables cannot be solver assignments"
        (fn () => with_session (changed ())
          (fn (graph,scope,sources,_,_,_) =>
            let
              val p = #1 (boolSyntax.dest_conj (S.canonical_goal sources))
              val rigid = #node (G.import graph scope cap p)
              val truth = G.constant graph scope boolSyntax.T
              val outcome = U.unify graph
                {scope=scope,flexible=[],equations=[(rigid,truth)]}
              val denied = refusal (fn () => ignore (U.unify graph
                {scope=scope,flexible=[rigid],equations=[(rigid,truth)]}))
            in require "rigid original acquired assignment authority"
              ((case outcome of U.NoMatch U.RigidMismatch => true
                  | _ => false) andalso
               denied = SOME "permission to assign a rigid variable") end))
    in () end

  fun run () =
    (require "Task47 public tests require installed external Z3"
       (Z3.is_configured ());
     require "Task47 public tests require installed external cvc5"
       (CVC.is_configured ());
     List.app (fn engine => List.app (fn (depth,label) =>
       test (engine_name engine ^ " selected public " ^ label)
         (fn () => public_case engine depth))
       [(0,"original identity, duplicate assumptions"),
        (1,"(p /\\ T) -> p, duplicate assumptions"),
        (2,"((p /\\ T) /\\ T) -> p, duplicate assumptions")])
       [Z3Engine,CVCEngine];
     raw_negatives ())
end
