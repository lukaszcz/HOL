open HolKernel Parse boolLib testutils HolSatLib

val _ = set_trace "Unicode" 0

(* #1170: SAT_ORACLE used to fabricate a bogus theorem on inputs whose
   negated form has a top-level conjunct that boolean-simplifies to F.
   For ``b ==> T`` the negation is ``b /\ ~T``; presimp turns ``~T`` into
   ``F``, but the F conjunct was silently dropped from the CNF passed to
   MiniSAT, which then declared satisfiability. SAT_ORACLE skipped the
   model-check that SAT_PROVE relies on and returned a bogus
   |- b ==> ~(b ==> T). The fix short-circuits in to_cnf when a conjunct
   reduces to F, so MiniSAT is never invoked for this case (and so the
   test does not depend on a working MiniSAT installation). *)
val _ = tprint "SAT_ORACLE proves `b ==> T` (#1170)"
val _ = require_msg
          (check_result (fn th => concl th ~~ ``b ==> T``))
          thm_to_string
          SAT_ORACLE
          ``b ==> T``

(* Definitional CNF uses a shared root assumption while replaying the
   resolution trace; the returned proof must still discharge that root. *)
val _ = tprint "SAT_PROVE discharges definitional CNF roots"
val _ = require_msg
          (check_result (fn th => null (hyp th) andalso
            concl th ~~ ``(p /\ q) ==> (q /\ p)``))
          thm_to_string
          SAT_PROVE
          ``(p /\ q) ==> (q /\ p)``

(* Proof-only mode checks UNSAT certificates but never reconstructs a model
   theorem for a satisfying assignment that the caller will discard. *)
val _ = tprint "SAT_PROVE_ONLY checks UNSAT proofs"
val _ = require_msg
          (check_result (fn th => null (hyp th) andalso
            concl th ~~ ``(p /\ q) ==> (q /\ p)``))
          thm_to_string
          SAT_PROVE_ONLY
          ``(p /\ q) ==> (q /\ p)``

val _ = tprint "SAT_PROVE_ONLY rejects SAT instances"
val _ = require_msg
          (check_result (fn rejected => rejected))
          Bool.toString
          (fn tm => (ignore (SAT_PROVE_ONLY tm); false)
             handle SAT_satisfiable _ => true)
          ``p \/ q``

(* Explicit CNF counts propositional atoms, which need not be HOL
   variables.  Here P is the only free variable but P T and P F are
   distinct DIMACS atoms.  Proof-only mode must also override an oracle
   flag supplied in the configuration. *)
val _ = tprint "explicit CNF counts compound Boolean atoms"
val _ = require_msg
          (check_result (fn th =>
            let val (oracles, axioms) = Tag.dest_tag (tag th)
            in null (hyp th) andalso
               concl th ~~ ``~((P:bool->bool) T /\ ~P T /\ P F /\ ~P F)``
               andalso List.all (fn name => name = "DISK_THM") oracles
               andalso null axioms
            end))
          thm_to_string
          (fn tm => GEN_SAT_PROVE_ONLY
            (satConfig.set_flag_is_proved false
              (satConfig.set_flag_is_cnf true
                (satConfig.set_term tm satConfig.base_config))))
          ``(P:bool->bool) T /\ ~P T /\ P F /\ ~P F``

val _ = tprint "proof-only explicit CNF rejects SAT without model checking"
val _ = require_msg
          (check_result (fn rejected => rejected))
          Bool.toString
          (fn tm =>
            (ignore (GEN_SAT_PROVE_ONLY
              (satConfig.set_flag_is_cnf true
                (satConfig.set_term tm satConfig.base_config)));
             false)
            handle SAT_satisfiable _ => true)
          ``(P:bool->bool) T /\ ~P F``

(* These controls force the boundary rather than letting a missing external
   solver silently turn a certificate test into an internal DPLL test. *)
local
  open satConfig SatSolvers
  fun checked expected th =
    let val (oracles, axioms) = Tag.dest_tag (tag th)
    in null (hyp th) andalso concl th ~~ expected andalso null axioms
       andalso List.all (fn s => s = "DISK_THM") oracles end
  fun control name action =
    (tprint name;
     require_msg (check_result I) Bool.toString action ())
  fun config cnf = set_flag_is_cnf true (set_term cnf base_config)
  val valid = ``(p /\ q) ==> (q /\ p)``
  val invalid = ``p \/ q``
  val cnf = ``p /\ ~p``
  val compound = ``(P:bool->bool) T /\ ~P F``
  fun sat_only conf =
    (GEN_SAT_PROVE_ONLY conf; false) handle SAT_satisfiable _ => true
  fun model conf goal =
    (GEN_SAT conf; false) handle SAT_cex th =>
      let val (assignment, denied) = dest_imp (concl th)
          val verified = satTools.satCheck (strip_conj assignment) denied
      in checked (concl th) th andalso checked (concl th) verified
         andalso denied ~~ mk_neg goal end
  fun solver_at path =
    let val SatSolver fields = minisatp
    in SatSolver
      {name = #name fields, URL = #URL fields, executable = path,
       post_exe = #post_exe fields, notime_run = #notime_run fields,
       time_run = #time_run fields, post_run = #post_run fields,
       only_true = #only_true fields, failure_string = #failure_string fields,
       start_string = #start_string fields, end_string = #end_string fields}
    end
  val missing = OS.FileSys.tmpName ()
  val _ = OS.FileSys.remove missing
  fun internal conf = set_solver (solver_at missing) conf
  fun measured conf prove =
    let val (result, stats) = satTools.with_solver_statistics
          (fn () => prove conf)
    in result andalso #external_calls stats = 0
       andalso #internal_calls stats = 1 end
  val _ = control "ordinary missing-solver checked UNSAT/model contracts"
    (fn () => measured (internal (set_term valid base_config))
        (fn conf => checked valid (GEN_SAT conf)) andalso
      measured (internal (set_term invalid base_config))
        (fn conf => model conf invalid))
  val _ = control "proof-only missing-solver CNF and compound SAT contracts"
    (fn () => measured (internal (config cnf))
        (fn conf => checked (mk_neg cnf) (GEN_SAT_PROVE_ONLY conf)) andalso
      measured (internal (config compound)) sat_only andalso
      measured (internal (set_term invalid base_config)) sat_only andalso
      sat_only (set_term F base_config))
  val _ = control "proof-only missing-proof fallback preserves explicit CNF"
    (fn () => measured (set_proof missing (config cnf))
        (fn conf => checked (mk_neg cnf) (GEN_SAT_PROVE_ONLY conf)) andalso
      measured (set_proof missing (config compound)) sat_only)
  val _ = control "ordinary missing-proof checked UNSAT/model contracts"
    (fn () => measured
        (set_flag_is_cnf false (set_proof missing
          (set_term valid base_config)))
        (fn conf => checked valid (GEN_SAT conf)) andalso
      measured (set_flag_is_cnf false (set_proof missing
        (set_term invalid base_config))) (fn conf => model conf invalid))

  val trace = OS.FileSys.tmpName ()
  fun with_trace bytes action =
    let val out = BinIO.openOut trace
        val _ = BinIO.output (out, Word8Vector.fromList
          (List.map Word8.fromInt bytes))
        val _ = BinIO.closeOut out
        val result = Exn.capture action (set_proof trace (config cnf))
        val _ = OS.FileSys.remove trace
    in Exn.release result end
  val roots = [2,0,0,4,1,0]
  val forward = [5,2,1,0]
  val backward = [3,1,2,0]
  fun trace_proves bytes problem = with_trace bytes (fn conf =>
    let val (th, stats) = satTools.with_solver_statistics (fn () =>
          GEN_SAT_PROVE_ONLY (set_term problem conf))
    in checked (mk_neg problem) th andalso #internal_calls stats = 0
       andalso #external_calls stats = 0 end)
  fun bad_trace bytes problem = with_trace bytes (fn conf =>
    ((GEN_SAT_PROVE_ONLY (set_term problem conf); false)
     handle HOL_ERR _ => true | Domain => true | Subscript => true))
  val _ = control "binary resolution: both pivots, factoring and deletion"
    (fn () => trace_proves (roots @ forward) cnf andalso
      trace_proves (roots @ backward) cnf andalso
      trace_proves (roots @ forward) ``(p \/ p) /\ ~p`` andalso
      trace_proves (roots @ [3,0] @ forward) cnf)
  val _ = control "binary resolution: malformed/incomplete traces reject"
    (fn () => List.all (fn bytes => bad_trace bytes cnf)
      [[], [128], [2,0], [2,0,0], [0,0,0], [6,0,0],
       roots @ [1,2,1,0], roots @ [5,2,0,0], roots @ [5,1,1,0]]
      andalso bad_trace (roots @ forward) ``p /\ q``)

  val _ = control "ordinary malformed traces retain checked failures"
    (fn () => List.all (fn bytes => with_trace bytes (fn conf =>
      ((GEN_SAT conf; false) handle HOL_ERR _ => true
        | Domain => true | Subscript => true)))
      [[], [128], [2,0], [0,0,0], [6,0,0]])

  (* A deterministic compact replay with a nonempty definition map.  The
     source atom is compound, but resolution must use its schematic name
     until the shared root context has been discharged. *)
  val _ = control "compact resolution discharges roots before expansion"
    (fn () => with_trace (roots @ forward) (fn _ =>
      let
        val x = mk_var ("sat_compact", bool)
        val atom = ``(p:bool) /\ q``
        val source = mk_conj (atom, mk_neg atom)
        val premise = ASSUME source
        val clauses = Array.fromList
          [(x, CONJUNCT1 premise), (mk_neg x, CONJUNCT2 premise)]
        val lfn = Redblackmap.insert
          (Redblackmap.mkDict Term.var_compare, x, atom)
        val sva = Array.fromList [T, x]
        val result = minisatParse.replayProof sva 2 "unused" minisatp 1
          clauses lfn (SOME trace)
      in case result of
          NONE => false
        | SOME th => checked (mk_neg source) (NOT_INTRO (DISCH source th))
      end))
  val _ = control "proof-only file input checks the file endpoint"
    (fn () =>
      let
        val input = OS.FileSys.tmpName ()
        fun put text =
          let val out = TextIO.openOut input
          in TextIO.output (out, text); TextIO.closeOut out end
        val result = Exn.capture (fn () =>
          let
            val _ = put "p cnf 1 2\n1 0\n-1 0\n"
            val problem = dimacsTools.readDimacs input
            val conf = set_infile input (internal base_config)
            val _ = checked (mk_neg problem) (GEN_SAT_PROVE_ONLY conf)
              orelse raise Fail "DIMACS endpoint"
            val _ = put "p cnf 1 1\n1 0\n"
          in sat_only conf end) ()
        val _ = OS.FileSys.remove input
      in Exn.release result end)

  val _ = if not (OS.FileSys.access (getSolverExe minisatp,
                                     [OS.FileSys.A_EXEC])) then () else
    let
      val _ = control "external checked SAT/UNSAT and proof-only SAT"
        (fn () =>
          let val (_, stats) = satTools.with_solver_statistics (fn () =>
                if checked valid (SAT_PROVE valid) andalso
                   model (set_term invalid base_config) invalid andalso
                   sat_only (config compound) then () else raise Fail "SAT")
          in #external_calls stats = 3 andalso #internal_calls stats = 0 end)
      val _ = control "external oracle SAT/UNSAT stays distinct from checked"
        (fn () =>
          let fun oracle th =
                let val (names, axioms) = Tag.dest_tag (tag th)
                in null (hyp th) andalso null axioms andalso
                   List.exists (fn s => s = "HolSatLib") names end
              val th = SAT_ORACLE valid
              val sat = (SAT_ORACLE invalid; false) handle SAT_cex th =>
                oracle th andalso snd (dest_imp (concl th)) ~~ mk_neg invalid
          in concl th ~~ valid andalso oracle th andalso sat end)
    in () end
in
  val _ = ()
end
