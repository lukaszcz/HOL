"""The TASK31 cases: what the identity, allocation and timing gates cover.

Data only, so the identity gate (task31_identity_grid.py), the timing table
(task31_grid.py) and the allocation matrix (allocation_matrix.py, task
`task31`) cannot disagree about which cells are in scope. The scope is the
`ClientPerformance.sml` cases of matrix.json that TASK_31 gates: the
traversal and tactic cases (the `downstream_*` cases belong to TASK_32/33).
Their sizes come from the matrix ledger: a `singleton` case has the one size
0, a `depth` case 0/1/10/100 and an `assumptions` case 0/1/10/100/1000/10000.
That is 6 singleton and 5 depth traversal cases (26 cells) and 14 tactic
families of 3 stages (252 cells), 278 cells in all. CASES is the order of the
matrix ledger, and the canonical order of every gate.

The reviewed differences from the baseline are not here but in
task31_attributed.json (task31_attribution.py), which no count is sealed to.
"""

TRAVERSAL_SINGLETON = (
    "traversal_construct", "traversal_context_construct",
    "traversal_complete", "traversal_reuse_hit", "traversal_reuse_miss",
    "traversal_weakening")
TRAVERSAL_DEPTH = (
    "traversal_deep", "traversal_congruence", "traversal_side_conditions",
    "traversal_failed_candidates", "traversal_saved")
TRAVERSAL = TRAVERSAL_SINGLETON + TRAVERSAL_DEPTH
STAGES = ("construct", "reuse", "complete")
# The families that stay cheap at every size, and the eleven whose
# application is quadratic or worse in the assumptions.
LIGHT_FAMILIES = ("supplied", "installed", "asm")
HEAVY_FAMILIES = (
    "full", "reverse", "no_strip_full", "no_strip_reverse", "global", "req0",
    "reqd", "req0_reqd", "reqd_req0", "dependency_full",
    "dependency_reverse")
FAMILIES = LIGHT_FAMILIES + HEAVY_FAMILIES
TACTICS = tuple("tactic_%s_%s" % (family, stage) for family in FAMILIES
                for stage in STAGES)
CASES = TRAVERSAL + TACTICS
# The depth of a traversal case, and the number of assumptions, that the
# timing sample takes.
SAMPLE_DEPTH = 100
SAMPLE_ASSUMPTIONS = 100

# The timing sample (gate 3), 28 cells: every traversal case (the singletons
# at their one size 0, the depth cases at depth 100), the `complete` stage of
# each of the 14 tactic families at 100 assumptions, and three cells at 1000
# assumptions.
SAMPLE = (
    tuple("%s-0" % case for case in TRAVERSAL_SINGLETON) +
    tuple("%s-%d" % (case, SAMPLE_DEPTH) for case in TRAVERSAL_DEPTH) +
    tuple("tactic_%s_complete-%d" % (family, SAMPLE_ASSUMPTIONS)
          for family in FAMILIES) +
    ("tactic_supplied_complete-1000", "tactic_asm_complete-1000",
     "tactic_installed_reuse-1000"))
SAMPLE_CASES = tuple(dict.fromkeys(cell.rsplit("-", 1)[0]
                                   for cell in SAMPLE))

# The infeasible cells: the 33 cells of the eleven heavy families at 10000
# assumptions, which exceed the process timeout of a cell. They are not timed
# and not allocation-counted; the identity gate covers them by the closure of
# their case, which is the same for every size (PROTOCOL.md, "TASK31"), and
# the disposition cites the cost survey it is given (`--survey`).
INFEASIBLE = tuple(
    "tactic_%s_%s-10000" % (family, stage)
    for family in HEAVY_FAMILIES for stage in STAGES)
# The same cells as (case, size) pairs, as the allocation matrix names them.
INFEASIBLE_CELLS = tuple((cell.rsplit("-", 1)[0], int(cell.rsplit("-", 1)[1]))
                         for cell in INFEASIBLE)
# The timeout of an infeasible cell's process, in seconds.
PROCESS_TIMEOUT = 1800

# The repository files every cell's process elaborates (`use`), whose git
# blobs the timing table compares at the baseline and at the candidate (the
# sources of the table, see timing_grid.Table). SOURCES is derived, not
# chosen: the union of the files the runner's loaded-source audit records for
# the cells, mapped to the tracked source each is built from (a generated
# `XTheory.sml` to its `XScript.sml`).
# `task31_identity_grid.py sources --output DIR` prints it from an identity
# grid, and the full grid is inconclusive if a
# file elaborated is missing here (`uncovered`) or a file here is elaborated
# by no cell (`unused_sources`), so the list is exact. The files of the
# initial heap are not listed: the identity grid derives them from the
# receipts of every cell. It holds the 33 simplifier sources and the shared
# modules that the private build recompiles against them.
ELABORATED = (
    "src/1/BoolExtractShared.sig", "src/1/BoolExtractShared.sml",
    "src/1/Mutual.sig", "src/1/Mutual.sml", "src/1/bnfBase.sig",
    "src/1/bnfBase.sml", "src/1/bnfBase_dtype.sml", "src/1/newtypeTools.sig",
    "src/1/newtypeTools.sml", "src/1/parse_bnf.sig", "src/1/parse_bnf.sml",
    "src/1/wlogLib.sig", "src/1/wlogLib.sml", "src/HolSat/HolSatLib.sig",
    "src/HolSat/HolSatLib.sml", "src/HolSat/SatSolvers.sml",
    "src/HolSat/def_cnf.sig", "src/HolSat/def_cnf.sml",
    "src/HolSat/dimacsTools.sml", "src/HolSat/dpll.sml",
    "src/HolSat/minisatParse.sml", "src/HolSat/minisatProve.sig",
    "src/HolSat/minisatProve.sml", "src/HolSat/minisatResolve.sml",
    "src/HolSat/satCommonTools.sml", "src/HolSat/satConfig.sig",
    "src/HolSat/satConfig.sml", "src/HolSat/satScript.sml",
    "src/HolSat/satTools.sml", "src/IndDef/CoIndDefLib.sig",
    "src/IndDef/CoIndDefLib.sml", "src/IndDef/IndDefLib.sig",
    "src/IndDef/IndDefLib.sml", "src/IndDef/IndDefRules.sig",
    "src/IndDef/IndDefRules.sml", "src/IndDef/InductiveDefinition.sig",
    "src/IndDef/InductiveDefinition.sml",
    "src/IndDef/InductiveDefinitionContextScript.sml",
    "src/IndDef/KeyedThmSet.sig", "src/IndDef/KeyedThmSet.sml",
    "src/basicProof/BasicProvers.sig", "src/basicProof/BasicProvers.sml",
    "src/boss/bossLib.sig", "src/boss/bossLib.sml",
    "src/combin/combinScript.sml", "src/combin/combinSyntax.sig",
    "src/combin/combinSyntax.sml", "src/combin/combinpp.sig",
    "src/combin/combinpp.sml", "src/compute/src/clauses.sig",
    "src/compute/src/clauses.sml", "src/compute/src/computeLib.sig",
    "src/compute/src/computeLib.sml", "src/compute/src/compute_rules.sig",
    "src/compute/src/compute_rules.sml", "src/compute/src/equations.sml",
    "src/coretypes/DefnBase.sig", "src/coretypes/DefnBase.sml",
    "src/coretypes/PairRules.sig", "src/coretypes/PairRules.sml",
    "src/coretypes/PairedLambda.sig", "src/coretypes/PairedLambda.sml",
    "src/coretypes/oneScript.sml", "src/coretypes/oneSyntax.sig",
    "src/coretypes/oneSyntax.sml", "src/coretypes/optionScript.sml",
    "src/coretypes/optionSimps.sig", "src/coretypes/optionSimps.sml",
    "src/coretypes/optionSyntax.sig", "src/coretypes/optionSyntax.sml",
    "src/coretypes/pairLib.sig", "src/coretypes/pairLib.sml",
    "src/coretypes/pairScript.sml", "src/coretypes/pairSimps.sig",
    "src/coretypes/pairSimps.sml", "src/coretypes/pairSyntax.sig",
    "src/coretypes/pairSyntax.sml", "src/coretypes/pairTools.sig",
    "src/coretypes/pairTools.sml", "src/coretypes/pairToolsContextScript.sml",
    "src/coretypes/sumScript.sml", "src/coretypes/sumSimps.sig",
    "src/coretypes/sumSimps.sml", "src/coretypes/sumSyntax.sig",
    "src/coretypes/sumSyntax.sml", "src/datatype/Datatype.sig",
    "src/datatype/Datatype.sml", "src/datatype/DatatypeSimps.sig",
    "src/datatype/DatatypeSimps.sml", "src/datatype/EnumType.sig",
    "src/datatype/EnumType.sml", "src/datatype/EnumTypeContextScript.sml",
    "src/datatype/bnfDatatypeLib.sig", "src/datatype/bnfDatatypeLib.sml",
    "src/datatype/bnfFixBNFScript.sml", "src/datatype/bnfFixLib.sig",
    "src/datatype/bnfFixLib.sml", "src/datatype/bnfInitialScript.sml",
    "src/datatype/bnfLib.sig", "src/datatype/bnfLib.sml",
    "src/datatype/bnfMutualScript.sml", "src/datatype/bnfPrelimsScript.sml",
    "src/datatype/legacyInduction.sig", "src/datatype/legacyInduction.sml",
    "src/datatype/record/RecordType.sig",
    "src/datatype/record/RecordType.sml", "src/list/src/ListConv1.sig",
    "src/list/src/ListConv1.sml", "src/list/src/indexedListsScript.sml",
    "src/list/src/indexedListsSimps.sig",
    "src/list/src/indexedListsSimps.sml", "src/list/src/listLib.sig",
    "src/list/src/listLib.sml", "src/list/src/listScript.sml",
    "src/list/src/listSimps.sig", "src/list/src/listSimps.sml",
    "src/list/src/listSyntax.sig", "src/list/src/listSyntax.sml",
    "src/list/src/rich_listScript.sml", "src/list/src/rich_listSimps.sig",
    "src/list/src/rich_listSimps.sml", "src/list/src/rich_listSyntax.sig",
    "src/list/src/rich_listSyntax.sml", "src/lite/liteLib.sig",
    "src/lite/liteLib.sml", "src/marker/markerLib.sig",
    "src/marker/markerLib.sml", "src/marker/markerScript.sml",
    "src/marker/markerSyntax.sig", "src/marker/markerSyntax.sml",
    "src/meson/src/Canon_Port.sig", "src/meson/src/Canon_Port.sml",
    "src/meson/src/Canon_Port_ContextScript.sml",
    "src/meson/src/jrhTactics.sig", "src/meson/src/jrhTactics.sml",
    "src/meson/src/mesonLib.sig", "src/meson/src/mesonLib.sml",
    "src/meson/src/mesonLibContextScript.sml", "src/metis/folMapping.sig",
    "src/metis/folMapping.sml", "src/metis/folMappingContextScript.sml",
    "src/metis/folTools.sig", "src/metis/folTools.sml",
    "src/metis/folToolsContextScript.sml", "src/metis/matchTools.sig",
    "src/metis/matchTools.sml", "src/metis/metisLib.sig",
    "src/metis/metisLib.sml", "src/metis/metisTools.sig",
    "src/metis/metisTools.sml", "src/metis/mlibCanon.sig",
    "src/metis/mlibCanon.sml", "src/metis/mlibClause.sig",
    "src/metis/mlibClause.sml", "src/metis/mlibClauseset.sig",
    "src/metis/mlibClauseset.sml", "src/metis/mlibHeap.sig",
    "src/metis/mlibHeap.sml", "src/metis/mlibKernel.sig",
    "src/metis/mlibKernel.sml", "src/metis/mlibLiteralnet.sig",
    "src/metis/mlibLiteralnet.sml", "src/metis/mlibMatch.sig",
    "src/metis/mlibMatch.sml", "src/metis/mlibMeson.sig",
    "src/metis/mlibMeson.sml", "src/metis/mlibMeter.sig",
    "src/metis/mlibMeter.sml", "src/metis/mlibMetis.sig",
    "src/metis/mlibMetis.sml", "src/metis/mlibModel.sig",
    "src/metis/mlibModel.sml", "src/metis/mlibMultiset.sig",
    "src/metis/mlibMultiset.sml", "src/metis/mlibOmega.sig",
    "src/metis/mlibOmega.sml", "src/metis/mlibOmegaint.sig",
    "src/metis/mlibOmegaint.sml", "src/metis/mlibParser.sig",
    "src/metis/mlibParser.sml", "src/metis/mlibPatricia.sig",
    "src/metis/mlibPatricia.sml", "src/metis/mlibPortable.sig",
    "src/metis/mlibPortable.sml", "src/metis/mlibResolution.sig",
    "src/metis/mlibResolution.sml", "src/metis/mlibRewrite.sig",
    "src/metis/mlibRewrite.sml", "src/metis/mlibSolver.sig",
    "src/metis/mlibSolver.sml", "src/metis/mlibStream.sig",
    "src/metis/mlibStream.sml", "src/metis/mlibSubst.sig",
    "src/metis/mlibSubst.sml", "src/metis/mlibSubsume.sig",
    "src/metis/mlibSubsume.sml", "src/metis/mlibSupport.sig",
    "src/metis/mlibSupport.sml", "src/metis/mlibTerm.sig",
    "src/metis/mlibTerm.sml", "src/metis/mlibTermnet.sig",
    "src/metis/mlibTermnet.sml", "src/metis/mlibTermorder.sig",
    "src/metis/mlibTermorder.sml", "src/metis/mlibThm.sig",
    "src/metis/mlibThm.sml", "src/metis/mlibTptp.sig",
    "src/metis/mlibTptp.sml", "src/metis/mlibUnits.sig",
    "src/metis/mlibUnits.sml", "src/metis/mlibUseful.sig",
    "src/metis/mlibUseful.sml", "src/metis/normalForms.sig",
    "src/metis/normalForms.sml", "src/metis/normalFormsContextScript.sml",
    "src/metis/normalFormsScript.sml", "src/num/arith/src/Arith.sig",
    "src/num/arith/src/Arith.sml", "src/num/arith/src/Arith_cons.sig",
    "src/num/arith/src/Arith_cons.sml", "src/num/arith/src/Exists_arith.sig",
    "src/num/arith/src/Exists_arith.sml",
    "src/num/arith/src/GenPolyCanon.sig",
    "src/num/arith/src/GenPolyCanon.sml", "src/num/arith/src/GenRelNorm.sml",
    "src/num/arith/src/Gen_arith.sig", "src/num/arith/src/Gen_arith.sml",
    "src/num/arith/src/Instance.sig", "src/num/arith/src/Instance.sml",
    "src/num/arith/src/Int_extra.sig", "src/num/arith/src/Int_extra.sml",
    "src/num/arith/src/Norm_arith.sig", "src/num/arith/src/Norm_arith.sml",
    "src/num/arith/src/Norm_bool.sig", "src/num/arith/src/Norm_bool.sml",
    "src/num/arith/src/Norm_ineqs.sig", "src/num/arith/src/Norm_ineqs.sml",
    "src/num/arith/src/NumRelNorms.sig", "src/num/arith/src/NumRelNorms.sml",
    "src/num/arith/src/Prenex.sig", "src/num/arith/src/Prenex.sml",
    "src/num/arith/src/RJBConv.sig", "src/num/arith/src/RJBConv.sml",
    "src/num/arith/src/Rationals.sig", "src/num/arith/src/Rationals.sml",
    "src/num/arith/src/Sol_ranges.sig", "src/num/arith/src/Sol_ranges.sml",
    "src/num/arith/src/Solve.sig", "src/num/arith/src/Solve.sml",
    "src/num/arith/src/Solve_ineqs.sig", "src/num/arith/src/Solve_ineqs.sml",
    "src/num/arith/src/SubAndCondContextScript.sml",
    "src/num/arith/src/Sub_and_cond.sig",
    "src/num/arith/src/Sub_and_cond.sml", "src/num/arith/src/Sup_Inf.sig",
    "src/num/arith/src/Sup_Inf.sml", "src/num/arith/src/Term_coeffs.sig",
    "src/num/arith/src/Term_coeffs.sml", "src/num/arith/src/Theorems.sig",
    "src/num/arith/src/Theorems.sml", "src/num/arith/src/Thm_convs.sig",
    "src/num/arith/src/Thm_convs.sml", "src/num/arith/src/numSimps.sig",
    "src/num/arith/src/numSimps.sml",
    "src/num/extra_theories/dividesScript.sml",
    "src/num/extra_theories/numpairScript.sml", "src/num/numLib.sig",
    "src/num/numLib.sml", "src/num/reduce/conv/Arithconv.sig",
    "src/num/reduce/conv/Arithconv.sml", "src/num/reduce/src/Boolconv.sig",
    "src/num/reduce/src/Boolconv.sml",
    "src/num/reduce/src/BoolconvContextScript.sml",
    "src/num/reduce/src/reduceLib.sig", "src/num/reduce/src/reduceLib.sml",
    "src/num/reduce/src/reduceScript.sml",
    "src/num/termination/TotalDefn.sig", "src/num/termination/TotalDefn.sml",
    "src/num/theories/NumConvContextScript.sml",
    "src/num/theories/Num_conv.sig", "src/num/theories/Num_conv.sml",
    "src/num/theories/WhileScript.sml",
    "src/num/theories/arithmeticScript.sml", "src/num/theories/basicSize.sml",
    "src/num/theories/basicSizeScript.sml",
    "src/num/theories/basicSizeSyntax.sig",
    "src/num/theories/basicSizeSyntax.sml", "src/num/theories/cvScript.sml",
    "src/num/theories/cv_compute/cvSyntax.sig",
    "src/num/theories/cv_compute/cvSyntax.sml",
    "src/num/theories/cv_compute/cv_computeLib.sig",
    "src/num/theories/cv_compute/cv_computeLib.sml",
    "src/num/theories/cv_compute/tailrecLib.sig",
    "src/num/theories/cv_compute/tailrecLib.sml",
    "src/num/theories/numScript.sml", "src/num/theories/numSyntax.sig",
    "src/num/theories/numSyntax.sml", "src/num/theories/numeralScript.sml",
    "src/num/theories/prim_recScript.sml", "src/parse/CharSet.sig",
    "src/parse/CharSet.sml", "src/parse/ParseDatatype.sig",
    "src/parse/ParseDatatype.sml", "src/parse/ParseDatatype_dtype.sml",
    "src/parse/testutils.sig", "src/parse/testutils.sml",
    "src/pattern_matches/constrFamiliesLib.sig",
    "src/pattern_matches/constrFamiliesLib.sml",
    "src/pattern_matches/parsePMATCH.sig",
    "src/pattern_matches/parsePMATCH.sml",
    "src/pattern_matches/patternMatchesLib.sig",
    "src/pattern_matches/patternMatchesLib.sml",
    "src/pattern_matches/patternMatchesScript.sml",
    "src/pattern_matches/patternMatchesSyntax.sig",
    "src/pattern_matches/patternMatchesSyntax.sml",
    "src/portableML/Arbint.sig", "src/portableML/Arbint.sml",
    "src/portableML/Streams.sig", "src/portableML/Streams.sml",
    "src/portableML/poly/Arbintcore.sig",
    "src/portableML/poly/Arbintcore.sml", "src/portableML/poly/Dynarray.sig",
    "src/portableML/poly/Dynarray.sml", "src/portableML/poly/Intmap.sig",
    "src/portableML/poly/Intmap.sml", "src/portableML/poly/Intset.sig",
    "src/portableML/poly/Intset.sml", "src/portableML/poly/Random.sig",
    "src/portableML/poly/Random.sml", "src/pred_set/src/PFset_conv.sig",
    "src/pred_set/src/PFset_conv.sml", "src/pred_set/src/PGspec.sig",
    "src/pred_set/src/PGspec.sml", "src/pred_set/src/PSet_ind.sig",
    "src/pred_set/src/PSet_ind.sml",
    "src/pred_set/src/cardinalityCoreScript.sml",
    "src/pred_set/src/hurdUtilsContextScript.sml",
    "src/pred_set/src/ordinalBasicScript.sml",
    "src/pred_set/src/permutesScript.sml", "src/pred_set/src/pred_setLib.sig",
    "src/pred_set/src/pred_setLib.sml", "src/pred_set/src/pred_setScript.sml",
    "src/pred_set/src/pred_setSimps.sig",
    "src/pred_set/src/pred_setSimps.sml",
    "src/pred_set/src/pred_setSyntax.sig",
    "src/pred_set/src/pred_setSyntax.sml", "src/pred_set/src/pred_setpp.sig",
    "src/pred_set/src/pred_setpp.sml",
    "src/pred_set/src/set_relationScript.sml",
    "src/pred_set/src/wellorderScript.sml", "src/q/Q.sig", "src/q/Q.sml",
    "src/q/QLib.sig", "src/q/QLib.sml", "src/quantHeuristics/ConseqConv.sig",
    "src/quantHeuristics/ConseqConv.sml",
    "src/quantHeuristics/ConseqConvScript.sml",
    "src/quantHeuristics/quantHeuristicsLib.sig",
    "src/quantHeuristics/quantHeuristicsLib.sml",
    "src/quantHeuristics/quantHeuristicsLibBase.sig",
    "src/quantHeuristics/quantHeuristicsLibBase.sml",
    "src/quantHeuristics/quantHeuristicsLibFunRemove.sig",
    "src/quantHeuristics/quantHeuristicsLibFunRemove.sml",
    "src/quantHeuristics/quantHeuristicsLibParameters.sig",
    "src/quantHeuristics/quantHeuristicsLibParameters.sml",
    "src/quantHeuristics/quantHeuristicsLibSimple.sig",
    "src/quantHeuristics/quantHeuristicsLibSimple.sml",
    "src/quantHeuristics/quantHeuristicsScript.sml",
    "src/quantHeuristics/quantHeuristicsTools.sig",
    "src/quantHeuristics/quantHeuristicsTools.sml",
    "src/quotient/src/quotientScript.sml", "src/refute/AC.sig",
    "src/refute/AC.sml", "src/refute/Canon.sig", "src/refute/Canon.sml",
    "src/refute/canonContextScript.sml", "src/refute/refuteLib.sig",
    "src/refute/refuteLib.sml", "src/relation/relationScript.sml",
    "src/simp/src/Cache.sig", "src/simp/src/Cache.sml",
    "src/simp/src/Cond_rewr.sig", "src/simp/src/Cond_rewr.sml",
    "src/simp/src/Opening.sig", "src/simp/src/Opening.sml",
    "src/simp/src/Satisfy.sig", "src/simp/src/Satisfy.sml",
    "src/simp/src/SatisfySimps.sig", "src/simp/src/SatisfySimps.sml",
    "src/simp/src/Sequence.sig", "src/simp/src/Sequence.sml",
    "src/simp/src/Trace.sig", "src/simp/src/Trace.sml",
    "src/simp/src/Traverse.sig", "src/simp/src/Traverse.sml",
    "src/simp/src/Travrules.sig", "src/simp/src/Travrules.sml",
    "src/simp/src/Unify.sig", "src/simp/src/Unify.sml",
    "src/simp/src/Unwind.sig", "src/simp/src/Unwind.sml",
    "src/simp/src/boolSimps.sig", "src/simp/src/boolSimps.sml",
    "src/simp/src/boolSimpsContextScript.sml", "src/simp/src/combinSimps.sig",
    "src/simp/src/combinSimps.sml", "src/simp/src/poly/BloomApprox.sig",
    "src/simp/src/poly/BloomApprox.sml", "src/simp/src/pureSimps.sig",
    "src/simp/src/pureSimps.sml", "src/simp/src/simpLib.sig",
    "src/simp/src/simpLib.sml", "src/taut/tautLib.sig",
    "src/taut/tautLib.sml", "src/tfl/src/Defn.sig", "src/tfl/src/Defn.sml",
    "src/tfl/src/Extract.sig", "src/tfl/src/Extract.sml",
    "src/tfl/src/Induction.sig", "src/tfl/src/Induction.sml",
    "src/tfl/src/Rules.sig", "src/tfl/src/Rules.sml",
    "src/tfl/src/wfrecUtils.sig", "src/tfl/src/wfrecUtils.sml",
    "src/unwind/unwindLib.sig", "src/unwind/unwindLib.sml",)
SOURCES = tuple(sorted(set(ELABORATED)))
