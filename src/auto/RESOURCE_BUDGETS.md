# Automation work budgets

`searchBudget` belongs to one invocation. A caller passes the same budget to
nested consumers; no backend resets its counters. Each dimension has an
optional nonnegative limit. `SOME 0` rejects the first charge, `NONE` is
unbounded, and negative limits or extensions are errors. Charges happen
before the admitted work. A yield retains usage, and extending that budget
does not reset it. Semantic depth bounds remain separate from these counts.

The implemented checkpoints are:

- Literal fact insertion: candidate charges on subterm scans, head and
  type matches, and duplicate/support comparisons; normalization charges
  on theorem specialization and type instances; application charges on
  admitted assumptions. The ordinary insertion entry point is unchanged.
- Clasimp's opt-in child-first traversal: normalization charges before
  congruence descent, weakening, and reducer attempts. AUTO, FORCE,
  FASTFORCE, SLOWSIMP, BESTSIMP, and CLARSIMP share one callback across
  their mutual simplification and search wrappers per tactic invocation.
  `CLARSIMP_TAC_BUDGETED` accepts a caller-owned budget and propagates
  `LimitReached` without translating it into tactic failure. Separate
  normalization steps such as FORCE's initial `FULL_SIMP_TAC` and
  extensionality are not yet charged by this callback.
- Classical best-first: candidate charges on heap selections, lazy child
  pulls, and forward-rule premise scans; application charges on node
  expansion; normalization charges before kernel replay.
- Aesop: candidate charges on forward-rule premise scans, ordinary
  introduction/elimination-major attempts, and rendered-tactic or
  multi-step alternative pulls; application charges on committed safe
  rules and installed unsafe alternatives; normalization charges on each
  normalization-rule scan.
- BLAST fixed-depth: candidate charges at cooperative scan and unification
  checkpoints; application charges on committed tableau transitions;
  normalization charges at term normalization and equality substitution.
- Order: candidate charges during source-theorem and conjunct
  classification, relation grouping, axiom lookup, graph scans, and
  reachability; application charges on derived rules, chained edges, and
  closures; normalization charges on context and fact reduction, conjunct
  splitting, and goal reduction.
- Linarith full proof search, certificate search, and replay: candidate
  charges on coefficient, atom, row, disjunction, and case scans;
  application charges on row-pair elimination, disequality branches,
  and search nodes; normalization charges on decomposition, row
  construction, preprocessing, augmentation, and justification replay.

Classical and Aesop candidate yields retain their search sessions. Classical
also retains a candidate awaiting kernel replay when the normalization limit
is reached. A nested expansion cutoff is terminal when that expansion does
not provide a cursor. BLAST restores its mutable trail on a limit and has a
one-shot fixed-depth result; order returns a one-shot proved, exhausted, or
limit result. Existing tactic, depth, and order entry points keep their
compatibility behavior.

Aesop's ordinary claset rule and forward-rule cursors retain their partial
scan across a candidate yield, including the uniqueness check for
deterministic safe rules. A rendered tactic is charged before its callback
starts; work inside an arbitrary callback remains the callback's own
responsibility. Forward duplicate filtering compares existing assumptions
in the candidate's arriving substitution. It compares alternative
results in their common parent substitution only when bindings of
pre-existing metavariables agree.

Aesop keys saved scans by the tactic registry generation. Replacing a
registered rule during a yielded budget session restarts its tree search
from the original goal under the same budget, so repeated work is charged.
An unchanged registry resumes its pending alternatives in place.

Aesop's budgeted session retains the explicit proof context for rendered
tactic rules across yields, including interleaved sessions. Contextual
engine rules, including Aesop's built-in disch, gen, and hypothesis
substitution, retain that context when lazy alternatives are forced.
Convenience search entry points snapshot the ambient context once at
invocation. Classical safe, clarify, fast, best, A*, first-best, and
depth searches pass the tactic context to their wrappers and built-in
safe tactic calls. Internal hypothesis substitution uses that context.
Exact BLAST reconstruction and recursive kernel replay use the supplied
context and propagate interrupts and typed work cutoffs to their callers.

Linarith's budgeted proof entry point includes splitting and carries an
explicit tactic context through nested forward side proofs without a
nested ambient pin. `LINARITH_TAC_BUDGETED` and
`CFG_LINARITH_TAC_BUDGETED` also charge the caller's budget through the
full tactic search. `SIMPLE_LINARITH_TAC_BUDGETED` charges its direct
refutation path. All three propagate a typed work-limit exception. They are
one-shot tactics: extending the budget permits a retry but does not
resume a suspended split tree. The existing tactic and simplifier
adapters retain their unbudgeted behavior. These are G5 integration
tasks, not exhaustive-search outcomes.
