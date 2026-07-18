# Phase 3 C1: Z3 higher-order proof shapes

Date: 2026-07-18

## Corpus and recording method

The six inputs are Z3-dialect lowerings: function values use nested
`Array` sorts, application uses `select`, and abstractions use Z3's
array `lambda` term. They cover lambda equality, a beta instance,
extensionality over lambdas, a lambda under a quantifier, an
eta-expanded partial application, and a map-valued `ite`.

Each input was recorded with `proof=true` and
`pp.simplify_implies=false` on local Z3 4.11.2, 4.12.4, 4.13.0,
4.14.1, and 4.15.3 executables. All 30 runs returned `unsat` with a
proof. The recorder found no unknown rule heads and no malformed
proof fragments.

Artifacts are under:

```
$HOLSMT_VALIDATION_DIR/tools/proof-corpus/complete/z3-<version>/
```

The complete-corpus manifest pins the shape family for every
case/version in `expected_shape_families`; `--ho-corpus` checks that
matrix and the per-case required rules on every recording.

## Version boundary summary

`verbatim` means lambda terms remain in ordinary proof terms and no
`z3name!k`, `:lambda-def`, or `proof-bind` occurs. `named` means the
proof introduces at least one `z3name!k`, a quantified
`:lambda-def`, and `proof-bind`.

| Case | 4.11.2 | 4.12.4 | 4.13.0 | 4.14.1 | 4.15.3 | Boundary |
|---|---|---|---|---|---|---|
| lambda equality | verbatim | named | named | named | named | 4.11.2 / 4.12.4 |
| beta instance | verbatim | verbatim | verbatim | verbatim | verbatim | none through 4.15.3 |
| lambda extensionality | named | named | named | named | named | before 4.11.2 |
| lambda under quantifier | named | named | named | named | named | before 4.11.2 |
| eta partial application | named | named | named | named | named | before 4.11.2 |
| map-valued `ite` | named | named | named | named | named | before 4.11.2 |

The split is case-dependent, not a single global 4.11-versus-4.14
boundary. The simple equality case changes at 4.12.4, direct beta
reduction stays in the old family in every tested release, and the
four array-extensional cases already use the named family in 4.11.2.

## Rule inventories

The inventories below are exact sets; versions grouped on one line
produced the same set.

### Lambda equality

- **4.11.2:** `asserted`, `monotonicity`, `mp`, `rewrite`, `trans`.
- **4.12.4, 4.13.0, 4.14.1, 4.15.3:** `asserted`, `intro-def`,
  `monotonicity`, `mp`, `mp~`, `nnf-pos`, `proof-bind`, `quant-inst`,
  `quant-intro`, `rewrite`, `trans`, `trans*`, `unit-resolution`.

The named versions contain two `:lambda-def` annotations and two
`proof-bind` occurrences, consumed once each by `nnf-pos` and
`quant-intro`.

### Beta instance

- **4.11.2, 4.12.4, 4.13.0, 4.14.1, 4.15.3:** `asserted`,
  `monotonicity`, `mp`, `rewrite`, `trans`.

All versions retain one verbatim lambda and use no lambda name,
`:lambda-def`, or `proof-bind`.

### Lambda extensionality

- **4.11.2, 4.12.4, 4.13.0, 4.14.1, 4.15.3:** `asserted`,
  `def-axiom`, `hypothesis`, `intro-def`, `lemma`, `monotonicity`,
  `mp`, `mp~`, `nnf-pos`, `proof-bind`, `quant-inst`, `quant-intro`,
  `rewrite`, `th-lemma-array`, `unit-resolution`.

Each version names two lambdas, contains four `:lambda-def`
annotations, and has six `proof-bind` occurrences: three under
`nnf-pos` and three under `quant-intro`.

### Lambda under quantifier

- **4.11.2, 4.12.4, 4.13.0, 4.14.1, 4.15.3:** `asserted`,
  `intro-def`, `monotonicity`, `mp`, `mp~`, `nnf-pos`, `proof-bind`,
  `quant-inst`, `quant-intro`, `rewrite`, `symm`, `th-lemma-array`,
  `trans*`, `unit-resolution`.

Each version names two lambdas, contains two `:lambda-def`
annotations, and has four `proof-bind` occurrences: three under
`nnf-pos` and one under `quant-intro`.

### Eta-expanded partial application

- **4.11.2, 4.12.4, 4.13.0, 4.14.1, 4.15.3:** `asserted`,
  `intro-def`, `monotonicity`, `mp`, `mp~`, `nnf-pos`, `proof-bind`,
  `quant-inst`, `rewrite`, `th-lemma-array`, `unit-resolution`.

Each version names one lambda and has one `:lambda-def` and one
`proof-bind`, consumed by `nnf-pos`.

### Map-valued `ite`

- **4.11.2, 4.12.4, 4.13.0, 4.14.1, 4.15.3:** `asserted`,
  `def-axiom`, `hypothesis`, `intro-def`, `lemma`, `monotonicity`,
  `mp`, `mp~`, `nnf-pos`, `proof-bind`, `quant-inst`, `quant-intro`,
  `rewrite`, `symm`, `th-lemma-array`, `trans*`, `unit-resolution`.

Each version names one lambda, contains two `:lambda-def`
annotations, and has two `proof-bind` occurrences: one under
`nnf-pos` and one under `quant-intro`.

## Exact binder and lambda-definition forms

Generated identifiers differ by version and are not stable API.
Modulo those identifiers, structure is stable across every version in
the named family. The recorder stores every occurrence, not a
truncated sample, in `proof.ho_shape.proof_binds` and
`proof.ho_shape.lambda_def_axioms`.

A `proof-bind` is a unary proof wrapper. Representative exact 4.15.3
terms and their enclosing forms are:

```smt2
(proof-bind ?x67)
(proof-bind ?x80)
(nnf-pos (proof-bind ?x67) (~ $x58 $x58))
(quant-intro (proof-bind ?x80) (= $x58 $x79))
```

The direct beta case has neither form. The named cases use the same
wrapper under `nnf-pos`; all except eta also use it under
`quant-intro`.

Lambda equality emits both arithmetic and let-normalized definitions:

```smt2
(! (= (+ x (* (- 1) (select z3name!0 x))) (- 1))
   :pattern ( (select z3name!0 x) ) :qid :lambda-def)

(! (let ((?x55 (select z3name!0 x)))
     (let ((?x30 (+ 1 x)))
       (= ?x30 ?x55)))
   :pattern ( (select z3name!0 x) ) :qid :lambda-def)
```

Extensionality emits a negated pointwise equation and its
let-normalized companion for each named lambda:

```smt2
(! (not (= (select f x) (select z3name!0 x)))
   :pattern ( (select z3name!0 x) ) :qid :lambda-def)

(! (let (($x61 (select z3name!0 x)))
     (let (($x25 (select f x)))
       (let (($x31 (not $x25)))
         (= $x31 $x61))))
   :pattern ( (select z3name!0 x) ) :qid :lambda-def)
```

The quantified-lambda case shows both a closed instantiation and a
function-valued lambda name:

```smt2
(! (let ((?x83 (select z3name!1 y)))
     (let ((?x36 (select u a)))
       (let ((?x37 (select ?x36 y)))
         (= ?x37 ?x83))))
   :pattern ( (select z3name!1 y) ) :qid :lambda-def)

(! (let ((?x59 (select (z3name!0 k!00) y)))
     (let ((?x29 (select (select u k!00) y)))
       (= ?x29 ?x59)))
   :pattern ( (select (z3name!0 k!00) y) ) :qid :lambda-def)
```

Eta uses a pointwise equality to the extensionality witness:

```smt2
(! (let ((?x47 (select z3name!1 y)))
     (let ((?x50 (select k!00 y)))
       (= ?x50 ?x47)))
   :pattern ( (select z3name!1 y) ) :qid :lambda-def)
```

Map-valued `ite` emits a conditional pointwise relation and a
let-normalized definition:

```smt2
(! (ite c
        (= (select f x) (select z3name!0 x))
        (= (select g x) (select z3name!0 x)))
   :pattern ( (select z3name!0 x) ) :qid :lambda-def)

(! (let ((?x48 (select z3name!0 x)))
     (let ((?x29 (select g x)))
       (let ((?x28 (select f x)))
         (let ((?x30 (ite c ?x28 ?x29)))
           (= ?x30 ?x48)))))
   :pattern ( (select z3name!0 x) ) :qid :lambda-def)
```

## Replay status and downstream implications

C1 found no previously unknown rule heads: every head in the 30 HO
proofs was already in `KNOWN_RULES` and `RULE_PREMISE_KIND`.
`proof-bind` is the HO-specific unsupported head. It remains registered
as a one-premise parse-only rule and is deliberately absent from
`REPLAY_SUPPORTED_RULES`. The existing heads `intro-def`, `nnf-pos`,
and `quant-intro` remain replay-supported, but their use with lambda
definitions is not evidence that the combined HO shape replays.

TASK_14 must preserve the bound proof term instead of treating
`proof-bind` as an identity shim. TASK_15 must reconstruct the
`:lambda-def` equations, beta/eta conversion, and congruence under
abstractions. In particular, it must not version-gate all HO proofs at
one global release boundary: the case matrix above is the gate.

## Verification evidence

- Fresh `smtheap` and HolSmt drivers built successfully.
- The two focused Python test modules pass (36 tests).
- The recorder's `--ho-corpus` gate passes on all five versions.
- The complete conformance run restricted to logic `ALL` reports 12
  expected HO red obligations in `function sorts`, all five proof
  version steps passing, and 0 unexpected regressions. Its overall
  status remains red/infrastructure because the phase intentionally
  has red obligations and the `ALL` filter selects no external cases.
