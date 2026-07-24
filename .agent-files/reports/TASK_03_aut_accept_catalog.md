# TASK_03 — `aut.accept` clause-shape catalog

Date: 2026-07-24

## Result

The P4.1 working hypothesis is **contradicted** by the recorded
clauses.  Z3's state argument is a cursor into the original string,
not the ordinal of a distinct derivative:

```text
aut.accept(s, k, R)  =  str.in_re(DROP k s, R)
```

The regex argument already carries the residual language.  Transitions
read character `k`, increment the cursor to `k + 1`, and pass a
derivative-like residual regex as the third argument.

This interpretation explains every cataloged shape, including
complement, intersection, difference after Z3's rewrite, bounded
loop, and a loop over a nullable body.  It also gives TASK_10 a
definition that is independent of an undocumented automaton
construction order.

Evidence is frozen in validation commit
`18b2576207f19ebd5bd205d39a080ac5512d22c8`.  The baseline corpus
has 14 proof recordings containing `aut.accept`: two on Z3 4.11.2
and three on each later matrix version.

## Notation and shape classes

Write `A(k,R)` for `aut.accept(s,k,R)`, `L` for `str.len s`, and
`c[k]` for `seq.nth_i s k`.

| ID | Normalized emitted shape | Class | P4.1 assessment |
| --- | --- | --- | --- |
| M | `not in_re(s,R) or A(0,R)` | membership-to-accept bridge | consistent with derivative reading, but only at state 0 and therefore non-discriminating |
| B | `A(k,R) ==> L >= k+1` for a non-nullable residual | state-indexed length bound | contradicts |
| T | `not A(k,R) or L <= k or (guard(c[k]) and A(k+1,R'))` | guarded acceptance transition | contradicts |
| N | `not A(k,to_re("")) or L <= k or false` | terminal/nullability fact | contradicts |

The contradiction is structural, not a construction-order mismatch:

- `B` depends on the numeric cursor.  In the complement proof,
  `A(1,re.+ re.allchar)` implies `L >= 2`, although
  `re.+ re.allchar` as a language only requires a one-character
  string.
- `N` occurs with the identical residual `str.to_re ""` at states
  1, 2, and 3.  It accepts the original string only when
  `L <= k`.  A fixed derivative-state interpretation of that regex
  cannot make its language depend on `k`.
- `T` reads `c[k]` and advances to `k+1`.  The third argument changes
  to the residual regex explicitly, so `k` is not selecting that
  residual from a separate construction-order table.

No observed shape merely needs construction-order pinning.  The
construction-order premise itself is the part contradicted by the
evidence.

## Frozen recording catalog by version

The counts below are `th-lemma-seq` applications whose reconstructed
premise or conclusion contains `aut.accept`.

| Z3 | recording | states and shapes | count |
| --- | --- | --- | ---: |
| 4.11.2 | `draft_regex_membership` | range: `M`, `B(0)`, `T(0)`, `N(1)` | 4 |
| 4.11.2 | `draft_re_loop` | loop: `M`, `B(0)`, `T(0..2)`, `N(3)` | 6 |
| 4.11.2 | `draft_re_comp` | no `aut.accept`; proof rewrites directly | 0 |
| 4.12.4 | `draft_regex_membership` | same range shapes as 4.11.2 | 4 |
| 4.12.4 | `draft_re_loop` | same loop shapes as 4.11.2 | 6 |
| 4.12.4 | `draft_re_comp` | complement: `M`, `T(0)`, `B(1)` | 3 |
| 4.13.0 | `draft_regex_membership` | same range shapes as 4.11.2 | 4 |
| 4.13.0 | `draft_re_loop` | same loop shapes as 4.11.2 | 6 |
| 4.13.0 | `draft_re_comp` | same complement shapes as 4.12.4 | 3 |
| 4.14.1 | `draft_regex_membership` | same range shapes as 4.11.2 | 4 |
| 4.14.1 | `draft_re_loop` | same loop shapes as 4.11.2 | 6 |
| 4.14.1 | `draft_re_comp` | same complement shapes as 4.12.4 | 3 |
| 4.15.3 | `draft_regex_membership` | same range shapes as 4.11.2 | 4 |
| 4.15.3 | `draft_re_loop` | same loop shapes as 4.11.2 | 6 |
| 4.15.3 | `draft_re_comp` | same complement shapes as 4.12.4 | 3 |

The raw let-binding numbers change at 4.14.1, but the expanded clauses
do not.  The ground `operator_re_*` recordings avoid `aut.accept`
because Z3 discharges them by rewriting; they are not omitted from
the scan.

### Range

For `R = re.range "a" "z"`:

```text
not in_re(s,R) or A(0,R)
A(0,R) ==> L >= 1
not A(0,R) or L <= 0 or
  (97 <= c[0] and c[0] <= 122 and A(1,to_re("")))
not A(1,to_re("")) or L <= 1 or false
```

The `T` and `N` shapes implement one-character suffix consumption.
They contradict the P4.1 construction-order reading.

### Bounded loop

For `R = ((_ re.loop 1 3) (str.to_re "a"))`, Z3 emits:

```text
not A(0,loop(1,3,"a")) or L <= 0 or
  (c[0] = 97 and A(1,loop(0,2,"a")))
not A(1,loop(0,2,"a")) or L <= 1 or
  (c[1] = 97 and A(2,loop(0,1,"a")))
not A(2,loop(0,1,"a")) or L <= 2 or
  (c[2] = 97 and A(3,to_re("")))
not A(3,to_re("")) or L <= 3 or false
```

Together with `M` and `A(0,R) ==> L >= 1`, these are the six
cataloged applications.  The numeric state follows the consumed
input position even though the residual loop bound changes
independently.  Assessment: **contradicts**.

### Complement

Z3 4.12.4 and newer use this transition for
`R = re.comp(str.to_re "a")`:

```text
not A(0,R) or L <= 0 or
  (c[0] != 97 or A(1,re.+ re.allchar))
A(1,re.+ re.allchar) ==> L >= 2
```

If the first character differs, the complement accepts immediately.
If it equals `a`, the suffix after cursor 1 must be nonempty.  This is
exactly `DROP`-cursor semantics and contradicts P4.1.  Z3 4.11.2
chooses a direct-rewrite proof for this particular frozen input; the
targeted complement-range probe below exercises its automaton path.

## Targeted constructor probes

Four additional proof-producing inputs were run on all five versions:

- `re.inter(range("a","z"), comp(to_re("m")))`, contradicted by
  non-membership in the range;
- `re.diff(re.all, range("m","z"))`, contradicted by membership in
  the removed range;
- `re.comp(range("a","z"))`, contradicted by range membership;
- `loop(1,2,opt(to_re("a")))`, contradicted by length 3.

All 20 runs returned `unsat`, a full proof, and `aut.accept`.

| Z3 | `re.inter` hash | `re.diff` hash | `re.comp` hash | nullable-loop hash |
| --- | --- | --- | --- | --- |
| 4.11.2 | `3b3771114709` | `9b9bd5b0766e` | `696b4997c72c` | `f98c5e412c63` |
| 4.12.4 | `3b3771114709` | `9b9bd5b0766e` | `696b4997c72c` | `f41310ae8e32` |
| 4.13.0 | `3b3771114709` | `9b9bd5b0766e` | `696b4997c72c` | `f41310ae8e32` |
| 4.14.1 | `ce56e93921c3` | `24fd1c231bd5` | `ed752dcf313e` | `6758b99d491f` |
| 4.15.3 | `ce56e93921c3` | `24fd1c231bd5` | `ed752dcf313e` | `6758b99d491f` |

Hashes are the first 12 hex digits of raw Z3 stdout SHA-256.

The probes use the common `QF_S` proof wrapper and these assertion
bodies:

```smt2
; re.inter
(declare-const x String)
(assert (str.in_re x
  (re.inter (re.range "a" "z")
            (re.comp (str.to_re "m")))))
(assert (not (str.in_re x (re.range "a" "z"))))

; re.diff
(declare-const x String)
(assert (str.in_re x
  (re.diff re.all (re.range "m" "z"))))
(assert (str.in_re x (re.range "m" "z")))

; re.comp
(declare-const x String)
(assert (str.in_re x (re.comp (re.range "a" "z"))))
(assert (str.in_re x (re.range "a" "z")))

; nullable re.loop
(declare-const x String)
(assert (str.in_re x
  ((_ re.loop 1 2) (re.opt (str.to_re "a")))))
(assert (= (str.len x) 3))
```

### `re.inter`

The direct intersection state has this `T` instance:

```text
not A(0,inter(range("a","z"),comp(to_re("m")))) or L <= 0 or
  (97 <= c[0] and c[0] <= 122 and c[0] != 109 and
   A(1,to_re("")))
```

The proof also constructs the complement-of-range automaton needed
by the negative assertion.  Assessment: **contradicts**.

### `re.diff`

For the tested `re.diff re.all R`, Z3 first rewrites the regex to
`re.comp R`; no direct `aut.accept(...,re.diff(...))` term remains.
The resulting complement transition is the same `T` family as the
complement-range probe.  The observed inherited shape therefore
**contradicts** P4.1.  Direct difference-state construction is not
needed for replay of this emitted proof shape.

### Nullable bounded loop

Z3 rewrites `re.opt "a"` to `re.union "a" ""`, then emits cursor
transitions:

```text
A(0,loop(1,2,a|eps))  -> L <= 0 or
  (c[0] = 97 and A(1,loop(0,1,a|eps)))
A(1,loop(0,1,a|eps))  -> L <= 1 or
  (c[1] = 97 and A(2,eps))
A(2,eps)               -> L <= 2
```

The state number still tracks consumed input while the nullable
residual is explicit.  Assessment: **contradicts**.

## Reproduction

Direct reruns on the oldest and newest versions reproduced the frozen
stdout byte-for-byte:

| Z3 | range | loop | complement |
| --- | --- | --- | --- |
| 4.11.2 | exact; 4 occurrences | exact; 8 occurrences | exact; 0 occurrences |
| 4.15.3 | exact; 4 occurrences | exact; 8 occurrences | exact; 4 occurrences |

Here "occurrences" counts raw `aut.accept` symbol uses, not reconstructed
theory applications.  The targeted probe hashes above also group
exactly by version family.

## Consequence for TASK_10 and TASK_20

TASK_10 should define the emitted symbol at the cursor abstraction:

```text
aut_accept s k R = smt_in_re (DROP k s) R
```

TASK_20 can then prove `M`, `B`, `T`, and `N` from ordinary membership,
nullability, and derivative equations.  It should not introduce or pin
a Z3 construction-order enumeration.  The catalog exposes no residual
shape requiring a D2 gate.
