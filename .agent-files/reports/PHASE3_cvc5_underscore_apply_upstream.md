# cvc5 rejects the SMT-LIB 2.7 `_` higher-order application syntax

## Suggested issue title

SMT-LIB 2.7 higher-order `(_ f t)` application is rejected

## Environment

- cvc5 1.3.4, git revision `f3b21c4`
- command: `cvc5 --lang smt2 repro.smt2`

## Minimal reproducer

```smt2
(set-logic HO_QF_UFLIA)
(declare-const g (-> Int (-> Int Int)))
(assert (= (_ (g 1) 2) 3))
(check-sat)
```

Actual result:

```text
(error "Parse Error: repro.smt2:3.15: Expected SMT-LIBv2 symbol, got `(` (LPAREN_TOK).")
```

The cvc5 extension spelling is accepted:

```smt2
(set-logic HO_QF_UFLIA)
(declare-const g (-> Int (-> Int Int)))
(assert (= (@ (g 1) 2) 3))
(check-sat)
```

This prints `sat`.

## Expected behavior

SMT-LIB 2.7, section 3.9 (Higher-order logic), defines explicit
higher-order application using the reserved `_` identifier.  The first input
should therefore parse as application of the function-valued term `(g 1)` to
`2`.  Accepting `@` as a cvc5 extension is useful, but it does not replace
acceptance of the standard spelling when reading SMT-LIB 2.7.

## Impact

Portable SMT-LIB 2.7 producers cannot send standard explicit application to
cvc5.  They must detect cvc5 and substitute `@`, even though their parsers
still need to accept `_` for conformance with the standard.

This report is intentionally only a ready-to-file draft; repository policy
leaves external filing to the owner.
