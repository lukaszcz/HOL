; holsmt-expected: {"typecheck-only": {"status": "pass"}}
(set-logic QF_UF)
(declare-const p Bool)
(assert (= p p))
(check-sat)
(exit)
