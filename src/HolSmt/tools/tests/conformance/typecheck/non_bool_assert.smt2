; holsmt-expected: {"typecheck-only": {"status": "fail", "diagnostic": "expected sort :bool, actual sort :int"}}
(set-logic QF_LIA)
(assert 1)
(check-sat)
(exit)
