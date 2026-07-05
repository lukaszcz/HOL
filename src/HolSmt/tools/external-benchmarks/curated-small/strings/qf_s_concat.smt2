; family: strings
; holsmt-expected: {"typecheck-only": {"status": "pass"}, "z3-tac": {"status": "pass"}}
(set-logic QF_S)
(declare-const s String)
(assert (= (str.++ s "") s))
(check-sat)
(exit)
