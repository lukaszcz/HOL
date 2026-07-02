; family: strings
; holsmt-expected: {"typecheck-only": {"status": "fail", "diagnostic": "invalid SMT-LIB input"}, "z3-tac": {"status": "fail", "diagnostic": "invalid SMT-LIB input"}}
(set-logic QF_S)
(declare-const s String)
(assert (= (str.++ s "") s))
(check-sat)
(exit)
