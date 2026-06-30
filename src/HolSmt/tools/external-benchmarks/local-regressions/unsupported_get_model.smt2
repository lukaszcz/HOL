; family: unsupported-queries
; holsmt-expected: {"z3-tac": {"status": "unsupported", "diagnostic": "get-model is outside checked Z3_TAC"}}
(set-logic QF_UF)
(declare-const p Bool)
(assert p)
(check-sat)
(get-model)
(exit)
