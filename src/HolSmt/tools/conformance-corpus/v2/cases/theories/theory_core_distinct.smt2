(set-logic QF_UF)
(declare-const a Bool)
(assert (distinct a true))
(check-sat)
