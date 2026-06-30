(set-logic QF_UF)

(declare-sort U 0)
(declare-const a U)
(assert (= a true))
(check-sat)
(exit)
