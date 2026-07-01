(set-logic QF_FP)
(declare-const fpv RoundingMode)
(assert (= fpv fpv))
(check-sat)
