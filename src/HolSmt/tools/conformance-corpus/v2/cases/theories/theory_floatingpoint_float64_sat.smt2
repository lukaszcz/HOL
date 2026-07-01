(set-logic QF_FP)
(declare-const fpv Float64)
(assert (= fpv fpv))
(check-sat)
