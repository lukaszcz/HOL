(set-logic QF_FP)
(declare-const fpv Float32)
(assert (= fpv fpv))
(check-sat)
