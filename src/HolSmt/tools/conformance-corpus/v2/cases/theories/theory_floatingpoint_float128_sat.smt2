(set-logic QF_FP)
(declare-const fpv Float128)
(assert (= fpv fpv))
(check-sat)
