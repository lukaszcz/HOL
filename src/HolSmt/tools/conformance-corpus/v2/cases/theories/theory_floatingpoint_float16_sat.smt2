(set-logic QF_FP)
(declare-const fpv Float16)
(assert (= fpv fpv))
(check-sat)
