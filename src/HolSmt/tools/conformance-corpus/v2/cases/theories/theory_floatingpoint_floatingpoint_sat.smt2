(set-logic QF_FP)
(declare-const fpv (_ FloatingPoint 8 24))
(assert (= fpv fpv))
(check-sat)
