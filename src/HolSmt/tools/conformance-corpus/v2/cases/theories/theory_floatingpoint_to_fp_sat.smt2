(set-logic QF_FP)
(assert (= ((_ to_fp 8 24) RNE 1.0) ((_ to_fp 8 24) RNE 1.0)))
(check-sat)
