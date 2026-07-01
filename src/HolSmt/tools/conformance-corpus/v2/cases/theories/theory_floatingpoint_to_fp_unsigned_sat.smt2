(set-logic QF_FP)
(assert (= ((_ to_fp_unsigned 8 24) RNE #x00000001) ((_ to_fp_unsigned 8 24) RNE #x00000001)))
(check-sat)
