(set-logic QF_FP)
(assert (= (fp #b0 #x7f #b00000000000000000000000) (fp #b0 #x7f #b00000000000000000000000)))
(check-sat)
