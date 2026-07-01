(set-logic QF_NIRA)
(assert (= (+ (to_real 2) 1.5) 3.5))
(check-sat)
