(set-logic QF_NIRA)
(assert (= (to_int (/ 7.0 2.0)) 3))
(check-sat)
