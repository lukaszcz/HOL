(set-logic QF_NRA)

(assert (= (/ 6.0 3.0) 2.0))
(assert (= (/ 1.0 0.0) (/ 1.0 0.0)))
(check-sat)
(exit)
