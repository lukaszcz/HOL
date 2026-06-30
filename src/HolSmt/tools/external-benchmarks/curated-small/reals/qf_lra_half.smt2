; family: reals
(set-logic QF_LRA)
(declare-const x Real)
(assert (= x (/ 1.0 2.0)))
(assert (not (= (+ x x) 1.0)))
(check-sat)
(exit)
