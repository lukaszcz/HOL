(set-logic QF_NIA)

(assert (= (div 7 3) 2))
(assert (= (mod 7 3) 1))
(assert (= (div 7 0) (div 7 0)))
(check-sat)
(exit)
