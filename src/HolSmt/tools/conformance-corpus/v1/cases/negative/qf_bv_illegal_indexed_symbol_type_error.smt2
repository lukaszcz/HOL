(set-logic QF_BV)
(assert (= ((_ extract -1 0) #b1) #b1))
(check-sat)
(exit)
