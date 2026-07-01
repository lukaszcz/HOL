(set-logic QF_BV)
(assert (= ((_ sign_extend 2) #b10) ((_ sign_extend 2) #b10)))
(check-sat)
