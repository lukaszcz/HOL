(set-logic QF_BV)
(assert (= ((_ zero_extend 2) #b10) ((_ zero_extend 2) #b10)))
(check-sat)
