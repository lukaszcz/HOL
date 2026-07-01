(set-logic QF_BV)
(assert (= ((_ repeat 2) #b10) ((_ repeat 2) #b10)))
(check-sat)
