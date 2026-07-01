(set-logic QF_LIA)
(declare-const p Bool)
(assert (= (ite p 1 2) 1))
(check-sat)
