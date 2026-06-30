(set-logic QF_LIA)

(declare-const x Int)
(assert (= (* x x) 4))
(check-sat)
(exit)
