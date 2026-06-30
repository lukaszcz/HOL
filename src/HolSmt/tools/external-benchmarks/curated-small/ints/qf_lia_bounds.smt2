; family: ints
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 3))
(assert (< x 3))
(check-sat)
(exit)
