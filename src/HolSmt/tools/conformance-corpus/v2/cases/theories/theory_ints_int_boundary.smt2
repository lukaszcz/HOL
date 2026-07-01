(set-logic QF_LIA)
(declare-const huge Int)
(assert (= huge 123456789012345678901234567890))
(check-sat)
