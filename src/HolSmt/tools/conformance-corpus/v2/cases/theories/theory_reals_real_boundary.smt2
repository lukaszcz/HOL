(set-logic QF_LRA)
(declare-const x Real)
(assert (= x 12345678901234567890.0))
(check-sat)
