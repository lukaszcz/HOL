(set-logic QF_SLIA)
(declare-const x String)
(assert (= x x))
(check-sat)
