(set-logic QF_AUFLIA)
(declare-const f (Array Int Bool))
(assert (= f f))
(check-sat)
