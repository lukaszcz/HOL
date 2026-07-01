(set-logic QF_AUFLIA)
(declare-fun make () (Array Int Bool))
(assert (= make make))
(check-sat)
