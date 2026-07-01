(set-logic QF_AX)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
