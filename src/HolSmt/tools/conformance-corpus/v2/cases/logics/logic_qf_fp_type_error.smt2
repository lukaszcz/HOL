(set-logic QF_FP)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
