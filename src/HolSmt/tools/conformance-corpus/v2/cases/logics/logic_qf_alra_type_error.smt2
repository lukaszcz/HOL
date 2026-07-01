(set-logic QF_ALRA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
