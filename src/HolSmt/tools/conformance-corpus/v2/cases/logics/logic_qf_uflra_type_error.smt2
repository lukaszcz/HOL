(set-logic QF_UFLRA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
