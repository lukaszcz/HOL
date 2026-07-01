(set-logic QF_UFFP)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
