(set-logic QF_SNIA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
