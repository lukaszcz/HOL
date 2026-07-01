(set-logic QF_ALIA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
