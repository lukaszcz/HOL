(set-logic QF_SLIA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
