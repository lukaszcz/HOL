(set-logic QF_UFDTLIA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
