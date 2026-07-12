(set-logic QF_UFDTNIA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
