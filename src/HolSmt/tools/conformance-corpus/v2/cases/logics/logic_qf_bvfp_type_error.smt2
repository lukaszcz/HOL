(set-logic QF_BVFP)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
