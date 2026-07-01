(set-logic QF_UFBV)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
