(set-logic QF_UFNIRA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
