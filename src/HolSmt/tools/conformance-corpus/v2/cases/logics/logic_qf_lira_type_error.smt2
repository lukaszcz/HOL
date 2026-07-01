(set-logic QF_LIRA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
