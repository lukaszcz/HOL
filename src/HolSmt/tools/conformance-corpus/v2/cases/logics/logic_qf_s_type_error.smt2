(set-logic QF_S)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
