(set-logic QF_ANRA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
