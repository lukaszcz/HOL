(set-logic QF_NIA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
