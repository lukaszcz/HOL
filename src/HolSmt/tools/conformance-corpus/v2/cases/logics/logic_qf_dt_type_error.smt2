(set-logic QF_DT)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
