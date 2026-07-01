(set-logic QF_LRA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
