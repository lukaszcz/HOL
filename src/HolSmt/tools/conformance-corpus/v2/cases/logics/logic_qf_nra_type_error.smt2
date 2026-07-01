(set-logic QF_NRA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
