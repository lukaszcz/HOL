(set-logic QF_UFLIA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
