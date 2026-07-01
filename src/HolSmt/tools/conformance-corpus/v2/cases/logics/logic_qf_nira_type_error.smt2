(set-logic QF_NIRA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
