(set-logic QF_RDL)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
