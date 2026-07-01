(set-logic QF_IDL)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
