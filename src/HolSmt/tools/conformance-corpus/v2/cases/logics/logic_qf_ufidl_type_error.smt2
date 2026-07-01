(set-logic QF_UFIDL)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
