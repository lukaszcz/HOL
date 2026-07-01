(set-logic QF_ANIA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
