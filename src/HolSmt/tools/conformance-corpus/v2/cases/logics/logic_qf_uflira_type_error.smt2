(set-logic QF_UFLIRA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
