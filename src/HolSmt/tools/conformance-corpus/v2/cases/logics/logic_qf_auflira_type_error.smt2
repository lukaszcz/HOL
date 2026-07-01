(set-logic QF_AUFLIRA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
