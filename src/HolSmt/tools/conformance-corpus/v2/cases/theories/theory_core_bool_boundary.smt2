(set-logic QF_UF)
(declare-fun f (Bool) Bool)
(assert (f true))
(check-sat)
