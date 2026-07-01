(set-logic ALIRA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
