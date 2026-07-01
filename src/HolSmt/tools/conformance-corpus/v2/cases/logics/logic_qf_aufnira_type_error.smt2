(set-logic QF_AUFNIRA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
