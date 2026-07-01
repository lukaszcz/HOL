(set-logic QF_AUFBV)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
