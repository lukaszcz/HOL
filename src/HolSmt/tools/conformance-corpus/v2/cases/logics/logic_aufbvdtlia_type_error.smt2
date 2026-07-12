(set-logic AUFBVDTLIA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
