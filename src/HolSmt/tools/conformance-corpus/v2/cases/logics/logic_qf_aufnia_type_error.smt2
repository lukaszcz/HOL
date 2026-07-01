(set-logic QF_AUFNIA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
