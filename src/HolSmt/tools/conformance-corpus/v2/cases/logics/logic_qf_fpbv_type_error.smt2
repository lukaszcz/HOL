(set-logic QF_FPBV)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
