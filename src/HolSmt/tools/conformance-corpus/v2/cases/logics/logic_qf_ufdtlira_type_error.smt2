(set-logic QF_UFDTLIRA)
(declare-fun f (Bool) Bool)
(assert (f true false))
(check-sat)
