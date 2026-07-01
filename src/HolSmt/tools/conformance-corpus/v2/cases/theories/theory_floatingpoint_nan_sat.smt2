(set-logic QF_FP)
(assert (= (_ NaN 8 24) (_ NaN 8 24)))
(check-sat)
