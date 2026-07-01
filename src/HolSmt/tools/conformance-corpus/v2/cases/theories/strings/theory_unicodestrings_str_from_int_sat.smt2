(set-logic QF_SLIA)
(assert (= (str.from_int 123) (str.from_int 123)))
(check-sat)
