(set-logic QF_SLIA)
(assert (= (str.to_int "123") (str.to_int "123")))
(check-sat)
