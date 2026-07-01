(set-logic QF_SLIA)
(assert (= (str.to_re "a") (str.to_re "a")))
(check-sat)
