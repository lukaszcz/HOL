(set-logic QF_SLIA)
(assert (= (str.to_code "A") (str.to_code "A")))
(check-sat)
