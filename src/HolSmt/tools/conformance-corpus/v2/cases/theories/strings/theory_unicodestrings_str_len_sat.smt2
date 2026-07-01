(set-logic QF_SLIA)
(assert (= (str.len "abc") (str.len "abc")))
(check-sat)
