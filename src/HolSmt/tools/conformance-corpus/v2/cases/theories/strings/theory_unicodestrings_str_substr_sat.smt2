(set-logic QF_SLIA)
(assert (= (str.substr "abc" 0 2) (str.substr "abc" 0 2)))
(check-sat)
