(set-logic QF_SLIA)
(assert (= (str.at "abc" 1) (str.at "abc" 1)))
(check-sat)
