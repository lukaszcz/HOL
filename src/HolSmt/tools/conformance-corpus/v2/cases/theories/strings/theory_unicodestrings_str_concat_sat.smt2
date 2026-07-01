(set-logic QF_SLIA)
(assert (= (str.++ "a" "b") (str.++ "a" "b")))
(check-sat)
