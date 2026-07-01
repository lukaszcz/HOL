(set-logic QF_SLIA)
(assert (= (str.replace "abc" "b" "x") (str.replace "abc" "b" "x")))
(check-sat)
