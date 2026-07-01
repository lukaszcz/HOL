(set-logic QF_SLIA)
(assert (= (str.indexof "abc" "b" 0) (str.indexof "abc" "b" 0)))
(check-sat)
