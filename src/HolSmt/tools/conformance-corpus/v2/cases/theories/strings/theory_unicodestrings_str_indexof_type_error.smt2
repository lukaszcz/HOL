(set-logic QF_SLIA)
(assert (= (str.indexof "abc" "b" 0) "type-error"))
(check-sat)
