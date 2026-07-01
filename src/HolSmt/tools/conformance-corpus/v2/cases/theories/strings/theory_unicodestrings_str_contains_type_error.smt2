(set-logic QF_SLIA)
(assert (= (str.contains "abc" "b") "type-error"))
(check-sat)
