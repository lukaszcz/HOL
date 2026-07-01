(set-logic QF_SLIA)
(assert (= (str.in_re "a" (str.to_re "a")) "type-error"))
(check-sat)
