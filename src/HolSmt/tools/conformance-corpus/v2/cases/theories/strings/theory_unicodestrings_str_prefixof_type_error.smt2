(set-logic QF_SLIA)
(assert (= (str.prefixof "a" "abc") "type-error"))
(check-sat)
