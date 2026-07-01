(set-logic QF_SLIA)
(assert (= (str.suffixof "c" "abc") "type-error"))
(check-sat)
