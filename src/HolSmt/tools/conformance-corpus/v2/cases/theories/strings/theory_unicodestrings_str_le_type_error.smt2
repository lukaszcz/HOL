(set-logic QF_SLIA)
(assert (= (str.<= "a" "b") "type-error"))
(check-sat)
