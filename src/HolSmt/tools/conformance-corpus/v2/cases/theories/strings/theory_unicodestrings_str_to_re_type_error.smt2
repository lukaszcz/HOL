(set-logic QF_SLIA)
(assert (= (str.to_re "a") "type-error"))
(check-sat)
