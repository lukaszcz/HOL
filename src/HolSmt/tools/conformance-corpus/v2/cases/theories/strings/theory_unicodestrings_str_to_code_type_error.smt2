(set-logic QF_SLIA)
(assert (= (str.to_code "A") "type-error"))
(check-sat)
