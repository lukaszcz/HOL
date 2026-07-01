(set-logic QF_SLIA)
(assert (= (str.is_digit "7") "type-error"))
(check-sat)
