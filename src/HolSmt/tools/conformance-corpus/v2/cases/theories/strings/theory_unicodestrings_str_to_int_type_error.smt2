(set-logic QF_SLIA)
(assert (= (str.to_int "123") "type-error"))
(check-sat)
