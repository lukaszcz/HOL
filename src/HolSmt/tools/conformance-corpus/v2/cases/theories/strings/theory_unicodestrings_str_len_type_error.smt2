(set-logic QF_SLIA)
(assert (= (str.len "abc") "type-error"))
(check-sat)
