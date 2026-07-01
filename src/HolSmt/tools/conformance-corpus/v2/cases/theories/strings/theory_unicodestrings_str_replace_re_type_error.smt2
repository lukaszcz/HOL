(set-logic QF_SLIA)
(assert (str.replace_re "abc" (str.to_re "b") "x"))
(check-sat)
