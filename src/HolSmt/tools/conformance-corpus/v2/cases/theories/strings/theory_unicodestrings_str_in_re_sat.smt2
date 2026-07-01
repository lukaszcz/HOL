(set-logic QF_SLIA)
(assert (or (str.in_re "a" (str.to_re "a")) (not (str.in_re "a" (str.to_re "a")))))
(check-sat)
