(set-logic QF_SLIA)
(assert (or (str.prefixof "a" "abc") (not (str.prefixof "a" "abc"))))
(check-sat)
