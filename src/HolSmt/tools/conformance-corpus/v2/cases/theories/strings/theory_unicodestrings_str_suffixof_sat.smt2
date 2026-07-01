(set-logic QF_SLIA)
(assert (or (str.suffixof "c" "abc") (not (str.suffixof "c" "abc"))))
(check-sat)
