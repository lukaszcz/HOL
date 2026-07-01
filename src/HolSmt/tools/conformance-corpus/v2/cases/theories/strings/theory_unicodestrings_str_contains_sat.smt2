(set-logic QF_SLIA)
(assert (or (str.contains "abc" "b") (not (str.contains "abc" "b"))))
(check-sat)
