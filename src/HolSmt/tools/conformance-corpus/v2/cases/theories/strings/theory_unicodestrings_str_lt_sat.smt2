(set-logic QF_SLIA)
(assert (or (str.< "a" "b") (not (str.< "a" "b"))))
(check-sat)
