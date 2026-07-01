(set-logic QF_SLIA)
(assert (or (str.is_digit "7") (not (str.is_digit "7"))))
(check-sat)
