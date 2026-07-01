(set-logic QF_SLIA)
(assert (= (re.range "a" "z") (re.range "a" "z")))
(check-sat)
