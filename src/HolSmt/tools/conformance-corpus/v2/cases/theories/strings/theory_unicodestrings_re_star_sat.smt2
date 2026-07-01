(set-logic QF_SLIA)
(assert (= (re.* (str.to_re "a")) (re.* (str.to_re "a"))))
(check-sat)
