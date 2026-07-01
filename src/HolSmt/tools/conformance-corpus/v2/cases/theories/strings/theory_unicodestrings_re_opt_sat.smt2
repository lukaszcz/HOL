(set-logic QF_SLIA)
(assert (= (re.opt (str.to_re "a")) (re.opt (str.to_re "a"))))
(check-sat)
