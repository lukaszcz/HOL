(set-logic QF_SLIA)
(assert (= ((_ re.loop 1 3) (str.to_re "a")) ((_ re.loop 1 3) (str.to_re "a"))))
(check-sat)
