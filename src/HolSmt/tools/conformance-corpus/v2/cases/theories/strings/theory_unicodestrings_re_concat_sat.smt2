(set-logic QF_SLIA)
(assert (= (re.++ (str.to_re "a") (str.to_re "b")) (re.++ (str.to_re "a") (str.to_re "b"))))
(check-sat)
