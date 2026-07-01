(set-logic QF_SLIA)
(assert (= (re.++ (str.to_re "a") (str.to_re "b")) "type-error"))
(check-sat)
