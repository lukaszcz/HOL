(set-logic QF_SLIA)
(assert (= (re.inter (str.to_re "a") re.all) "type-error"))
(check-sat)
