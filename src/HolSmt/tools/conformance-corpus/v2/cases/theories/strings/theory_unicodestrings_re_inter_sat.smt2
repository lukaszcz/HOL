(set-logic QF_SLIA)
(assert (= (re.inter (str.to_re "a") re.all) (re.inter (str.to_re "a") re.all)))
(check-sat)
