(set-logic QF_SLIA)
(assert (= (re.diff re.all (str.to_re "a")) "type-error"))
(check-sat)
