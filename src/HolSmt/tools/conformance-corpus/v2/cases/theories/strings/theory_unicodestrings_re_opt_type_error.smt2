(set-logic QF_SLIA)
(assert (= (re.opt (str.to_re "a")) "type-error"))
(check-sat)
