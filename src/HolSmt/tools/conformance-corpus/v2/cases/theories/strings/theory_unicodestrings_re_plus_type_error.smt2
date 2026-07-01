(set-logic QF_SLIA)
(assert (= (re.+ (str.to_re "a")) "type-error"))
(check-sat)
