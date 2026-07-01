(set-logic QF_SLIA)
(assert (= ((_ re.loop 1 3) (str.to_re "a")) "type-error"))
(check-sat)
