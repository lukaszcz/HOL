(set-logic QF_SLIA)
(assert (= (re.range "a" "z") "type-error"))
(check-sat)
