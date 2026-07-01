(set-logic QF_SLIA)
(assert (= ((_ re.^ 2) (str.to_re "a")) "type-error"))
(check-sat)
