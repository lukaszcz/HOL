(set-logic QF_SLIA)
(assert (= ((_ re.^ 2) (str.to_re "a")) ((_ re.^ 2) (str.to_re "a"))))
(check-sat)
