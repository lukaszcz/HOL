(set-logic QF_SLIA)
(assert (= (str.replace_re_all "aba" (str.to_re "a") "x") (str.replace_re_all "aba" (str.to_re "a") "x")))
(check-sat)
