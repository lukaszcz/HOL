(set-logic QF_SLIA)
(assert (= (str.replace_all "aba" "a" "x") (str.replace_all "aba" "a" "x")))
(check-sat)
