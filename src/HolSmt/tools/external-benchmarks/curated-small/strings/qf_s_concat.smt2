; family: strings
(set-logic QF_S)
(declare-const s String)
(assert (= (str.++ s "") s))
(check-sat)
(exit)
