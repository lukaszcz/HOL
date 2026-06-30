(set-logic QF_LIRA)

(declare-const i Int)
(assert (is_int (to_real i)))
(assert (= (to_int (to_real 4)) 4))
(check-sat)
(exit)
