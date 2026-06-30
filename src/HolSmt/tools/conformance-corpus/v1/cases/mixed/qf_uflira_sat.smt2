(set-logic QF_UFLIRA)

(declare-const i Int)
(declare-const r Real)
(assert (<= (to_real i) (+ r 2.0)))
(assert (is_int (to_real i)))
(check-sat)
(exit)
