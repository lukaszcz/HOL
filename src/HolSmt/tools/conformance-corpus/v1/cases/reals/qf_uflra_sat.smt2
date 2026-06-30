(set-logic QF_UFLRA)

(declare-const x Real)
(declare-const y Real)
(assert (<= (+ x 1.0) (+ y 2.0)))
(assert (= (- (+ x y) y) x))
(check-sat)
(exit)
