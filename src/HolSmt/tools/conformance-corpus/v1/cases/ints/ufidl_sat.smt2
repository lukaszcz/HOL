(set-logic UFIDL)

(declare-const x Int)
(declare-const y Int)
(assert (<= (+ x 1) (+ y 2)))
(assert (= (- (+ x y) y) x))
(check-sat)
(exit)
