(set-logic UFIDL)

(declare-const x Int)
(declare-const y Int)
(assert (<= (- x y) 1))
(check-sat)
(exit)
