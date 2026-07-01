(set-logic ALL)
(declare-const x (Bag Int))
(assert (= x x))
(check-sat)
