(set-logic ALL)
(declare-const x (Set Int))
(assert (= x x))
(check-sat)
