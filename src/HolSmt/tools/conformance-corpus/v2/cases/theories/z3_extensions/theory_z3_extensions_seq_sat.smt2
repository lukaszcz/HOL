(set-logic ALL)
(declare-const x (Seq Int))
(assert (= x x))
(check-sat)
