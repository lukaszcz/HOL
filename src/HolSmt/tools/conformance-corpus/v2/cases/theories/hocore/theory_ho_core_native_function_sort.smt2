(set-logic ALL)
(declare-const f (-> Int Bool))
(assert (= f f))
(check-sat)
