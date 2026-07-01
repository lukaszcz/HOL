(set-logic AUFLIA)
(declare-const a (Array Int Bool))
(assert (forall ((i Bool)) (= (select a i) true)))
(check-sat)
