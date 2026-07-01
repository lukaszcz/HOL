(set-logic ALL)
(declare-const b (Bag Int))
(assert (= (bag.count 1 b) (bag.count 1 b)))
(check-sat)
