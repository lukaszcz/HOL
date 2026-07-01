(set-logic ALL)
(declare-const s (Set Int))
(assert (= (set.insert 1 s) (set.insert 1 s)))
(check-sat)
