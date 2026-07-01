(set-logic ALL)
(declare-const s (Set Int))
(assert (= (set.member 1 s) true))
(check-sat)
