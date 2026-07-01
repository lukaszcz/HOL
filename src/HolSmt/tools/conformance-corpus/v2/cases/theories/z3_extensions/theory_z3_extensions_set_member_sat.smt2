(set-logic ALL)
(declare-const s (Set Int))
(assert (or (set.member 1 s) (not (set.member 1 s))))
(check-sat)
