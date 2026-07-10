(set-logic ALL)
(declare-datatype Maybe ((none) (some (value Int))))
(assert (= (value none) 0))
(check-sat)
