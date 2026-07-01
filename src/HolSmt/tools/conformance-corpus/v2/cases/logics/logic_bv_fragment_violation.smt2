(set-logic BV)
(declare-const outside_fragment Int)
(assert (= outside_fragment 0))
(check-sat)
