(set-logic ANIRA)
(declare-fun outside_fragment (Int) Int)
(assert (= (outside_fragment 0) 0))
(check-sat)
