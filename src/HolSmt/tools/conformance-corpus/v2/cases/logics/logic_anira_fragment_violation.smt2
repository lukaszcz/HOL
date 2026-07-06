(set-logic ANIRA)
(declare-const outside_fragment (_ BitVec 1))
(assert (= outside_fragment #b0))
(check-sat)
