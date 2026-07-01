(set-logic QF_BV)
(declare-const bad (_ BitVec 0))
(assert (= bad bad))
(check-sat)
