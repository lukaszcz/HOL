(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(assert (= a a))
(check-sat)
