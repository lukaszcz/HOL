; family: bitvectors
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (not (= (bvxor x x) #x00)))
(check-sat)
(exit)
