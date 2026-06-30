(set-logic QF_BV)
(assert (and
  (= (ubv_to_int #x0f) 15)
  (= (sbv_to_int #xff) (- 1))
  (= ((_ int_to_bv 8) 257) #x01)
))
(exit)
