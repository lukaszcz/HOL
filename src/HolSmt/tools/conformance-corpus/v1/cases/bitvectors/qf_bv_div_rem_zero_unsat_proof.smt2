(set-logic QF_BV)
(assert (not (and
  (= (bvudiv #x2a #x00) #xff)
  (= (bvurem #x2a #x00) #x2a)
)))
(check-sat)
(get-proof)
(exit)
