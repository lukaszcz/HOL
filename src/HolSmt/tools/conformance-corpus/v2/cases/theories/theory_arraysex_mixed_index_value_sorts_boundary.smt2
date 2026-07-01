(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 1) (_ BitVec 16)))
(assert (= (select (store a #b0 #x0001) #b0) #x0001))
(check-sat)
