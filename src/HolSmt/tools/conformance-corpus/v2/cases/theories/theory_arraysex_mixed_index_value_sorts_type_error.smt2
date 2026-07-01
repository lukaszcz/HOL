(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 8) Bool))
(assert (= (select a true) true))
(check-sat)
