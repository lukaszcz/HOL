(set-logic QF_SLIA)
(declare-const x (RegLan String))
(assert (= x x))
(check-sat)
