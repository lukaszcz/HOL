(set-logic QF_DT)
(declare-datatype Color ((red) (blue)))
(assert (= red blue))
(check-sat)
