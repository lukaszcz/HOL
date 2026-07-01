(set-logic QF_UF)
(declare-datatype Color ((red) (blue)))
(assert (= red blue))
(check-sat)
