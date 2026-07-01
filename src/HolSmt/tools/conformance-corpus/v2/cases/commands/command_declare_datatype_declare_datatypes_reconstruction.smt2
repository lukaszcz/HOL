(set-logic QF_UF)
(declare-datatype Color ((red) (blue)))
(assert (not (= red blue)))
(check-sat)
