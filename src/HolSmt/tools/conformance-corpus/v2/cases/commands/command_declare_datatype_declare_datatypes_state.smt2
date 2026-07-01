(set-logic QF_UF)
(declare-datatypes ((Color 0)) (((red) (blue))))
(declare-const c Color)
(check-sat)
