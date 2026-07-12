(set-logic QF_DT)
(declare-datatypes ((Color 0)) (((red) (blue))))
(declare-const c Color)
(check-sat)
