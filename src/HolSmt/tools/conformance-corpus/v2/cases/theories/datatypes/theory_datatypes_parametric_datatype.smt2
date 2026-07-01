(set-logic ALL)
(declare-datatype Box (par (T) ((box (value T)))))
(check-sat)
