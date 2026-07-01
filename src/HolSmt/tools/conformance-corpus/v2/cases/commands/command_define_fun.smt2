(set-logic QF_UF)
(define-fun id ((p Bool)) Bool p)
(assert (id true))
(check-sat)
