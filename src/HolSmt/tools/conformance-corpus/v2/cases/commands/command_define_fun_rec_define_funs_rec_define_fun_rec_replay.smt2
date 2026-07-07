(set-logic QF_UF)
(define-fun-rec f ((p Bool)) Bool p)
(assert (not (f true)))
(check-sat)
