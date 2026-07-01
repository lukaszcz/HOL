(set-logic QF_UF)
(define-fun-rec f ((p Bool)) Bool (f p))
(check-sat)
