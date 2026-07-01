(set-logic QF_UF)
(define-fun both ((p Bool) (q Bool)) Bool (and p q))
(assert (both true true))
(check-sat)
