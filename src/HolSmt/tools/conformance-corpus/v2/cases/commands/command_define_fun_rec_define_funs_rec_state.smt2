(set-logic QF_UF)
(define-funs-rec ((f ((p Bool)) Bool)) ((not p)))
(assert (f false))
(check-sat)
