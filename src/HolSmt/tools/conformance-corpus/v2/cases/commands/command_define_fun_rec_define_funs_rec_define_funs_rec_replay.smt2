(set-logic QF_UF)
(define-funs-rec ((even ((p Bool)) Bool) (odd ((p Bool)) Bool)) ((odd p) (not (even p))))
(assert (even true))
(check-sat)
