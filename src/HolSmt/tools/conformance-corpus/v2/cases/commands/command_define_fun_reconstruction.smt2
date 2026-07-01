(set-logic QF_UF)
(define-fun bad () Bool false)
(assert bad)
(check-sat)
