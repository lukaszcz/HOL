(set-logic QF_UF)
(declare-const p Bool)
(assert (! p :named named_p))
(check-sat)
