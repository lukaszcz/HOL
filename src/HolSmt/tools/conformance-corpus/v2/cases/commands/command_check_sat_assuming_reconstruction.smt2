(set-logic QF_UF)
(declare-const p Bool)
(assert (! p :named p_name))
(check-sat-assuming ((not p)))
