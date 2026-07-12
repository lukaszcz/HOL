; family: datatypes
; holsmt-expected: {"proof-parse": {"status": "fail", "diagnostic": "Z3 did not emit a raw proof"}, "proof-replay": {"status": "fail", "diagnostic": "Z3 did not emit a raw proof"}, "z3-tac": {"status": "pass"}}
(set-logic QF_DT)
(declare-datatype Color ((red) (blue)))
(assert (= red blue))
(check-sat)
(exit)
