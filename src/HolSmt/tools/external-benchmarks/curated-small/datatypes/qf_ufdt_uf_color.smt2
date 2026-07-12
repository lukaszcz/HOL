; family: datatypes
; holsmt-expected: {"proof-parse": {"status": "fail", "diagnostic": "Z3 did not emit a raw proof"}, "proof-replay": {"status": "fail", "diagnostic": "Z3 did not emit a raw proof"}, "z3-tac": {"status": "pass"}}
(set-logic QF_UFDT)
(declare-sort U 0)
(declare-datatype Color ((red) (blue)))
(declare-fun paint (U) Color)
(declare-const u U)
(assert (= (paint u) red))
(assert (= (paint u) blue))
(check-sat)
(exit)
