; family: ints
; holsmt-expected: {"proof-parse": {"status": "fail", "diagnostic": "Z3 did not emit a raw proof"}, "proof-replay": {"status": "fail", "diagnostic": "Z3 did not emit a raw proof"}}
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 3))
(assert (< x 3))
(check-sat)
(exit)
