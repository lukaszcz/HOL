; family: reals
; holsmt-expected: {"proof-parse": {"status": "fail", "diagnostic": "Z3 did not emit a raw proof"}, "proof-replay": {"status": "fail", "diagnostic": "Z3 did not emit a raw proof"}, "z3-tac": {"status": "fail", "diagnostic": "Z3 proof replay failed"}}
(set-logic QF_LRA)
(declare-const x Real)
(assert (= x (/ 1.0 2.0)))
(assert (not (= (+ x x) 1.0)))
(check-sat)
(exit)
