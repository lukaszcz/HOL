; family: uf
; holsmt-expected: {"proof-parse": {"status": "fail", "diagnostic": "Z3 did not emit a raw proof"}, "proof-replay": {"status": "fail", "diagnostic": "Z3 did not emit a raw proof"}}
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const x U)
(declare-const y U)
(assert (= x y))
(assert (not (= (f x) (f y))))
(check-sat)
(exit)
