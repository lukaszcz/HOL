; family: bitvectors
; holsmt-expected: {"proof-parse": {"status": "fail", "diagnostic": "Z3 did not emit a raw proof"}, "proof-replay": {"status": "fail", "diagnostic": "Z3 did not emit a raw proof"}}
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (not (= (bvxor x x) #x00)))
(check-sat)
(exit)
