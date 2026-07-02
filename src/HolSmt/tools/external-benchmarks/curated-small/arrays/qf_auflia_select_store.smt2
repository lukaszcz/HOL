; family: arrays
; holsmt-expected: {"proof-parse": {"status": "fail", "diagnostic": "Z3 did not emit a raw proof"}, "proof-replay": {"status": "fail", "diagnostic": "Z3 did not emit a raw proof"}, "z3-tac": {"status": "fail", "diagnostic": "unsupported higher-order/function sort"}}
(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const v Int)
(assert (not (= (select (store a i v) i) v)))
(check-sat)
(exit)
