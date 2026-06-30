(set-logic UF)

(declare-sort U 0)
(declare-const |and| U)
(declare-fun |p q| (U) Bool)
(assert (forall ((|and| U)) (=> (|p q| |and|) (|p q| |and|))))
(assert (exists ((x U)) (let ((x x)) (= x x))))
(check-sat)
(exit)
