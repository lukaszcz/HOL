(set-option :produce-proofs true)
(set-logic AUFLIA)
(declare-fun |&a| (Int) Int)
(assert (not
  (forall ((x Int))
    (forall ((y Int))
      (or false (= (+ (|&a| x) y) (+ y (|&a| x))))))))
(check-sat)
(get-proof)
