(set-option :produce-proofs true)
(set-logic AUFLIA)
(assert (not
  (forall ((x Int))
    (or false (= (+ x 1) (+ 1 x))))))
(check-sat)
(get-proof)
