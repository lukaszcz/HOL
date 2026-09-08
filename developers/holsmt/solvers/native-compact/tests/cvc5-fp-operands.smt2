(set-logic FP)
(set-option :produce-proofs true)
(assert
  (not
    (forall ((x (_ FloatingPoint 2 2)) (y (_ FloatingPoint 2 2)))
      (=>
        (and
          (not (fp.isNaN x))
          (and
            (not (fp.isInfinite x))
            (and
              (not (fp.isNaN y))
              (and
                (not (fp.isInfinite y))
                (and (fp.leq x y)
                     (fp.leq y
                       (fp.add roundNearestTiesToEven x x)))))))
        (fp.eq
          (fp.sub roundNearestTiesToEven y x)
          (fp.sub roundTowardZero y x))))))
(check-sat)
(get-proof)
