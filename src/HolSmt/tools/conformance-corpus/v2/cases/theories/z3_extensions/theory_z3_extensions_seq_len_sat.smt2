(set-logic ALL)
(declare-const xs (Seq Int))
(assert (= (seq.len xs) (seq.len xs)))
(check-sat)
