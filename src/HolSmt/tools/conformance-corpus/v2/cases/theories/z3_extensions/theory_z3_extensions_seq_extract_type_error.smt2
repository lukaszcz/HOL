(set-logic ALL)
(declare-const xs (Seq Int))
(assert (seq.extract xs 0 1))
(check-sat)
