(set-logic ALL)
(declare-datatype D ((mk (self D))))
(check-sat)
