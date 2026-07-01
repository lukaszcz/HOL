(set-logic ALL)
(declare-datatype List ((nil) (cons (head Int) (tail List))))
(declare-const xs List)
(check-sat)
