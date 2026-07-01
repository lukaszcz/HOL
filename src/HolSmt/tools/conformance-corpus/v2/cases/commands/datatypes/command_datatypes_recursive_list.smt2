(set-logic ALL)
(declare-datatype List ((nil) (cons (head Int) (tail List))))
(check-sat)
