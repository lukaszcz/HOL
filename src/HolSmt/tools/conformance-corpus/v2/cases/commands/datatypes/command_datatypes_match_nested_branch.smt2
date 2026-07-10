(set-logic ALL)
(declare-datatype Tree ((leaf (value Int)) (node (left Tree) (right Tree))))
(declare-const t Tree)
(assert (= (match t
  (((leaf x) x)
   ((node l r) (match l (((leaf y) y) ((node u v) 0)))))) 0))
(check-sat)
