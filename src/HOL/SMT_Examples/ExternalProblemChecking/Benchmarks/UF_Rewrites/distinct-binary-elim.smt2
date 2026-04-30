;Originally on BV
(set-logic AUFLIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (not (= (distinct 0 y) (not (= 0 y)))))
(check-sat)
(exit)
