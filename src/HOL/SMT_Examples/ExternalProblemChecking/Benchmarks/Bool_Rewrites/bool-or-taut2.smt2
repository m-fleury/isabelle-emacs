(set-logic ALL)
(assert (not (= (forall ((c Int)) (or (not (>= c (- 1))) (>= c (- 1)))) (forall ((c Int)) true))))
(check-sat)
(exit)
