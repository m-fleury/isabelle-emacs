;handcrafted based on taut2
(set-logic ALL)
(assert (not (= (forall ((c Int)) (or (>= c -1) (not (>= c (- 1))))) (forall ((c Int)) true))))
(check-sat)
(exit)
