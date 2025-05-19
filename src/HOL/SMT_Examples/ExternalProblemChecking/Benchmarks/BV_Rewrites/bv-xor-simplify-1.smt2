(set-logic ALL)
(assert (not (= (forall ((s (_ BitVec 4))) (not (= (bvxor (bvxor (_ bv0 4) s) s) (_ bv0 4)))) (forall ((s (_ BitVec 4))) false))))
(check-sat)
(exit)
