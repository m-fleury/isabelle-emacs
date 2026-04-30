;modified from strings
(set-logic QF_UF)
(declare-fun b () Int)
(declare-fun f (Int Int Int) Int)
(assert (not (= (= (ite (= 42 (f b 0 1)) true true) true) (ite (= 42 (f b 0 1)) (= true true) (= true true)))))
(check-sat)
(exit)
