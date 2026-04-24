;handcrafted using basis from bool-not-eq-elim1
(set-logic ALL)
(declare-fun x9 () Bool)
(declare-fun x () Int)
(declare-fun x1 () Int)
(assert (not (= (exists ((a Int) (s Int)) (forall ((o Bool)) (not (ite x9 (forall ((k Int)) true) (= o (= 0 (ite x9 x x1))))))) (exists ((a Int) (s Int)) false))))
(check-sat)
(exit)
