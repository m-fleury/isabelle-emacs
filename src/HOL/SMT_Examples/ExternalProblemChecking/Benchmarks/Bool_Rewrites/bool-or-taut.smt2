;used to contain arrays
(set-logic ALL)
(declare-fun x () Bool)
(declare-fun select (Int Int) Bool)
(assert (not (= (or x (not x) (forall ((_x Int)) (not (select _x 0)))) true)))
(check-sat)
(exit)
