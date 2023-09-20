(set-option :produce-proofs true)
(set-logic AUFLIA)
(declare-sort A$ 0)
(declare-fun p$ (A$) Bool)
(declare-fun y$ () A$)
(assert (! (not (=> (and (forall ((?v0 A$)) (p$ ?v0)) (not (p$ y$))) false)) :named a0))
(check-sat)
(get-proof)