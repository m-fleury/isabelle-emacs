;originally had bit-vectors
(set-logic AUFLIA)
(declare-fun a () Bool)
(declare-fun f (Bool) Bool)
(assert (not (= (= (f a) true) (f a))))
(check-sat)
(exit)
