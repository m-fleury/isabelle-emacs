;handcrafted since I could not find a real example
(set-logic AUFLIA)
(declare-fun t () Int)
(declare-fun f (Int) Bool)
(assert (= (f t) true)) 
(check-sat)
(exit)
