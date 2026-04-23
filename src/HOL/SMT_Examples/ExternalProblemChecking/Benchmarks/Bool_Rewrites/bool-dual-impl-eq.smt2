;manually changed all strings to ints. + to +, 0 -> 0, 1 -> 1, should not make a difference.
(set-logic AUFLIA)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun z () Int)
(declare-fun t () Int)
(assert (not (= (and (=> (= (+ (+ x1 0 x2) z) (+ (+ x2 1 x1) t)) (and (= (+ x1 0 x2) (+ x2 1 x1)) (= z t))) (=> (and (= (+ x1 0 x2) (+ x2 1 x1)) (= z t)) (= (+ (+ x1 0 x2) z) (+ (+ x2 1 x1) t)))) (= (= (+ (+ x1 0 x2) z) (+ (+ x2 1 x1) t)) (and (= (+ x1 0 x2) (+ x2 1 x1)) (= z t))))))
(check-sat)
(exit)
