(set-logic BV)
(assert (not (= (=> (forall ((?y6 (_ BitVec 32))) (not (= (_ bv0 32) (bvadd (bvmul ?y6 (_ bv4294967231 32)) (bvneg (bvmul ?y6 (_ bv4294967231 32))))))) false) (not (forall ((?y6 (_ BitVec 32))) (not (= (_ bv0 32) (bvadd (bvmul ?y6 (_ bv4294967231 32)) (bvneg (bvmul ?y6 (_ bv4294967231 32)))))))))))
(check-sat)
(exit)
