; smt.random_seed=1 smt.refine_inj_axioms=false -smt2
(set-option :produce-proofs true)
(set-logic AUFLIRA)
(assert (! (not (exists ((?v0 Int)) (< 0 ?v0))) :named a0))
(check-sat)
(get-proof)