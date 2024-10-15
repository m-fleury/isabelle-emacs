(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |
Generated by: Aman Goel (amangoel@umich.edu), Karem A. Sakallah (karem@umich.edu)
Generated on: 2018-04-06

Generated by the tool Averroes 2 (successor of [1]) which implements safety property
verification on hardware systems.

This SMT problem belongs to a set of SMT problems generated by applying Averroes 2
to benchmarks derived from [2-5].

A total of 412 systems (345 from [2], 19 from [3], 26 from [4], 22 from [5]) were
syntactically converted from their original formats (using [6, 7]), and given to
Averroes 2 to perform property checking with abstraction (wide bit-vectors -> terms,
wide operators -> UF) using SMT solvers [8, 9].

[1] Lee S., Sakallah K.A. (2014) Unbounded Scalable Verification Based on Approximate
Property-Directed Reachability and Datapath Abstraction. In: Biere A., Bloem R. (eds)
Computer Aided Verification. CAV 2014. Lecture Notes in Computer Science, vol 8559.
Springer, Cham
[2] http://fmv.jku.at/aiger/index.html#beem
[3] http://www.cs.cmu.edu/~modelcheck/vcegar
[4] http://www.cprover.org/hardware/v2c
[5] http://github.com/aman-goel/verilogbench
[6] http://www.clifford.at/yosys
[7] http://github.com/chengyinwu/V3
[8] http://github.com/Z3Prover/z3
[9] http://github.com/SRI-CSL/yices2

id: loyd.1.prop1
query-maker: "Yices 2"
query-time: 0.001000 ms
query-class: abstract
query-category: oneshot
query-type: regular
status: unsat
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unsat)
(declare-sort utt$8 0)
(declare-sort utt$32 0)
(declare-fun y$1 () Bool)
(declare-fun y$10 () Bool)
(declare-fun y$12 () Bool)
(declare-fun y$14 () Bool)
(declare-fun y$16 () Bool)
(declare-fun y$18 () Bool)
(declare-fun y$20 () Bool)
(declare-fun y$22 () Bool)
(declare-fun y$24 () Bool)
(declare-fun y$3 () Bool)
(declare-fun y$5 () Bool)
(declare-fun y$629 () Bool)
(declare-fun y$630 () Bool)
(declare-fun y$642 () Bool)
(declare-fun y$649 () Bool)
(declare-fun y$7 () Bool)
(declare-fun y$a_done () Bool)
(declare-fun y$a_not_done () Bool)
(declare-fun y$a_q () Bool)
(declare-fun y$dve_invalid () Bool)
(declare-fun y$id14 () Bool)
(declare-fun y$id14_op () Bool)
(declare-fun y$n0s32 () utt$32)
(declare-fun y$n0s8 () utt$8)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$n1s8 () utt$8)
(declare-fun y$n2s32 () utt$32)
(declare-fun y$n2s8 () utt$8)
(declare-fun y$n3s32 () utt$32)
(declare-fun y$n3s8 () utt$8)
(declare-fun y$n4s32 () utt$32)
(declare-fun y$n4s8 () utt$8)
(declare-fun y$n5s32 () utt$32)
(declare-fun y$n5s8 () utt$8)
(declare-fun y$prop () Bool)
(declare-fun y$v_a_0 () utt$8)
(declare-fun y$v_a_1 () utt$8)
(declare-fun y$v_a_2 () utt$8)
(declare-fun y$v_a_3 () utt$8)
(declare-fun y$v_a_4 () utt$8)
(declare-fun y$v_a_5 () utt$8)
(declare-fun y$v_x () utt$8)
(declare-fun y$v_y () utt$8)
(assert (distinct y$n0s8 y$n1s8 y$n2s8 y$n3s8 y$n4s8 y$n5s8))
(assert (distinct y$n0s32 y$n2s32 y$n1s32 y$n3s32 y$n4s32 y$n5s32))
(assert (= y$a_done (not y$1)))
(assert (= y$a_not_done (not y$3)))
(assert (= y$a_q (not y$5)))
(assert (= y$dve_invalid (not y$7)))
(assert (= y$10 (= y$n0s8 y$v_a_0)))
(assert (= y$12 (= y$n0s8 y$v_a_1)))
(assert (= y$14 (= y$n0s8 y$v_a_2)))
(assert (= y$16 (= y$n0s8 y$v_a_3)))
(assert (= y$18 (= y$n0s8 y$v_a_4)))
(assert (= y$20 (= y$n0s8 y$v_a_5)))
(assert (= y$22 (= y$n0s8 y$v_x)))
(assert (= y$24 (= y$n0s8 y$v_y)))
(assert (= y$prop (not y$642)))
(assert (= y$id14_op (and y$a_done y$7)))
(assert (= y$id14_op (not y$629)))
(assert (= y$630 (= y$prop y$629)))
(assert (= y$649 (and y$1 y$3 y$5 y$7 y$10 y$12 y$14 y$16 y$18 y$20 y$22 y$24 y$642 y$630)))
(assert y$649)
(check-sat)
(exit)
