theory CENTAUR_Demo_Quant
  imports Main
begin
declare [[smt_cvc_alethe]]
declare [[smt_trace]]


















lemma "\<exists>x::int. x + 1 = x * 2"
  by (smt (cvc5))
  























end