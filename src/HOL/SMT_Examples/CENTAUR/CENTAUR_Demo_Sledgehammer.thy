theory CENTAUR_Demo_Sledgehammer
  imports Main
begin
declare [[smt_cvc_alethe = false]]
declare [[smt_trace = false]]


lemma rewrite_arith_poly_norm_rel_leq_left_to_real:
  fixes x1::"int" and x2::"int" and y1::"real" and y2 and cx and cy
  shows "((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (of_int (x1 - x2)::real)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 \<le> x2) = (y1 \<le> y2))) = True"
  sledgehammer




























end