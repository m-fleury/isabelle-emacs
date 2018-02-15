(*  Title:      HOL/HOLCF/IOA/NTP/Sender.thy
    Author:     Tobias Nipkow & Konrad Slind
*)

section \<open>The implementation: sender\<close>

theory Sender
imports IOA.IOA Action
begin

type_synonym
'm sender_state = "'m list * bool multiset * bool multiset * bool * bool"
(*                messages   #sent           #received      header  mode *)

definition sq :: "'m sender_state => 'm list" where "sq = fst"
definition ssent :: "'m sender_state => bool multiset" where "ssent = fst \<circ> snd"
definition srcvd :: "'m sender_state => bool multiset" where "srcvd = fst \<circ> snd \<circ> snd"
definition sbit :: "'m sender_state => bool" where "sbit = fst \<circ> snd \<circ> snd \<circ> snd"
definition ssending :: "'m sender_state => bool" where "ssending = snd \<circ> snd \<circ> snd \<circ> snd"

definition
  sender_asig :: "'m action signature" where
  "sender_asig = ((UN m. {S_msg(m)}) Un (UN b. {R_ack(b)}),
                   UN pkt. {S_pkt(pkt)},
                   {C_m_s,C_r_s})"

definition
  sender_trans :: "('m action, 'm sender_state)transition set" where
  "sender_trans =
 {tr. let s = fst(tr);
          t = snd(snd(tr))
      in case fst(snd(tr))
      of
      S_msg(m) => sq(t)=sq(s)@[m]   \<and>
                  ssent(t)=ssent(s) \<and>
                  srcvd(t)=srcvd(s) \<and>
                  sbit(t)=sbit(s)   \<and>
                  ssending(t)=ssending(s) |
      R_msg(m) => False |
      S_pkt(pkt) => hdr(pkt) = sbit(s)      \<and>
                       (\<exists>Q. sq(s) = (msg(pkt)#Q))  \<and>
                       sq(t) = sq(s)           \<and>
                       ssent(t) = addm (ssent s) (sbit s) \<and>
                       srcvd(t) = srcvd(s) \<and>
                       sbit(t) = sbit(s)   \<and>
                       ssending(s)         \<and>
                       ssending(t) |
    R_pkt(pkt) => False |
    S_ack(b)   => False |
      R_ack(b) => sq(t)=sq(s)                  \<and>
                     ssent(t)=ssent(s)            \<and>
                     srcvd(t) = addm (srcvd s) b  \<and>
                     sbit(t)=sbit(s)              \<and>
                     ssending(t)=ssending(s) |
      C_m_s => count (ssent s) (~sbit s) < count (srcvd s) (~sbit s) \<and>
               sq(t)=sq(s)       \<and>
               ssent(t)=ssent(s) \<and>
               srcvd(t)=srcvd(s) \<and>
               sbit(t)=sbit(s)   \<and>
               ssending(s)       \<and>
               ~ssending(t) |
      C_m_r => False |
      C_r_s => count (ssent s) (sbit s) <= count (srcvd s) (~sbit s) \<and>
               sq(t)=tl(sq(s))      \<and>
               ssent(t)=ssent(s)    \<and>
               srcvd(t)=srcvd(s)    \<and>
               sbit(t) = (~sbit(s)) \<and>
               ~ssending(s)         \<and>
               ssending(t) |
      C_r_r(m) => False}"

definition
  sender_ioa :: "('m action, 'm sender_state)ioa" where
  "sender_ioa =
   (sender_asig, {([],{|},{|},False,True)}, sender_trans,{},{})"

lemma in_sender_asig:
  "S_msg(m) \<in> actions(sender_asig)"
  "R_msg(m) \<notin> actions(sender_asig)"
  "S_pkt(pkt) \<in> actions(sender_asig)"
  "R_pkt(pkt) \<notin> actions(sender_asig)"
  "S_ack(b) \<notin> actions(sender_asig)"
  "R_ack(b) \<in> actions(sender_asig)"
  "C_m_s \<in> actions(sender_asig)"
  "C_m_r \<notin> actions(sender_asig)"
  "C_r_s \<in> actions(sender_asig)"
  "C_r_r(m) \<notin> actions(sender_asig)"
  by (simp_all add: sender_asig_def actions_def asig_projections)

lemmas sender_projections = sq_def ssent_def srcvd_def sbit_def ssending_def

end
