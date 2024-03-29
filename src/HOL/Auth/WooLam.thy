(*  Title:      HOL/Auth/WooLam.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

section\<open>The Woo-Lam Protocol\<close>

theory WooLam imports Public begin

text\<open>Simplified version from page 11 of
  Abadi and Needham (1996). 
  Prudent Engineering Practice for Cryptographic Protocols.
  IEEE Trans. S.E. 22(1), pages 6-15.

Note: this differs from the Woo-Lam protocol discussed by Lowe (1996):
  Some New Attacks upon Security Protocols.
  Computer Security Foundations Workshop
\<close>

inductive_set woolam :: "event list set"
  where
         (*Initial trace is empty*)
   Nil:  "[] \<in> woolam"

         (** These rules allow agents to send messages to themselves **)

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
 | Fake: "\<lbrakk>evsf \<in> woolam;  X \<in> synth (analz (spies evsf))\<rbrakk>
          \<Longrightarrow> Says Spy B X  # evsf \<in> woolam"

         (*Alice initiates a protocol run*)
 | WL1:  "evs1 \<in> woolam \<Longrightarrow> Says A B (Agent A) # evs1 \<in> woolam"

         (*Bob responds to Alice's message with a challenge.*)
 | WL2:  "\<lbrakk>evs2 \<in> woolam;  Says A' B (Agent A) \<in> set evs2\<rbrakk>
          \<Longrightarrow> Says B A (Nonce NB) # evs2 \<in> woolam"

         (*Alice responds to Bob's challenge by encrypting NB with her key.
           B is *not* properly determined -- Alice essentially broadcasts
           her reply.*)
 | WL3:  "\<lbrakk>evs3 \<in> woolam;
             Says A  B (Agent A)  \<in> set evs3;
             Says B' A (Nonce NB) \<in> set evs3\<rbrakk>
          \<Longrightarrow> Says A B (Crypt (shrK A) (Nonce NB)) # evs3 \<in> woolam"

         (*Bob forwards Alice's response to the Server.  NOTE: usually
           the messages are shown in chronological order, for clarity.
           But here, exchanging the two events would cause the lemma
           WL4_analz_spies to pick up the wrong assumption!*)
 | WL4:  "\<lbrakk>evs4 \<in> woolam;
             Says A'  B X         \<in> set evs4;
             Says A'' B (Agent A) \<in> set evs4\<rbrakk>
          \<Longrightarrow> Says B Server \<lbrace>Agent A, Agent B, X\<rbrace> # evs4 \<in> woolam"

         (*Server decrypts Alice's response for Bob.*)
 | WL5:  "\<lbrakk>evs5 \<in> woolam;
             Says B' Server \<lbrace>Agent A, Agent B, Crypt (shrK A) (Nonce NB)\<rbrace>
               \<in> set evs5\<rbrakk>
          \<Longrightarrow> Says Server B (Crypt (shrK B) \<lbrace>Agent A, Nonce NB\<rbrace>)
                 # evs5 \<in> woolam"


declare Says_imp_knows_Spy [THEN analz.Inj, dest]
declare parts.Body  [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un  [dest]


(*A "possibility property": there are traces that reach the end*)
lemma "\<exists>NB. \<exists>evs \<in> woolam.
             Says Server B (Crypt (shrK B) \<lbrace>Agent A, Nonce NB\<rbrace>) \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] woolam.Nil
                    [THEN woolam.WL1, THEN woolam.WL2, THEN woolam.WL3,
                     THEN woolam.WL4, THEN woolam.WL5], possibility)
done

(*Could prove forwarding lemmas for WL4, but we do not need them!*)

(**** Inductive proofs about woolam ****)

(** Theorems of the form X \<notin> parts (spies evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees a good agent's shared key!*)
lemma Spy_see_shrK [simp]:
     "evs \<in> woolam \<Longrightarrow> (Key (shrK A) \<in> parts (spies evs)) = (A \<in> bad)"
by (erule woolam.induct, force, simp_all, blast+)

lemma Spy_analz_shrK [simp]:
     "evs \<in> woolam \<Longrightarrow> (Key (shrK A) \<in> analz (spies evs)) = (A \<in> bad)"
by auto

lemma Spy_see_shrK_D [dest!]:
     "\<lbrakk>Key (shrK A) \<in> parts (knows Spy evs);  evs \<in> woolam\<rbrakk> \<Longrightarrow> A \<in> bad"
by (blast dest: Spy_see_shrK)


(**** Autheticity properties for Woo-Lam ****)

(*** WL4 ***)

(*If the encrypted message appears then it originated with Alice*)
lemma NB_Crypt_imp_Alice_msg:
     "\<lbrakk>Crypt (shrK A) (Nonce NB) \<in> parts (spies evs);
         A \<notin> bad;  evs \<in> woolam\<rbrakk>
      \<Longrightarrow> \<exists>B. Says A B (Crypt (shrK A) (Nonce NB)) \<in> set evs"
by (erule rev_mp, erule woolam.induct, force, simp_all, blast+)

(*Guarantee for Server: if it gets a message containing a certificate from
  Alice, then she originated that certificate.  But we DO NOT know that B
  ever saw it: the Spy may have rerouted the message to the Server.*)
lemma Server_trusts_WL4 [dest]:
     "\<lbrakk>Says B' Server \<lbrace>Agent A, Agent B, Crypt (shrK A) (Nonce NB)\<rbrace>
           \<in> set evs;
         A \<notin> bad;  evs \<in> woolam\<rbrakk>
      \<Longrightarrow> \<exists>B. Says A B (Crypt (shrK A) (Nonce NB)) \<in> set evs"
by (blast intro!: NB_Crypt_imp_Alice_msg)


(*** WL5 ***)

(*Server sent WL5 only if it received the right sort of message*)
lemma Server_sent_WL5 [dest]:
     "\<lbrakk>Says Server B (Crypt (shrK B) \<lbrace>Agent A, NB\<rbrace>) \<in> set evs;
         evs \<in> woolam\<rbrakk>
      \<Longrightarrow> \<exists>B'. Says B' Server \<lbrace>Agent A, Agent B, Crypt (shrK A) NB\<rbrace>
             \<in> set evs"
by (erule rev_mp, erule woolam.induct, force, simp_all, blast+)

(*If the encrypted message appears then it originated with the Server!*)
lemma NB_Crypt_imp_Server_msg [rule_format]:
     "\<lbrakk>Crypt (shrK B) \<lbrace>Agent A, NB\<rbrace> \<in> parts (spies evs);
         B \<notin> bad;  evs \<in> woolam\<rbrakk>
      \<Longrightarrow> Says Server B (Crypt (shrK B) \<lbrace>Agent A, NB\<rbrace>) \<in> set evs"
by (erule rev_mp, erule woolam.induct, force, simp_all, blast+)

(*Guarantee for B.  If B gets the Server's certificate then A has encrypted
  the nonce using her key.  This event can be no older than the nonce itself.
  But A may have sent the nonce to some other agent and it could have reached
  the Server via the Spy.*)
lemma B_trusts_WL5:
     "\<lbrakk>Says S B (Crypt (shrK B) \<lbrace>Agent A, Nonce NB\<rbrace>) \<in> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> woolam\<rbrakk>
      \<Longrightarrow> \<exists>B. Says A B (Crypt (shrK A) (Nonce NB)) \<in> set evs"
by (blast dest!: NB_Crypt_imp_Server_msg)


(*B only issues challenges in response to WL1.  Not used.*)
lemma B_said_WL2:
     "\<lbrakk>Says B A (Nonce NB) \<in> set evs;  B \<noteq> Spy;  evs \<in> woolam\<rbrakk>
      \<Longrightarrow> \<exists>A'. Says A' B (Agent A) \<in> set evs"
by (erule rev_mp, erule woolam.induct, force, simp_all, blast+)


(**CANNOT be proved because A doesn't know where challenges come from...*)
lemma "\<lbrakk>A \<notin> bad;  B \<noteq> Spy;  evs \<in> woolam\<rbrakk>
  \<Longrightarrow> Crypt (shrK A) (Nonce NB) \<in> parts (spies evs) \<and>
      Says B A (Nonce NB) \<in> set evs
      \<longrightarrow> Says A B (Crypt (shrK A) (Nonce NB)) \<in> set evs"
apply (erule rev_mp, erule woolam.induct, force, simp_all, blast, auto)
oops

end
