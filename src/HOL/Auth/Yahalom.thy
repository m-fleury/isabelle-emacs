(*  Title:      HOL/Auth/Yahalom.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

section\<open>The Yahalom Protocol\<close>

theory Yahalom imports Public begin

text\<open>From page 257 of
  Burrows, Abadi and Needham (1989).  A Logic of Authentication.
  Proc. Royal Soc. 426

This theory has the prototypical example of a secrecy relation, KeyCryptNonce.
\<close>

inductive_set yahalom :: "event list set"
  where
         (*Initial trace is empty*)
   Nil:  "[] \<in> yahalom"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
 | Fake: "[| evsf \<in> yahalom;  X \<in> synth (analz (knows Spy evsf)) |]
          ==> Says Spy B X  # evsf \<in> yahalom"

         (*A message that has been sent can be received by the
           intended recipient.*)
 | Reception: "[| evsr \<in> yahalom;  Says A B X \<in> set evsr |]
               ==> Gets B X # evsr \<in> yahalom"

         (*Alice initiates a protocol run*)
 | YM1:  "[| evs1 \<in> yahalom;  Nonce NA \<notin> used evs1 |]
          ==> Says A B {|Agent A, Nonce NA|} # evs1 \<in> yahalom"

         (*Bob's response to Alice's message.*)
 | YM2:  "[| evs2 \<in> yahalom;  Nonce NB \<notin> used evs2;
             Gets B {|Agent A, Nonce NA|} \<in> set evs2 |]
          ==> Says B Server 
                  {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, Nonce NB|}|}
                # evs2 \<in> yahalom"

         (*The Server receives Bob's message.  He responds by sending a
            new session key to Alice, with a packet for forwarding to Bob.*)
 | YM3:  "[| evs3 \<in> yahalom;  Key KAB \<notin> used evs3;  KAB \<in> symKeys;
             Gets Server 
                  {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, Nonce NB|}|}
               \<in> set evs3 |]
          ==> Says Server A
                   {|Crypt (shrK A) {|Agent B, Key KAB, Nonce NA, Nonce NB|},
                     Crypt (shrK B) {|Agent A, Key KAB|}|}
                # evs3 \<in> yahalom"

 | YM4:  
       \<comment>\<open>Alice receives the Server's (?) message, checks her Nonce, and
           uses the new session key to send Bob his Nonce.  The premise
           @{term "A \<noteq> Server"} is needed for \<open>Says_Server_not_range\<close>.
           Alice can check that K is symmetric by its length.\<close>
         "[| evs4 \<in> yahalom;  A \<noteq> Server;  K \<in> symKeys;
             Gets A {|Crypt(shrK A) {|Agent B, Key K, Nonce NA, Nonce NB|}, X|}
                \<in> set evs4;
             Says A B {|Agent A, Nonce NA|} \<in> set evs4 |]
          ==> Says A B {|X, Crypt K (Nonce NB)|} # evs4 \<in> yahalom"

         (*This message models possible leaks of session keys.  The Nonces
           identify the protocol run.  Quoting Server here ensures they are
           correct.*)
 | Oops: "[| evso \<in> yahalom;  
             Says Server A {|Crypt (shrK A)
                                   {|Agent B, Key K, Nonce NA, Nonce NB|},
                             X|}  \<in> set evso |]
          ==> Notes Spy {|Nonce NA, Nonce NB, Key K|} # evso \<in> yahalom"


definition KeyWithNonce :: "[key, nat, event list] => bool" where
  "KeyWithNonce K NB evs ==
     \<exists>A B na X. 
       Says Server A {|Crypt (shrK A) {|Agent B, Key K, na, Nonce NB|}, X|} 
         \<in> set evs"


declare Says_imp_analz_Spy [dest]
declare parts.Body  [dest]
declare Fake_parts_insert_in_Un  [dest]
declare analz_into_parts [dest]

text\<open>A "possibility property": there are traces that reach the end\<close>
lemma "[| A \<noteq> Server; K \<in> symKeys; Key K \<notin> used [] |]
      ==> \<exists>X NB. \<exists>evs \<in> yahalom.
             Says A B {|X, Crypt K (Nonce NB)|} \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] yahalom.Nil
                    [THEN yahalom.YM1, THEN yahalom.Reception,
                     THEN yahalom.YM2, THEN yahalom.Reception,
                     THEN yahalom.YM3, THEN yahalom.Reception,
                     THEN yahalom.YM4])
apply (possibility, simp add: used_Cons)
done


subsection\<open>Regularity Lemmas for Yahalom\<close>

lemma Gets_imp_Says:
     "[| Gets B X \<in> set evs; evs \<in> yahalom |] ==> \<exists>A. Says A B X \<in> set evs"
by (erule rev_mp, erule yahalom.induct, auto)

text\<open>Must be proved separately for each protocol\<close>
lemma Gets_imp_knows_Spy:
     "[| Gets B X \<in> set evs; evs \<in> yahalom |]  ==> X \<in> knows Spy evs"
by (blast dest!: Gets_imp_Says Says_imp_knows_Spy)

lemmas Gets_imp_analz_Spy = Gets_imp_knows_Spy [THEN analz.Inj]
declare Gets_imp_analz_Spy [dest]


text\<open>Lets us treat YM4 using a similar argument as for the Fake case.\<close>
lemma YM4_analz_knows_Spy:
     "[| Gets A {|Crypt (shrK A) Y, X|} \<in> set evs;  evs \<in> yahalom |]
      ==> X \<in> analz (knows Spy evs)"
by blast

lemmas YM4_parts_knows_Spy =
       YM4_analz_knows_Spy [THEN analz_into_parts]

text\<open>For Oops\<close>
lemma YM4_Key_parts_knows_Spy:
     "Says Server A {|Crypt (shrK A) {|B,K,NA,NB|}, X|} \<in> set evs
      ==> K \<in> parts (knows Spy evs)"
  by (metis parts.Body parts.Fst parts.Snd  Says_imp_knows_Spy parts.Inj)

text\<open>Theorems of the form @{term "X \<notin> parts (knows Spy evs)"} imply 
that NOBODY sends messages containing X!\<close>

text\<open>Spy never sees a good agent's shared key!\<close>
lemma Spy_see_shrK [simp]:
     "evs \<in> yahalom ==> (Key (shrK A) \<in> parts (knows Spy evs)) = (A \<in> bad)"
by (erule yahalom.induct, force,
    drule_tac [6] YM4_parts_knows_Spy, simp_all, blast+)

lemma Spy_analz_shrK [simp]:
     "evs \<in> yahalom ==> (Key (shrK A) \<in> analz (knows Spy evs)) = (A \<in> bad)"
by auto

lemma Spy_see_shrK_D [dest!]:
     "[|Key (shrK A) \<in> parts (knows Spy evs);  evs \<in> yahalom|] ==> A \<in> bad"
by (blast dest: Spy_see_shrK)

text\<open>Nobody can have used non-existent keys!
    Needed to apply \<open>analz_insert_Key\<close>\<close>
lemma new_keys_not_used [simp]:
    "[|Key K \<notin> used evs; K \<in> symKeys; evs \<in> yahalom|]
     ==> K \<notin> keysFor (parts (spies evs))"
apply (erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
txt\<open>Fake\<close>
apply (force dest!: keysFor_parts_insert, auto)
done


text\<open>Earlier, all protocol proofs declared this theorem.
  But only a few proofs need it, e.g. Yahalom and Kerberos IV.\<close>
lemma new_keys_not_analzd:
 "[|K \<in> symKeys; evs \<in> yahalom; Key K \<notin> used evs|]
  ==> K \<notin> keysFor (analz (knows Spy evs))"
by (blast dest: new_keys_not_used intro: keysFor_mono [THEN subsetD])


text\<open>Describes the form of K when the Server sends this message.  Useful for
  Oops as well as main secrecy property.\<close>
lemma Says_Server_not_range [simp]:
     "[| Says Server A {|Crypt (shrK A) {|Agent B, Key K, na, nb|}, X|}
           \<in> set evs;   evs \<in> yahalom |]
      ==> K \<notin> range shrK"
by (erule rev_mp, erule yahalom.induct, simp_all)


subsection\<open>Secrecy Theorems\<close>

(****
 The following is to prove theorems of the form

  Key K \<in> analz (insert (Key KAB) (knows Spy evs)) ==>
  Key K \<in> analz (knows Spy evs)

 A more general formula must be proved inductively.
****)

text\<open>Session keys are not used to encrypt other session keys\<close>

lemma analz_image_freshK [rule_format]:
 "evs \<in> yahalom ==>
   \<forall>K KK. KK <= - (range shrK) -->
          (Key K \<in> analz (Key`KK Un (knows Spy evs))) =
          (K \<in> KK | Key K \<in> analz (knows Spy evs))"
apply (erule yahalom.induct,
       drule_tac [7] YM4_analz_knows_Spy, analz_freshK, spy_analz, blast)
apply (simp only: Says_Server_not_range analz_image_freshK_simps)
apply safe
done

lemma analz_insert_freshK:
     "[| evs \<in> yahalom;  KAB \<notin> range shrK |] ==>
      (Key K \<in> analz (insert (Key KAB) (knows Spy evs))) =
      (K = KAB | Key K \<in> analz (knows Spy evs))"
by (simp only: analz_image_freshK analz_image_freshK_simps)


text\<open>The Key K uniquely identifies the Server's  message.\<close>
lemma unique_session_keys:
     "[| Says Server A
          {|Crypt (shrK A) {|Agent B, Key K, na, nb|}, X|} \<in> set evs;
        Says Server A'
          {|Crypt (shrK A') {|Agent B', Key K, na', nb'|}, X'|} \<in> set evs;
        evs \<in> yahalom |]
     ==> A=A' & B=B' & na=na' & nb=nb'"
apply (erule rev_mp, erule rev_mp)
apply (erule yahalom.induct, simp_all)
txt\<open>YM3, by freshness, and YM4\<close>
apply blast+
done


text\<open>Crucial secrecy property: Spy does not see the keys sent in msg YM3\<close>
lemma secrecy_lemma:
     "[| A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Says Server A
            {|Crypt (shrK A) {|Agent B, Key K, na, nb|},
              Crypt (shrK B) {|Agent A, Key K|}|}
           \<in> set evs -->
          Notes Spy {|na, nb, Key K|} \<notin> set evs -->
          Key K \<notin> analz (knows Spy evs)"
apply (erule yahalom.induct, force,
       drule_tac [6] YM4_analz_knows_Spy)
apply (simp_all add: pushes analz_insert_eq analz_insert_freshK, spy_analz)   \<comment>\<open>Fake\<close>
apply (blast dest: unique_session_keys)+  \<comment>\<open>YM3, Oops\<close>
done

text\<open>Final version\<close>
lemma Spy_not_see_encrypted_key:
     "[| Says Server A
            {|Crypt (shrK A) {|Agent B, Key K, na, nb|},
              Crypt (shrK B) {|Agent A, Key K|}|}
           \<in> set evs;
         Notes Spy {|na, nb, Key K|} \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Key K \<notin> analz (knows Spy evs)"
by (blast dest: secrecy_lemma)


subsubsection\<open>Security Guarantee for A upon receiving YM3\<close>

text\<open>If the encrypted message appears then it originated with the Server\<close>
lemma A_trusts_YM3:
     "[| Crypt (shrK A) {|Agent B, Key K, na, nb|} \<in> parts (knows Spy evs);
         A \<notin> bad;  evs \<in> yahalom |]
       ==> Says Server A
            {|Crypt (shrK A) {|Agent B, Key K, na, nb|},
              Crypt (shrK B) {|Agent A, Key K|}|}
           \<in> set evs"
apply (erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
txt\<open>Fake, YM3\<close>
apply blast+
done

text\<open>The obvious combination of \<open>A_trusts_YM3\<close> with
  \<open>Spy_not_see_encrypted_key\<close>\<close>
lemma A_gets_good_key:
     "[| Crypt (shrK A) {|Agent B, Key K, na, nb|} \<in> parts (knows Spy evs);
         Notes Spy {|na, nb, Key K|} \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Key K \<notin> analz (knows Spy evs)"
  by (metis A_trusts_YM3 secrecy_lemma)


subsubsection\<open>Security Guarantees for B upon receiving YM4\<close>

text\<open>B knows, by the first part of A's message, that the Server distributed
  the key for A and B.  But this part says nothing about nonces.\<close>
lemma B_trusts_YM4_shrK:
     "[| Crypt (shrK B) {|Agent A, Key K|} \<in> parts (knows Spy evs);
         B \<notin> bad;  evs \<in> yahalom |]
      ==> \<exists>NA NB. Says Server A
                      {|Crypt (shrK A) {|Agent B, Key K,
                                         Nonce NA, Nonce NB|},
                        Crypt (shrK B) {|Agent A, Key K|}|}
                     \<in> set evs"
apply (erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
txt\<open>Fake, YM3\<close>
apply blast+
done

text\<open>B knows, by the second part of A's message, that the Server
  distributed the key quoting nonce NB.  This part says nothing about
  agent names.  Secrecy of NB is crucial.  Note that @{term "Nonce NB
  \<notin> analz(knows Spy evs)"} must be the FIRST antecedent of the
  induction formula.\<close>

lemma B_trusts_YM4_newK [rule_format]:
     "[|Crypt K (Nonce NB) \<in> parts (knows Spy evs);
        Nonce NB \<notin> analz (knows Spy evs);  evs \<in> yahalom|]
      ==> \<exists>A B NA. Says Server A
                      {|Crypt (shrK A) {|Agent B, Key K, Nonce NA, Nonce NB|},
                        Crypt (shrK B) {|Agent A, Key K|}|}
                     \<in> set evs"
apply (erule rev_mp, erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy)
apply (analz_mono_contra, simp_all)
txt\<open>Fake, YM3\<close>
apply blast
apply blast
txt\<open>YM4.  A is uncompromised because NB is secure
  A's certificate guarantees the existence of the Server message\<close>
apply (blast dest!: Gets_imp_Says Crypt_Spy_analz_bad
             dest: Says_imp_spies
                   parts.Inj [THEN parts.Fst, THEN A_trusts_YM3])
done


subsubsection\<open>Towards proving secrecy of Nonce NB\<close>

text\<open>Lemmas about the predicate KeyWithNonce\<close>

lemma KeyWithNonceI:
 "Says Server A
          {|Crypt (shrK A) {|Agent B, Key K, na, Nonce NB|}, X|}
        \<in> set evs ==> KeyWithNonce K NB evs"
by (unfold KeyWithNonce_def, blast)

lemma KeyWithNonce_Says [simp]:
   "KeyWithNonce K NB (Says S A X # evs) =
      (Server = S &
       (\<exists>B n X'. X = {|Crypt (shrK A) {|Agent B, Key K, n, Nonce NB|}, X'|})
      | KeyWithNonce K NB evs)"
by (simp add: KeyWithNonce_def, blast)


lemma KeyWithNonce_Notes [simp]:
   "KeyWithNonce K NB (Notes A X # evs) = KeyWithNonce K NB evs"
by (simp add: KeyWithNonce_def)

lemma KeyWithNonce_Gets [simp]:
   "KeyWithNonce K NB (Gets A X # evs) = KeyWithNonce K NB evs"
by (simp add: KeyWithNonce_def)

text\<open>A fresh key cannot be associated with any nonce
  (with respect to a given trace).\<close>
lemma fresh_not_KeyWithNonce:
     "Key K \<notin> used evs ==> ~ KeyWithNonce K NB evs"
by (unfold KeyWithNonce_def, blast)

text\<open>The Server message associates K with NB' and therefore not with any
  other nonce NB.\<close>
lemma Says_Server_KeyWithNonce:
 "[| Says Server A {|Crypt (shrK A) {|Agent B, Key K, na, Nonce NB'|}, X|}
       \<in> set evs;
     NB \<noteq> NB';  evs \<in> yahalom |]
  ==> ~ KeyWithNonce K NB evs"
by (unfold KeyWithNonce_def, blast dest: unique_session_keys)


text\<open>The only nonces that can be found with the help of session keys are
  those distributed as nonce NB by the Server.  The form of the theorem
  recalls \<open>analz_image_freshK\<close>, but it is much more complicated.\<close>


text\<open>As with \<open>analz_image_freshK\<close>, we take some pains to express the 
  property as a logical equivalence so that the simplifier can apply it.\<close>
lemma Nonce_secrecy_lemma:
     "P --> (X \<in> analz (G Un H)) --> (X \<in> analz H)  ==>
      P --> (X \<in> analz (G Un H)) = (X \<in> analz H)"
by (blast intro: analz_mono [THEN subsetD])

lemma Nonce_secrecy:
     "evs \<in> yahalom ==>
      (\<forall>KK. KK <= - (range shrK) -->
           (\<forall>K \<in> KK. K \<in> symKeys --> ~ KeyWithNonce K NB evs)   -->
           (Nonce NB \<in> analz (Key`KK Un (knows Spy evs))) =
           (Nonce NB \<in> analz (knows Spy evs)))"
apply (erule yahalom.induct,
       frule_tac [7] YM4_analz_knows_Spy)
apply (safe del: allI impI intro!: Nonce_secrecy_lemma [THEN impI, THEN allI])
apply (simp_all del: image_insert image_Un
       add: analz_image_freshK_simps split_ifs
            all_conj_distrib ball_conj_distrib
            analz_image_freshK fresh_not_KeyWithNonce
            imp_disj_not1               (*Moves NBa\<noteq>NB to the front*)
            Says_Server_KeyWithNonce)
txt\<open>For Oops, simplification proves @{prop "NBa\<noteq>NB"}.  By
  @{term Says_Server_KeyWithNonce}, we get @{prop "~ KeyWithNonce K NB
  evs"}; then simplification can apply the induction hypothesis with
  @{term "KK = {K}"}.\<close>
txt\<open>Fake\<close>
apply spy_analz
txt\<open>YM2\<close>
apply blast
txt\<open>YM3\<close>
apply blast
txt\<open>YM4\<close>
apply (erule_tac V = "\<forall>KK. P KK" for P in thin_rl, clarify)
txt\<open>If @{prop "A \<in> bad"} then @{term NBa} is known, therefore
  @{prop "NBa \<noteq> NB"}.  Previous two steps make the next step
  faster.\<close>
apply (metis A_trusts_YM3 Gets_imp_analz_Spy Gets_imp_knows_Spy KeyWithNonce_def
      Spy_analz_shrK analz.Fst analz.Snd analz_shrK_Decrypt parts.Fst parts.Inj)
done


text\<open>Version required below: if NB can be decrypted using a session key then
   it was distributed with that key.  The more general form above is required
   for the induction to carry through.\<close>
lemma single_Nonce_secrecy:
     "[| Says Server A
          {|Crypt (shrK A) {|Agent B, Key KAB, na, Nonce NB'|}, X|}
         \<in> set evs;
         NB \<noteq> NB';  KAB \<notin> range shrK;  evs \<in> yahalom |]
      ==> (Nonce NB \<in> analz (insert (Key KAB) (knows Spy evs))) =
          (Nonce NB \<in> analz (knows Spy evs))"
by (simp_all del: image_insert image_Un imp_disjL
             add: analz_image_freshK_simps split_ifs
                  Nonce_secrecy Says_Server_KeyWithNonce)


subsubsection\<open>The Nonce NB uniquely identifies B's message.\<close>

lemma unique_NB:
     "[| Crypt (shrK B) {|Agent A, Nonce NA, nb|} \<in> parts (knows Spy evs);
         Crypt (shrK B') {|Agent A', Nonce NA', nb|} \<in> parts (knows Spy evs);
        evs \<in> yahalom;  B \<notin> bad;  B' \<notin> bad |]
      ==> NA' = NA & A' = A & B' = B"
apply (erule rev_mp, erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
txt\<open>Fake, and YM2 by freshness\<close>
apply blast+
done


text\<open>Variant useful for proving secrecy of NB.  Because nb is assumed to be
  secret, we no longer must assume B, B' not bad.\<close>
lemma Says_unique_NB:
     "[| Says C S   {|X,  Crypt (shrK B) {|Agent A, Nonce NA, nb|}|}
           \<in> set evs;
         Gets S' {|X', Crypt (shrK B') {|Agent A', Nonce NA', nb|}|}
           \<in> set evs;
         nb \<notin> analz (knows Spy evs);  evs \<in> yahalom |]
      ==> NA' = NA & A' = A & B' = B"
by (blast dest!: Gets_imp_Says Crypt_Spy_analz_bad
          dest: Says_imp_spies unique_NB parts.Inj analz.Inj)


subsubsection\<open>A nonce value is never used both as NA and as NB\<close>

lemma no_nonce_YM1_YM2:
     "[|Crypt (shrK B') {|Agent A', Nonce NB, nb'|} \<in> parts(knows Spy evs);
        Nonce NB \<notin> analz (knows Spy evs);  evs \<in> yahalom|]
  ==> Crypt (shrK B)  {|Agent A, na, Nonce NB|} \<notin> parts(knows Spy evs)"
apply (erule rev_mp, erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy)
apply (analz_mono_contra, simp_all)
txt\<open>Fake, YM2\<close>
apply blast+
done

text\<open>The Server sends YM3 only in response to YM2.\<close>
lemma Says_Server_imp_YM2:
     "[| Says Server A {|Crypt (shrK A) {|Agent B, k, na, nb|}, X|} \<in> set evs;
         evs \<in> yahalom |]
      ==> Gets Server {| Agent B, Crypt (shrK B) {|Agent A, na, nb|} |}
             \<in> set evs"
by (erule rev_mp, erule yahalom.induct, auto)

text\<open>A vital theorem for B, that nonce NB remains secure from the Spy.\<close>
lemma Spy_not_see_NB :
     "[| Says B Server
                {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, Nonce NB|}|}
           \<in> set evs;
         (\<forall>k. Notes Spy {|Nonce NA, Nonce NB, k|} \<notin> set evs);
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Nonce NB \<notin> analz (knows Spy evs)"
apply (erule rev_mp, erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_analz_knows_Spy)
apply (simp_all add: split_ifs pushes new_keys_not_analzd analz_insert_eq
                     analz_insert_freshK)
txt\<open>Fake\<close>
apply spy_analz
txt\<open>YM1: NB=NA is impossible anyway, but NA is secret because it is fresh!\<close>
apply blast
txt\<open>YM2\<close>
apply blast
txt\<open>Prove YM3 by showing that no NB can also be an NA\<close>
apply (blast dest!: no_nonce_YM1_YM2 dest: Gets_imp_Says Says_unique_NB)
txt\<open>LEVEL 7: YM4 and Oops remain\<close>
apply (clarify, simp add: all_conj_distrib)
txt\<open>YM4: key K is visible to Spy, contradicting session key secrecy theorem\<close>
txt\<open>Case analysis on Aa:bad; PROOF FAILED problems
  use \<open>Says_unique_NB\<close> to identify message components: @{term "Aa=A"}, @{term "Ba=B"}\<close>
apply (blast dest!: Says_unique_NB analz_shrK_Decrypt
                    parts.Inj [THEN parts.Fst, THEN A_trusts_YM3]
             dest: Gets_imp_Says Says_imp_spies Says_Server_imp_YM2
                   Spy_not_see_encrypted_key)
txt\<open>Oops case: if the nonce is betrayed now, show that the Oops event is
  covered by the quantified Oops assumption.\<close>
apply (clarify, simp add: all_conj_distrib)
apply (frule Says_Server_imp_YM2, assumption)
apply (metis Gets_imp_Says Says_Server_not_range Says_unique_NB no_nonce_YM1_YM2 parts.Snd single_Nonce_secrecy spies_partsEs(1))
done


text\<open>B's session key guarantee from YM4.  The two certificates contribute to a
  single conclusion about the Server's message.  Note that the "Notes Spy"
  assumption must quantify over \<open>\<forall>\<close> POSSIBLE keys instead of our particular K.
  If this run is broken and the spy substitutes a certificate containing an
  old key, B has no means of telling.\<close>
lemma B_trusts_YM4:
     "[| Gets B {|Crypt (shrK B) {|Agent A, Key K|},
                  Crypt K (Nonce NB)|} \<in> set evs;
         Says B Server
           {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, Nonce NB|}|}
           \<in> set evs;
         \<forall>k. Notes Spy {|Nonce NA, Nonce NB, k|} \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
       ==> Says Server A
                   {|Crypt (shrK A) {|Agent B, Key K,
                             Nonce NA, Nonce NB|},
                     Crypt (shrK B) {|Agent A, Key K|}|}
             \<in> set evs"
by (blast dest: Spy_not_see_NB Says_unique_NB
                Says_Server_imp_YM2 B_trusts_YM4_newK)



text\<open>The obvious combination of \<open>B_trusts_YM4\<close> with 
  \<open>Spy_not_see_encrypted_key\<close>\<close>
lemma B_gets_good_key:
     "[| Gets B {|Crypt (shrK B) {|Agent A, Key K|},
                  Crypt K (Nonce NB)|} \<in> set evs;
         Says B Server
           {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, Nonce NB|}|}
           \<in> set evs;
         \<forall>k. Notes Spy {|Nonce NA, Nonce NB, k|} \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Key K \<notin> analz (knows Spy evs)"
  by (metis B_trusts_YM4 Spy_not_see_encrypted_key)


subsection\<open>Authenticating B to A\<close>

text\<open>The encryption in message YM2 tells us it cannot be faked.\<close>
lemma B_Said_YM2 [rule_format]:
     "[|Crypt (shrK B) {|Agent A, Nonce NA, nb|} \<in> parts (knows Spy evs);
        evs \<in> yahalom|]
      ==> B \<notin> bad -->
          Says B Server {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, nb|}|}
            \<in> set evs"
apply (erule rev_mp, erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
txt\<open>Fake\<close>
apply blast
done

text\<open>If the server sends YM3 then B sent YM2\<close>
lemma YM3_auth_B_to_A_lemma:
     "[|Says Server A {|Crypt (shrK A) {|Agent B, Key K, Nonce NA, nb|}, X|}
       \<in> set evs;  evs \<in> yahalom|]
      ==> B \<notin> bad -->
          Says B Server {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, nb|}|}
            \<in> set evs"
apply (erule rev_mp, erule yahalom.induct, simp_all)
txt\<open>YM3, YM4\<close>
apply (blast dest!: B_Said_YM2)+
done

text\<open>If A receives YM3 then B has used nonce NA (and therefore is alive)\<close>
lemma YM3_auth_B_to_A:
     "[| Gets A {|Crypt (shrK A) {|Agent B, Key K, Nonce NA, nb|}, X|}
           \<in> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Says B Server {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, nb|}|}
       \<in> set evs"
  by (metis A_trusts_YM3 Gets_imp_analz_Spy YM3_auth_B_to_A_lemma analz.Fst
         not_parts_not_analz)


subsection\<open>Authenticating A to B using the certificate 
  @{term "Crypt K (Nonce NB)"}\<close>

text\<open>Assuming the session key is secure, if both certificates are present then
  A has said NB.  We can't be sure about the rest of A's message, but only
  NB matters for freshness.\<close>
lemma A_Said_YM3_lemma [rule_format]:
     "evs \<in> yahalom
      ==> Key K \<notin> analz (knows Spy evs) -->
          Crypt K (Nonce NB) \<in> parts (knows Spy evs) -->
          Crypt (shrK B) {|Agent A, Key K|} \<in> parts (knows Spy evs) -->
          B \<notin> bad -->
          (\<exists>X. Says A B {|X, Crypt K (Nonce NB)|} \<in> set evs)"
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy)
apply (analz_mono_contra, simp_all)
txt\<open>Fake\<close>
apply blast
txt\<open>YM3: by \<open>new_keys_not_used\<close>, the message
   @{term "Crypt K (Nonce NB)"} could not exist\<close>
apply (force dest!: Crypt_imp_keysFor)
txt\<open>YM4: was @{term "Crypt K (Nonce NB)"} the very last message?
    If not, use the induction hypothesis\<close>
apply (simp add: ex_disj_distrib)
txt\<open>yes: apply unicity of session keys\<close>
apply (blast dest!: Gets_imp_Says A_trusts_YM3 B_trusts_YM4_shrK
                    Crypt_Spy_analz_bad
             dest: Says_imp_knows_Spy [THEN parts.Inj] unique_session_keys)
done

text\<open>If B receives YM4 then A has used nonce NB (and therefore is alive).
  Moreover, A associates K with NB (thus is talking about the same run).
  Other premises guarantee secrecy of K.\<close>
lemma YM4_imp_A_Said_YM3 [rule_format]:
     "[| Gets B {|Crypt (shrK B) {|Agent A, Key K|},
                  Crypt K (Nonce NB)|} \<in> set evs;
         Says B Server
           {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, Nonce NB|}|}
           \<in> set evs;
         (\<forall>NA k. Notes Spy {|Nonce NA, Nonce NB, k|} \<notin> set evs);
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> \<exists>X. Says A B {|X, Crypt K (Nonce NB)|} \<in> set evs"
by (metis A_Said_YM3_lemma B_gets_good_key Gets_imp_analz_Spy YM4_parts_knows_Spy analz.Fst not_parts_not_analz)
end
