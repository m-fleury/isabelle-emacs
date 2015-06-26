(*  Title:      HOL/TLA/Memory/Memory.thy
    Author:     Stephan Merz, University of Munich
*)

section \<open>RPC-Memory example: Memory specification\<close>

theory Memory
imports MemoryParameters ProcedureInterface
begin

type_synonym memChType = "(memOp, Vals) channel"
type_synonym memType = "(Locs \<Rightarrow> Vals) stfun"  (* intention: MemLocs \<Rightarrow> MemVals *)
type_synonym resType = "(PrIds \<Rightarrow> Vals) stfun"

consts
  (* state predicates *)
  MInit      :: "memType \<Rightarrow> Locs \<Rightarrow> stpred"
  PInit      :: "resType \<Rightarrow> PrIds \<Rightarrow> stpred"
  (* auxiliary predicates: is there a pending read/write request for
     some process id and location/value? *)
  RdRequest  :: "memChType \<Rightarrow> PrIds \<Rightarrow> Locs \<Rightarrow> stpred"
  WrRequest  :: "memChType \<Rightarrow> PrIds \<Rightarrow> Locs \<Rightarrow> Vals \<Rightarrow> stpred"

  (* actions *)
  GoodRead   :: "memType \<Rightarrow> resType \<Rightarrow> PrIds \<Rightarrow> Locs \<Rightarrow> action"
  BadRead    :: "memType \<Rightarrow> resType \<Rightarrow> PrIds \<Rightarrow> Locs \<Rightarrow> action"
  ReadInner  :: "memChType \<Rightarrow> memType \<Rightarrow> resType \<Rightarrow> PrIds \<Rightarrow> Locs \<Rightarrow> action"
  Read       :: "memChType \<Rightarrow> memType \<Rightarrow> resType \<Rightarrow> PrIds \<Rightarrow> action"
  GoodWrite  :: "memType \<Rightarrow> resType \<Rightarrow> PrIds \<Rightarrow> Locs \<Rightarrow> Vals \<Rightarrow> action"
  BadWrite   :: "memType \<Rightarrow> resType \<Rightarrow> PrIds \<Rightarrow> Locs \<Rightarrow> Vals \<Rightarrow> action"
  WriteInner :: "memChType \<Rightarrow> memType \<Rightarrow> resType \<Rightarrow> PrIds \<Rightarrow> Locs \<Rightarrow> Vals \<Rightarrow> action"
  Write      :: "memChType \<Rightarrow> memType \<Rightarrow> resType \<Rightarrow> PrIds \<Rightarrow> Locs \<Rightarrow> action"
  MemReturn  :: "memChType \<Rightarrow> resType \<Rightarrow> PrIds \<Rightarrow> action"
  MemFail    :: "memChType \<Rightarrow> resType \<Rightarrow> PrIds \<Rightarrow> action"
  RNext      :: "memChType \<Rightarrow> memType \<Rightarrow> resType \<Rightarrow> PrIds \<Rightarrow> action"
  UNext      :: "memChType \<Rightarrow> memType \<Rightarrow> resType \<Rightarrow> PrIds \<Rightarrow> action"

  (* temporal formulas *)
  RPSpec     :: "memChType \<Rightarrow> memType \<Rightarrow> resType \<Rightarrow> PrIds \<Rightarrow> temporal"
  UPSpec     :: "memChType \<Rightarrow> memType \<Rightarrow> resType \<Rightarrow> PrIds \<Rightarrow> temporal"
  MSpec      :: "memChType \<Rightarrow> memType \<Rightarrow> resType \<Rightarrow> Locs \<Rightarrow> temporal"
  IRSpec     :: "memChType \<Rightarrow> memType \<Rightarrow> resType \<Rightarrow> temporal"
  IUSpec     :: "memChType \<Rightarrow> memType \<Rightarrow> resType \<Rightarrow> temporal"

  RSpec      :: "memChType \<Rightarrow> resType \<Rightarrow> temporal"
  USpec      :: "memChType \<Rightarrow> temporal"

  (* memory invariant: in the paper, the invariant is hidden in the definition of
     the predicate S used in the implementation proof, but it is easier to verify
     at this level. *)
  MemInv    :: "memType \<Rightarrow> Locs \<Rightarrow> stpred"

defs
  MInit_def:         "MInit mm l == PRED mm!l = #InitVal"
  PInit_def:         "PInit rs p == PRED rs!p = #NotAResult"

  RdRequest_def:     "RdRequest ch p l == PRED
                         Calling ch p \<and> (arg<ch!p> = #(read l))"
  WrRequest_def:     "WrRequest ch p l v == PRED
                         Calling ch p \<and> (arg<ch!p> = #(write l v))"
  (* a read that doesn't raise BadArg *)
  GoodRead_def:      "GoodRead mm rs p l == ACT
                        #l \<in> #MemLoc \<and> ((rs!p)$ = $(mm!l))"
  (* a read that raises BadArg *)
  BadRead_def:       "BadRead mm rs p l == ACT
                        #l \<notin> #MemLoc \<and> ((rs!p)$ = #BadArg)"
  (* the read action with l visible *)
  ReadInner_def:     "ReadInner ch mm rs p l == ACT
                         $(RdRequest ch p l)
                         \<and> (GoodRead mm rs p l  \<or>  BadRead mm rs p l)
                         \<and> unchanged (rtrner ch ! p)"
  (* the read action with l quantified *)
  Read_def:          "Read ch mm rs p == ACT (\<exists>l. ReadInner ch mm rs p l)"

  (* similar definitions for the write action *)
  GoodWrite_def:     "GoodWrite mm rs p l v == ACT
                        #l \<in> #MemLoc \<and> #v \<in> #MemVal
                        \<and> ((mm!l)$ = #v) \<and> ((rs!p)$ = #OK)"
  BadWrite_def:      "BadWrite mm rs p l v == ACT
                        \<not> (#l \<in> #MemLoc \<and> #v \<in> #MemVal)
                        \<and> ((rs!p)$ = #BadArg) \<and> unchanged (mm!l)"
  WriteInner_def:    "WriteInner ch mm rs p l v == ACT
                        $(WrRequest ch p l v)
                        \<and> (GoodWrite mm rs p l v  \<or>  BadWrite mm rs p l v)
                        \<and> unchanged (rtrner ch ! p)"
  Write_def:         "Write ch mm rs p l == ACT (\<exists>v. WriteInner ch mm rs p l v)"

  (* the return action *)
  MemReturn_def:     "MemReturn ch rs p == ACT
                       (   ($(rs!p) \<noteq> #NotAResult)
                        \<and> ((rs!p)$ = #NotAResult)
                        \<and> Return ch p (rs!p))"

  (* the failure action of the unreliable memory *)
  MemFail_def:       "MemFail ch rs p == ACT
                        $(Calling ch p)
                        \<and> ((rs!p)$ = #MemFailure)
                        \<and> unchanged (rtrner ch ! p)"
  (* next-state relations for reliable / unreliable memory *)
  RNext_def:         "RNext ch mm rs p == ACT
                       (  Read ch mm rs p
                        \<or> (\<exists>l. Write ch mm rs p l)
                        \<or> MemReturn ch rs p)"
  UNext_def:         "UNext ch mm rs p == ACT
                        (RNext ch mm rs p \<or> MemFail ch rs p)"

  RPSpec_def:        "RPSpec ch mm rs p == TEMP
                        Init(PInit rs p)
                        \<and> \<box>[ RNext ch mm rs p ]_(rtrner ch ! p, rs!p)
                        \<and> WF(RNext ch mm rs p)_(rtrner ch ! p, rs!p)
                        \<and> WF(MemReturn ch rs p)_(rtrner ch ! p, rs!p)"
  UPSpec_def:        "UPSpec ch mm rs p == TEMP
                        Init(PInit rs p)
                        \<and> \<box>[ UNext ch mm rs p ]_(rtrner ch ! p, rs!p)
                        \<and> WF(RNext ch mm rs p)_(rtrner ch ! p, rs!p)
                        \<and> WF(MemReturn ch rs p)_(rtrner ch ! p, rs!p)"
  MSpec_def:         "MSpec ch mm rs l == TEMP
                        Init(MInit mm l)
                        \<and> \<box>[ \<exists>p. Write ch mm rs p l ]_(mm!l)"
  IRSpec_def:        "IRSpec ch mm rs == TEMP
                        (\<forall>p. RPSpec ch mm rs p)
                        \<and> (\<forall>l. #l \<in> #MemLoc \<longrightarrow> MSpec ch mm rs l)"
  IUSpec_def:        "IUSpec ch mm rs == TEMP
                        (\<forall>p. UPSpec ch mm rs p)
                        \<and> (\<forall>l. #l \<in> #MemLoc \<longrightarrow> MSpec ch mm rs l)"

  RSpec_def:         "RSpec ch rs == TEMP (\<exists>\<exists>mm. IRSpec ch mm rs)"
  USpec_def:         "USpec ch == TEMP (\<exists>\<exists>mm rs. IUSpec ch mm rs)"

  MemInv_def:        "MemInv mm l == PRED  #l \<in> #MemLoc \<longrightarrow> mm!l \<in> #MemVal"

lemmas RM_action_defs =
  MInit_def PInit_def RdRequest_def WrRequest_def MemInv_def
  GoodRead_def BadRead_def ReadInner_def Read_def
  GoodWrite_def BadWrite_def WriteInner_def Write_def
  MemReturn_def RNext_def

lemmas UM_action_defs = RM_action_defs MemFail_def UNext_def

lemmas RM_temp_defs = RPSpec_def MSpec_def IRSpec_def
lemmas UM_temp_defs = UPSpec_def MSpec_def IUSpec_def


(* The reliable memory is an implementation of the unreliable one *)
lemma ReliableImplementsUnReliable: "\<turnstile> IRSpec ch mm rs \<longrightarrow> IUSpec ch mm rs"
  by (force simp: UNext_def UPSpec_def IUSpec_def RM_temp_defs elim!: STL4E [temp_use] squareE)

(* The memory spec implies the memory invariant *)
lemma MemoryInvariant: "\<turnstile> MSpec ch mm rs l \<longrightarrow> \<box>(MemInv mm l)"
  by (auto_invariant simp: RM_temp_defs RM_action_defs)

(* The invariant is trivial for non-locations *)
lemma NonMemLocInvariant: "\<turnstile> #l \<notin> #MemLoc \<longrightarrow> \<box>(MemInv mm l)"
  by (auto simp: MemInv_def intro!: necT [temp_use])

lemma MemoryInvariantAll:
    "\<turnstile> (\<forall>l. #l \<in> #MemLoc \<longrightarrow> MSpec ch mm rs l) \<longrightarrow> (\<forall>l. \<box>(MemInv mm l))"
  apply clarify
  apply (auto elim!: MemoryInvariant [temp_use] NonMemLocInvariant [temp_use])
  done

(* The memory engages in an action for process p only if there is an
   unanswered call from p.
   We need this only for the reliable memory.
*)

lemma Memoryidle: "\<turnstile> \<not>$(Calling ch p) \<longrightarrow> \<not> RNext ch mm rs p"
  by (auto simp: Return_def RM_action_defs)

(* Enabledness conditions *)

lemma MemReturn_change: "\<turnstile> MemReturn ch rs p \<longrightarrow> <MemReturn ch rs p>_(rtrner ch ! p, rs!p)"
  by (force simp: MemReturn_def angle_def)

lemma MemReturn_enabled: "\<And>p. basevars (rtrner ch ! p, rs!p) \<Longrightarrow>
      \<turnstile> Calling ch p \<and> (rs!p \<noteq> #NotAResult)
         \<longrightarrow> Enabled (<MemReturn ch rs p>_(rtrner ch ! p, rs!p))"
  apply (tactic
    \<open>action_simp_tac @{context} [@{thm MemReturn_change} RSN (2, @{thm enabled_mono}) ] [] 1\<close>)
  apply (tactic
    \<open>action_simp_tac (@{context} addsimps [@{thm MemReturn_def}, @{thm Return_def},
      @{thm rtrner_def}]) [exI] [@{thm base_enabled}, @{thm Pair_inject}] 1\<close>)
  done

lemma ReadInner_enabled: "\<And>p. basevars (rtrner ch ! p, rs!p) \<Longrightarrow>
      \<turnstile> Calling ch p \<and> (arg<ch!p> = #(read l)) \<longrightarrow> Enabled (ReadInner ch mm rs p l)"
  apply (case_tac "l : MemLoc")
  apply (force simp: ReadInner_def GoodRead_def BadRead_def RdRequest_def
    intro!: exI elim!: base_enabled [temp_use])+
  done

lemma WriteInner_enabled: "\<And>p. basevars (mm!l, rtrner ch ! p, rs!p) \<Longrightarrow>
      \<turnstile> Calling ch p \<and> (arg<ch!p> = #(write l v))
         \<longrightarrow> Enabled (WriteInner ch mm rs p l v)"
  apply (case_tac "l:MemLoc & v:MemVal")
  apply (force simp: WriteInner_def GoodWrite_def BadWrite_def WrRequest_def
    intro!: exI elim!: base_enabled [temp_use])+
  done

lemma ReadResult: "\<turnstile> Read ch mm rs p \<and> (\<forall>l. $(MemInv mm l)) \<longrightarrow> (rs!p)` \<noteq> #NotAResult"
  by (force simp: Read_def ReadInner_def GoodRead_def BadRead_def MemInv_def)

lemma WriteResult: "\<turnstile> Write ch mm rs p l \<longrightarrow> (rs!p)` \<noteq> #NotAResult"
  by (auto simp: Write_def WriteInner_def GoodWrite_def BadWrite_def)

lemma ReturnNotReadWrite: "\<turnstile> (\<forall>l. $MemInv mm l) \<and> MemReturn ch rs p
         \<longrightarrow> \<not> Read ch mm rs p \<and> (\<forall>l. \<not> Write ch mm rs p l)"
  by (auto simp: MemReturn_def dest!: WriteResult [temp_use] ReadResult [temp_use])

lemma RWRNext_enabled: "\<turnstile> (rs!p = #NotAResult) \<and> (\<forall>l. MemInv mm l)
         \<and> Enabled (Read ch mm rs p \<or> (\<exists>l. Write ch mm rs p l))
         \<longrightarrow> Enabled (<RNext ch mm rs p>_(rtrner ch ! p, rs!p))"
  by (force simp: RNext_def angle_def elim!: enabled_mono2
    dest: ReadResult [temp_use] WriteResult [temp_use])


(* Combine previous lemmas: the memory can make a visible step if there is an
   outstanding call for which no result has been produced.
*)
lemma RNext_enabled: "\<And>p. \<forall>l. basevars (mm!l, rtrner ch!p, rs!p) \<Longrightarrow>
      \<turnstile> (rs!p = #NotAResult) \<and> Calling ch p \<and> (\<forall>l. MemInv mm l)
         \<longrightarrow> Enabled (<RNext ch mm rs p>_(rtrner ch ! p, rs!p))"
  apply (auto simp: enabled_disj [try_rewrite] intro!: RWRNext_enabled [temp_use])
  apply (case_tac "arg (ch w p)")
   apply (tactic \<open>action_simp_tac (@{context} addsimps [@{thm Read_def},
     temp_rewrite @{context} @{thm enabled_ex}]) [@{thm ReadInner_enabled}, exI] [] 1\<close>)
   apply (force dest: base_pair [temp_use])
  apply (erule contrapos_np)
  apply (tactic \<open>action_simp_tac (@{context} addsimps [@{thm Write_def},
    temp_rewrite @{context} @{thm enabled_ex}])
    [@{thm WriteInner_enabled}, exI] [] 1\<close>)
  done

end
