(*  Title:      HOL/Tools/SMT/cvc5_replay.ML
    Author:     Mathias Fleury, JKU
    Author:     Hanna Lachnitt, Stanford University

Proof parsing and replay for cvc5.
*)

signature CVC5_REPLAY =
sig
  val replay: Proof.context -> SMT_Translate.replay_data -> string list -> thm
end;

structure CVC5_Replay: CVC5_REPLAY =
struct

val replay = Alethe_Replay.replay CVC5_Replay_Methods.method_for

end
