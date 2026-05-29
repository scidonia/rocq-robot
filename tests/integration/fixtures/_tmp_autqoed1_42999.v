From Stdlib Require Import Arith.

(* Proof with multiple focused goals at Admitted. — no tactic-level admits.
   After "split.", there are 2 focused goals covered by a single Admitted. *)
Lemma multi_goal : True /\ True.
Proof.
  split.
Admitted.

(* Unstarted proof — 1 goal at Admitted. *)
Lemma single_goal : True.
Proof.
Admitted.
