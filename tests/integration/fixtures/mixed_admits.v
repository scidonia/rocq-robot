From Stdlib Require Import Arith.

(** Fixture for mixed-goal admit_hash tests.
    Uses only Prop goals (petanque cannot query Set/Type goals).
    Goal types: True  and  True -> True  (two distinct Prop goals). *)

(** Four goals: True /\ (True -> True) /\ True /\ (True -> True).
    Two True goals (same hash) and two (True -> True) goals (same hash). *)
Lemma mixed_four : True /\ (True -> True) /\ True /\ (True -> True).
Proof.
  split.
  - admit.
  - split.
    + admit.
    + split.
      * admit.
      * admit.
Admitted.

(** Same shape, first True already solved.
    Remaining admits: (True -> True), True, (True -> True). *)
Lemma mixed_partial : True /\ (True -> True) /\ True /\ (True -> True).
Proof.
  split.
  - exact I.
  - split.
    + admit.
    + split.
      * admit.
      * admit.
Admitted.

(** All same goal — all 4 admits share one hash. *)
Lemma all_true : True /\ True /\ True /\ True.
Proof.
  split.
  - admit.
  - split.
    + admit.
    + split.
      * admit.
      * admit.
Admitted.
