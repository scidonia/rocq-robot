From Stdlib Require Import Arith.

Lemma nested_conj : (True /\ True) /\ (True /\ True).
Proof.
  split.
  - split; exact I.
  - split; exact I.
Qed.
