From Stdlib Require Import Arith.

Lemma nested_conj : (True /\ True) /\ (True /\ True).
Proof.
  split.
  - split.
    + admit.
    + admit.
  - admit.
Admitted.
