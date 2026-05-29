From Stdlib Require Import Arith.

(** Bullet already has tactics before admit. *)
Lemma partial_bullet : True /\ True.
Proof.
  split.
  - intros. admit.
  - exact I.
  exact I.
Admitted.
