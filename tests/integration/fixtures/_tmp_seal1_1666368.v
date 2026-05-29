From Stdlib Require Import Arith.

(** Bullet already has tactics before admit. *)
Lemma partial_bullet : True /\ True.
Proof.
  split.
  - intros. exact I.
  - exact I.
Qed.
