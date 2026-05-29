From Stdlib Require Import Arith List Lia.
Import ListNotations.

(** Basic fixture for integration tests *)
Lemma trivial : True.
Proof.
Admitted.

Lemma conjunction : True /\ True.
Proof.
Admitted.

Lemma with_hyp : forall (n : nat), n = n.
Proof.
Admitted.

Lemma two_goals : True /\ True /\ True.
Proof.
Admitted.

Lemma already_proved : True.
Proof.
  exact I.
Qed.

Lemma has_admits : True /\ True.
Proof.
  split.
  - admit.
  - admit.
Admitted.
