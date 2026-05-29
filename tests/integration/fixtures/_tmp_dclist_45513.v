From Stdlib Require Import Arith.

(* (True /\ True) /\ True — three-way conjunction used to test
   admit → split → admit → close workflows with nested bullets *)
Lemma deep_conj : (True /\ True) /\ True.
Proof.
  split.
  - admit.
  - admit.
Admitted.
