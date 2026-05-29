From Stdlib Require Import Arith.

Lemma only_nat : forall n : nat, n = n.
Proof.
intro n.
exact true.
Admitted.
