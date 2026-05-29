From Stdlib Require Import Arith.

(* Fixture with a deliberate type error for check_range testing *)
Lemma bad_proof : True.
Proof.
  exact 42.
Qed.
