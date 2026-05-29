From Stdlib Require Import Arith.

(* Fixture for induction-inside-bullet tests.
   Goal: (forall n, n + 0 = n) /\ (forall n, 0 + n = n)
   Proof strategy:
     split.
     - intro n. induction n.
       + simpl. reflexivity.         (* base *)
       + simpl. rewrite IHn. reflexivity.  (* step *)
     - intro n. reflexivity.         (* bullet 2: trivial by simpl *)
*)
Lemma induction_in_bullet : (forall n : nat, n + 0 = n) /\ (forall n : nat, 0 + n = n).
Proof.
Admitted.


