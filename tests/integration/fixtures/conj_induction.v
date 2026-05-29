From Stdlib Require Import Arith.

(* Conjunction proved by simultaneous induction.
   IH carries both conjuncts: IHn : n + 0 = n /\ 0 + n = n.
   Proof strategy:
     induction n.
     - split. reflexivity. reflexivity.       (* base: both trivial *)
     - destruct IHn as [IH1 IH2]. split.
       + simpl. rewrite IH1. reflexivity.     (* n + 0 = n step *)
       + simpl. reflexivity.                  (* 0 + S n = S n step *)
*)
Lemma conj_induction : forall n : nat, (n + 0 = n) /\ (0 + n = n).
Proof.
Admitted.
