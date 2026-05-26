(** Example Coq file for testing mcp-coq-lsp *)

Require Import Nat.

(** A simple theorem about natural number equality *)
Lemma nat_eq_refl : forall n : nat, n = n.
Proof.
  intros.
  reflexivity.
Qed.

(** A theorem using addition *)
Lemma add_zero : forall n : nat, n + 0 = n.
Proof.
  (* Try: intros. *)
  (* Try: induction n. *)
Admitted.
