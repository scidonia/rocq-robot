From Stdlib Require Import Arith List Lia.
Import ListNotations.

(** Fixture for reproducing auto-Qed failure: rewrite followed by
    { } blocks produces "bullet closed (1 admitted)" instead of
    "done — Qed applied". *)

(** Baseline: no { } block — should auto-Qed *)
Lemma no_curly_baseline : forall (n : nat), n <= n.
Proof.
Admitted.

(** Single { } block after rewrite — triggers the bug *)
Lemma rewrite_curly_single : forall (n : nat), n + 0 = n.
Proof.
Admitted.

(** Two { } blocks after rewrite — also triggers the bug *)
Lemma rewrite_curly_double : forall (l1 l2 : list nat) (n x : nat),
  n < length (firstn (n+1) l1) ->
  nth_error (firstn (n+1) l1 ++ l2) n = Some x ->
  nth_error (firstn (n+1) l1) n = Some x.
Proof.
Admitted.
