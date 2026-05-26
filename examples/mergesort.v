Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.

Fixpoint merge (l1 l2 : list nat) : list nat :=
  match l1, l2 with
  | [], l2 => l2
  | l1, [] => l1
  | x :: xs, y :: ys =>
    if x <=? y then x :: merge xs (y :: ys)
    else y :: merge (x :: xs) ys
  end.

Inductive sorted : list nat -> Prop :=
  | sorted_nil : sorted []
  | sorted_singleton x : sorted [x]
  | sorted_cons x y l :
      x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Lemma sorted_cons_inv : forall x l,
  sorted (x :: l) -> sorted l.
Proof.
  intros x l H; inversion H; subst; auto.
Qed.

Lemma merge_sorted : forall l1 l2,
  sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
  induction l1; intros l2 H1 H2; auto.
  destruct l2; auto.
  simpl.
  destruct (a <=? n) eqn:Le.
  - apply sorted_cons.
    + apply (Nat.leb_spec a n); auto.
    + apply IHl1; auto.
      inversion H1; subst; auto.
  - apply sorted_cons.
    + apply (Nat.leb_spec n a).
      apply Nat.leb_gt in Le; omega.
    + apply IHl1; auto.
      inversion H2; subst; auto.
Qed.

Fixpoint split (l : list nat) : list nat * list nat :=
  match l with
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest =>
    let (l1, l2) := split rest in
    (x :: l1, y :: l2)
  end.

Lemma split_length : forall l,
  length (fst (split l)) + length (snd (split l)) = length l.
Proof.
  induction l; auto.
  destruct l; auto.
  simpl; rewrite IHl; auto.
Qed.

Fixpoint mergesort (l : list nat) : list nat :=
  match l with
  | [] => []
  | [x] => [x]
  | _ :: _ :: _ =>
    let (l1, l2) := split l in
    merge (mergesort l1) (mergesort l2)
  end.

Lemma split_shorter_l : forall l,
  length (fst (split l)) < length l \/ length l <= 1.
Proof.
  destruct l as [|x [|y l']]; auto.
  right; omega.
  left; simpl.
  destruct (split l') as (a, b); simpl.
  rewrite <- plus_n_Sm.
  apply lt_n_S.
  rewrite <- (split_length l') at 1.
  simpl; omega.
Qed.

Lemma split_shorter_r : forall l,
  length (snd (split l)) < length l \/ length l <= 1.
Proof.
  destruct l as [|x [|y l']]; auto.
  right; omega.
  left; simpl.
  destruct (split l') as (a, b); simpl.
  rewrite <- plus_n_Sm.
  apply lt_n_S.
  rewrite <- (split_length l') at 1.
  simpl; omega.
Qed.

Lemma mergesort_sorted : forall l, sorted (mergesort l).
Proof.
  intro l; apply (lt_wf_ind (length l) (fun n l' => forall Hlen : length l' = n, sorted (mergesort l')));
  clear l; intros n l' IH Hlen.
  destruct l' as [|x [|y l'']]; simpl; auto.
  destruct (split (x :: y :: l'')) as (a, b) eqn:Split.
  simpl.
  apply merge_sorted.
  - apply IH (length (fst (split (x :: y :: l'')))).
    + destruct (split_shorter_l (x :: y :: l'')) as [H | H']; auto.
      rewrite Hlen; exact H.
    + reflexivity.
  - apply IH (length (snd (split (x :: y :: l'')))).
    + destruct (split_shorter_r (x :: y :: l'')) as [H | H']; auto.
      rewrite Hlen; exact H.
    + reflexivity.
Qed.
