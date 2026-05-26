Require Import Nat List.
Import ListNotations.

Lemma leb_le : forall n m, (n <=? m) = true -> n <= m.
Proof.
  induction n; intros m H; destruct m; simpl in H.
  - apply le_n.
  - apply le_0_n.
  - easy.
  - apply le_n_S. apply IHn. exact H.
Qed.

Lemma leb_gt : forall n m, (n <=? m) = false -> m < n.
Proof.
  induction n; intros m H; destruct m; simpl in H.
  - easy.
  - easy.
  - apply Lt.lt_0_sn.
  - apply Lt.lt_n_S. apply IHn. exact H.
Qed.

Fixpoint insert (n : nat) (l : list nat) : list nat :=
  match l with
  | [] => [n]
  | h :: t => if n <=? h then n :: h :: t else h :: insert n t
  end.

Fixpoint insertion_sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (insertion_sort t)
  end.

Inductive sorted : list nat -> Prop :=
| sorted_nil : sorted []
| sorted_single : forall x, sorted [x]
| sorted_cons : forall x y l, x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Lemma insert_sorted : forall (n : nat) (l : list nat),
  sorted l -> sorted (insert n l).
Proof.
  intros n l Hs. induction l as [| h t IH].
  - simpl. apply sorted_single.
  - inversion Hs; subst; clear Hs; simpl; destruct (n <=? h) eqn:E.
    + apply sorted_cons. * apply leb_le in E. exact E. * apply sorted_single.
    + apply sorted_cons. * apply leb_gt in E. apply Coq.Arith.PeanoNat.Nat.lt_le_incl in E. exact E. * apply sorted_single.
    + apply sorted_cons. * apply leb_le in E. exact E. * apply H2.
    + apply sorted_cons. * apply leb_gt in E. apply Coq.Arith.PeanoNat.Nat.lt_le_incl in E. exact E. * apply IH. apply H2.
Qed.

Lemma insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  (* *)
Admitted.
