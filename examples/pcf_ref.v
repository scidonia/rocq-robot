From Stdlib Require Import Arith List Lia.
Import ListNotations.

(** * PCF + References: Type Preservation *)

Inductive ty : Type :=
  | TyNat | TyBool | TyArrow : ty -> ty -> ty | TyRef : ty -> ty.

Inductive tm : Type :=
  | Var : nat -> tm | Num : nat -> tm | BOOL : bool -> tm
  | Succ : tm -> tm | Pred : tm -> tm | IsZero : tm -> tm
  | If : tm -> tm -> tm -> tm
  | Lam : ty -> tm -> tm | App : tm -> tm -> tm | Fix : tm -> tm
  | Ref : tm -> tm | Deref : tm -> tm | Assign : tm -> tm -> tm | Loc : nat -> tm.

Definition ctx := list ty.
Definition store_ty := list ty.

Inductive has_type : ctx -> store_ty -> tm -> ty -> Prop :=
  | T_Var : forall G S x T, nth_error G x = Some T -> has_type G S (Var x) T
  | T_Num : forall G S n, has_type G S (Num n) TyNat
  | T_Bool : forall G S b, has_type G S (BOOL b) TyBool
  | T_Succ : forall G S t, has_type G S t TyNat -> has_type G S (Succ t) TyNat
  | T_Pred : forall G S t, has_type G S t TyNat -> has_type G S (Pred t) TyNat
  | T_IsZero : forall G S t, has_type G S t TyNat -> has_type G S (IsZero t) TyBool
  | T_If : forall G S t1 t2 t3 T, has_type G S t1 TyBool -> has_type G S t2 T -> has_type G S t3 T -> has_type G S (If t1 t2 t3) T
  | T_Lam : forall G S T1 T2 t, has_type (T1 :: G) S t T2 -> has_type G S (Lam T1 t) (TyArrow T1 T2)
  | T_App : forall G S t1 t2 T1 T2, has_type G S t1 (TyArrow T1 T2) -> has_type G S t2 T1 -> has_type G S (App t1 t2) T2
  | T_Fix : forall G S t T, has_type (T :: G) S t T -> has_type G S (Fix t) T
  | T_Ref : forall G S t T, has_type G S t T -> has_type G S (Ref t) (TyRef T)
  | T_Deref : forall G S t T, has_type G S t (TyRef T) -> has_type G S (Deref t) T
  | T_Assign : forall G S t1 t2 T, has_type G S t1 (TyRef T) -> has_type G S t2 T -> has_type G S (Assign t1 t2) TyNat
  | T_Loc : forall G S l T, nth_error S l = Some T -> has_type G S (Loc l) (TyRef T).

Inductive value : tm -> Prop :=
  | V_Num : forall n, value (Num n)
  | V_Bool : forall b, value (BOOL b)
  | V_Lam : forall T t, value (Lam T t)
  | V_Loc : forall l, value (Loc l).

Fixpoint shift_at (d : nat) (t : tm) : tm :=
  match t with
  | Var x => if x <? d then Var x else Var (x + 1)
  | Num n => Num n | BOOL b => BOOL b
  | Succ t1 => Succ (shift_at d t1) | Pred t1 => Pred (shift_at d t1)
  | IsZero t1 => IsZero (shift_at d t1)
  | If t1 t2 t3 => If (shift_at d t1) (shift_at d t2) (shift_at d t3)
  | Lam T t1 => Lam T (shift_at (S d) t1)
  | App t1 t2 => App (shift_at d t1) (shift_at d t2)
  | Fix t1 => Fix (shift_at (S d) t1)
  | Ref t1 => Ref (shift_at d t1) | Deref t1 => Deref (shift_at d t1)
  | Assign t1 t2 => Assign (shift_at d t1) (shift_at d t2)
  | Loc l => Loc l
  end.

Definition shift (t : tm) : tm := shift_at 0 t.

Fixpoint subst (j : nat) (s t : tm) : tm :=
  match t with
  | Var x => if Nat.eqb x j then s else Var x
  | Num n => Num n | BOOL b => BOOL b
  | Succ t1 => Succ (subst j s t1) | Pred t1 => Pred (subst j s t1)
  | IsZero t1 => IsZero (subst j s t1)
  | If t1 t2 t3 => If (subst j s t1) (subst j s t2) (subst j s t3)
  | Lam T t1 => Lam T (subst (S j) (shift s) t1)
  | App t1 t2 => App (subst j s t1) (subst j s t2)
  | Fix t1 => Fix (subst (S j) (shift s) t1)
  | Ref t1 => Ref (subst j s t1) | Deref t1 => Deref (subst j s t1)
  | Assign t1 t2 => Assign (subst j s t1) (subst j s t2)
  | Loc l => Loc l
  end.

Definition heap := list (nat * tm).

Fixpoint heap_lookup (l : nat) (mu : heap) : option tm :=
  match mu with
  | [] => None
  | (l', v) :: mu' => if Nat.eqb l l' then Some v else heap_lookup l mu'
  end.

Fixpoint heap_update (l : nat) (v : tm) (mu : heap) : heap :=
  match mu with
  | [] => []
  | (l', v') :: mu' => if Nat.eqb l l' then (l, v) :: mu'
                        else (l', v') :: heap_update l v mu'
  end.

Inductive heap_ok : heap -> store_ty -> Prop :=
  | heap_empty : forall S, heap_ok [] S
  | heap_cons : forall l v mu S T, heap_ok mu S -> has_type [] S v T -> nth_error S l = Some T -> heap_ok ((l, v) :: mu) S.

Inductive step : tm -> heap -> tm -> heap -> Prop :=
  | S_Succ : forall t mu t' mu', step t mu t' mu' -> step (Succ t) mu (Succ t') mu'
  | S_PredZero : forall mu, step (Pred (Num 0)) mu (Num 0) mu
  | S_PredSucc : forall n mu, step (Pred (Num (S n))) mu (Num n) mu
  | S_Pred : forall t mu t' mu', step t mu t' mu' -> step (Pred t) mu (Pred t') mu'
  | S_IsZeroZero : forall mu, step (IsZero (Num 0)) mu (BOOL true) mu
  | S_IsZeroSucc : forall n mu, step (IsZero (Num (S n))) mu (BOOL false) mu
  | S_IsZero : forall t mu t' mu', step t mu t' mu' -> step (IsZero t) mu (IsZero t') mu'
  | S_IfTrue : forall t1 t2 mu, step (If (BOOL true) t1 t2) mu t1 mu
  | S_IfFalse : forall t1 t2 mu, step (If (BOOL false) t1 t2) mu t2 mu
  | S_If : forall t1 mu t1' mu' t2 t3, step t1 mu t1' mu' -> step (If t1 t2 t3) mu (If t1' t2 t3) mu'
  | S_App1 : forall t1 mu t1' mu' t2, step t1 mu t1' mu' -> step (App t1 t2) mu (App t1' t2) mu'
  | S_App2 : forall v1 t2 mu t2' mu', value v1 -> step t2 mu t2' mu' -> step (App v1 t2) mu (App v1 t2') mu'
  | S_AppAbs : forall T t1 v2 mu, value v2 -> step (App (Lam T t1) v2) mu (subst 0 v2 t1) mu
  | S_Fix : forall t mu, step (Fix t) mu (subst 0 (Fix t) t) mu
  | S_Ref : forall t mu t' mu', step t mu t' mu' -> step (Ref t) mu (Ref t') mu'
  | S_RefV : forall v mu, value v -> step (Ref v) mu (Loc (length mu)) ((length mu, v) :: mu)
  | S_Deref : forall t mu t' mu', step t mu t' mu' -> step (Deref t) mu (Deref t') mu'
  | S_DerefLoc : forall l mu v, heap_lookup l mu = Some v -> step (Deref (Loc l)) mu v mu
  | S_Assign1 : forall t1 mu t1' mu' t2, step t1 mu t1' mu' -> step (Assign t1 t2) mu (Assign t1' t2) mu'
  | S_Assign2 : forall l t2 mu t2' mu', step t2 mu t2' mu' -> step (Assign (Loc l) t2) mu (Assign (Loc l) t2') mu'
  | S_AssignV : forall l v mu, value v -> step (Assign (Loc l) v) mu (Num 0) (heap_update l v mu).

Definition extends (S' S : store_ty) : Prop := exists S2, S' = S ++ S2.

(** * Type Preservation *)




Lemma shift_at_typing : forall G1 G2 S t T T', has_type (G1 ++ G2) S t T -> has_type (G1 ++ T' :: G2) S (shift_at (length G1) t) T.
Proof.
intros G1 G2 S t T T' Hty.
  remember (G1 ++ G2) as Gamma.
  generalize dependent G2. generalize dependent G1.
  induction Hty; intros G1' G2' Heq; subst; simpl.
  - (* T_Var *) destruct (Nat.ltb_spec x (length G1')).
    + apply T_Var. rewrite nth_error_app1 in H by auto. rewrite nth_error_app1 by auto. exact H.
    + apply T_Var. replace (x + 1) with (S x) by lia. rewrite nth_error_app2 in H by lia. rewrite nth_error_app2 by lia. simpl. rewrite Nat.sub_succ_l by lia. exact H.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ; eauto.
  - apply T_Pred; eauto.
  - apply T_IsZero; eauto.
  - apply T_If; eauto.
  - apply T_Lam. replace (T1 :: G1' ++ T' :: G2') with ((T1 :: G1') ++ T' :: G2') by reflexivity. apply (IHHty (T1 :: G1') G2'). simpl. rewrite Heq. reflexivity.
  - eapply T_App; eauto.
  - apply T_Fix. replace (T0 :: G1' ++ T' :: G2') with ((T0 :: G1') ++ T' :: G2') by reflexivity. apply (IHHty (T0 :: G1') G2'). simpl. rewrite Heq. reflexivity.
  - apply T_Ref; eauto.
  - apply T_Deref; eauto.
  - eapply T_Assign; eauto.
  - apply T_Loc. exact H.
Qed.

Lemma shift_typing : forall T' G S t T, has_type G S t T -> has_type (T' :: G) S (shift t) T.
Proof.
intros. apply (shift_at_typing [] G S t T T'). simpl. exact H.
Qed.


Lemma substitution_preserves_typing : forall G S t T U s, has_type (G ++ [U]) S t T -> has_type G S s U -> has_type G S (subst (length G) s t) T.
Proof.
intros G S t T U s Hty Hs.
  remember (G ++ [U]) as Gamma.
  generalize dependent G.
  induction Hty; intros G' HeqG Hs'; subst; simpl.
  - rename H into Hnth. destruct (Nat.eqb_spec x (length G')).
    + subst. rewrite Nat.eqb_refl. assert (nth_error (G' ++ [U]) (length G') = Some U) by (rewrite nth_error_app2 by lia; simpl; rewrite Nat.sub_diag; reflexivity). rewrite Hnth in H. injection H; intros; subst. exact Hs'.
    + rewrite <- Nat.eqb_neq in n. rewrite Nat.eqb_sym in n. rewrite n. apply T_Var. exact Hnth.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ; eauto.
  - apply T_Pred; eauto.
  - apply T_IsZero; eauto.
  - apply T_If; eauto.
  - apply T_Lam. replace (T1 :: G' ++ [U]) with ((T1 :: G') ++ [U]) in Hty by reflexivity. apply (IHHty (T1 :: G')); auto. simpl. apply shift_typing. exact Hs'.
  - eapply T_App; eauto.
  - apply T_Fix. replace (T0 :: G' ++ [U]) with ((T0 :: G') ++ [U]) in Hty by reflexivity. apply (IHHty (T0 :: G')); auto. simpl. apply shift_typing. exact Hs'.
  - apply T_Ref; eauto.
  - apply T_Deref; eauto.
  - eapply T_Assign; eauto.
  - apply T_Loc. exact H.
Qed.


Lemma has_type_store_weakening : forall G S S2 t T, has_type G S t T -> has_type G (S ++ S2) t T.
Proof.
intros G S S2 t T Hty. induction Hty; eauto using has_type. apply T_Loc. rewrite nth_error_app1; auto. apply nth_error_Some. rewrite H. discriminate.
Qed.



Lemma heap_ok_store_weakening : forall mu S S2, heap_ok mu S -> heap_ok mu (S ++ S2).
Proof.
  intros mu S S2 Hok. induction Hok.
  - constructor.
  - apply heap_cons with (T := T); auto.
    + apply IHHok.
    + apply has_type_store_weakening with (S := S); auto.
    + apply nth_error_Some in H0. rewrite nth_error_app1; auto.
Qed.

Lemma heap_ok_length : forall mu S, heap_ok mu S -> length mu = length S.
Proof.
  intros mu S Hok. induction Hok; simpl; auto.
  apply nth_error_Some in H0. rewrite <- IHHok. lia.
Qed.

Theorem preservation :
  forall t mu t' mu' T S,
    has_type [] S t T ->
    step t mu t' mu' ->
    heap_ok mu S ->
    exists S',
      extends S' S /\
      heap_ok mu' S' /\
      has_type [] S' t' T.
Proof.
intros t mu t' mu' T S Hty Hstep Hok.
  revert T S Hty Hok.
  induction Hstep; intros T0 S Hty Hok.
  - (* S_Succ *) inversion Hty; subst. destruct (IHHstep TyNat S H2 Hok) as [S' [? [? ?]]]. exists S'; eauto using T_Succ.
  - (* S_PredZero *) inversion Hty; subst. exists S; repeat split; eauto using T_Num. unfold extends; exists []; symmetry; apply app_nil_r.
  - (* S_PredSucc *) inversion Hty; subst. exists S; repeat split; eauto using T_Num. unfold extends; exists []; symmetry; apply app_nil_r.
  - (* S_Pred *) inversion Hty; subst. destruct (IHHstep TyNat S H2 Hok) as [S' [? [? ?]]]. exists S'; eauto using T_Pred.
  - (* S_IsZeroZero *) inversion Hty; subst. exists S; repeat split; eauto using T_Bool. unfold extends; exists []; symmetry; apply app_nil_r.
  - (* S_IsZeroSucc *) inversion Hty; subst. exists S; repeat split; eauto using T_Bool. unfold extends; exists []; symmetry; apply app_nil_r.
  - (* S_IsZero *) inversion Hty; subst. destruct (IHHstep TyNat S H2 Hok) as [S' [? [? ?]]]. exists S'; eauto using T_IsZero.
  - (* S_IfTrue *) inversion Hty; subst. exists S; repeat split; eauto. unfold extends; exists []; symmetry; apply app_nil_r.
  - (* S_IfFalse *) inversion Hty; subst. exists S; repeat split; eauto. unfold extends; exists []; symmetry; apply app_nil_r.
  - (* S_If *) inversion Hty; subst. destruct (IHHstep TyBool S H3 Hok) as [S' [? [? ?]]]. exists S'; eauto using T_If.
  - (* S_App1 *) inversion Hty; subst. destruct (IHHstep (TyArrow T1 T0) S H3 Hok) as [S' [? [? ?]]]. exists S'; eauto using T_App.
  - (* S_App2 *) inversion Hty; subst. destruct (IHHstep T1 S H5 Hok) as [S' [? [? ?]]]. exists S'; eauto using T_App.
  - (* S_AppAbs *) inversion Hty; subst. inversion H4; subst. exists S; split; [unfold extends; exists []; symmetry; apply app_nil_r|]. split; [exact Hok|]. eapply substitution_preserves_typing with (G := []); simpl; eauto.
  - (* S_Fix *) inversion Hty; subst. exists S; split; [unfold extends; exists []; symmetry; apply app_nil_r|]. split; [exact Hok|]. eapply substitution_preserves_typing with (G := []); simpl; eauto.
  - (* S_Ref *) inversion Hty; subst. destruct (IHHstep T0 S H2 Hok) as [S' [? [? ?]]]. exists S'; eauto using T_Ref.
  - (* S_RefV *) inversion Hty; subst. exists (S ++ [T]). split; [unfold extends; exists [T]; reflexivity|]. split. { apply heap_cons with (T := T). apply heap_ok_store_weakening; auto. apply has_type_store_weakening; auto. rewrite nth_error_app2 by (rewrite heap_ok_length with (S := S); auto; lia). rewrite heap_ok_length with (S := S); auto. rewrite Nat.sub_diag; reflexivity. } { apply T_Loc. rewrite nth_error_app2 by (rewrite heap_ok_length with (S := S); auto; lia). rewrite heap_ok_length with (S := S); auto. rewrite Nat.sub_diag; reflexivity. }
  - (* S_Deref *) inversion Hty; subst. destruct (IHHstep (TyRef T0) S H2 Hok) as [S' [? [? ?]]]. exists S'; eauto using T_Deref.
  - (* S_DerefLoc *) inversion Hty; subst. inversion H0; subst. exists S; split; [unfold extends; exists []; symmetry; apply app_nil_r|]. split; [exact Hok|]. induction Hok; simpl in H. discriminate. destruct (Nat.eqb l l0) eqn:Heq. apply Nat.eqb_eq in Heq; subst; rewrite Nat.eqb_refl in H; injection H; intros; subst. rewrite H3 in H1; injection H1; intros; subst. exact H0. apply IHHok; rewrite Heq in H; exact H.
  - (* S_Assign1 *) inversion Hty; subst. destruct (IHHstep (TyRef T1) S H2 Hok) as [S' [? [? ?]]]. exists S'; eauto using T_Assign.
  - (* S_Assign2 *) inversion Hty; subst. destruct (IHHstep T1 S H4 Hok) as [S' [? [? ?]]]. exists S'; eauto using T_Assign.
  - (* S_AssignV *) inversion Hty; subst. inversion H0; subst. exists S; split; [unfold extends; exists []; symmetry; apply app_nil_r|]. split. { induction Hok. constructor. simpl; destruct (Nat.eqb l l0) eqn:Heq. apply Nat.eqb_eq in Heq; subst; apply heap_cons with (T := T1); auto; rewrite H2 in H3; injection H3; intros; subst; exact H4. apply heap_cons with (T := T); auto. } { apply T_Num. }
Qed.
