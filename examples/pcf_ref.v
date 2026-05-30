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


Lemma extends_refl : forall S, extends S S.
Proof.
intro S; exists []; symmetry; apply app_nil_r.
Qed.


Lemma nth_error_app_left : forall (A : Type) (l1 l2 : list A) n x, nth_error l1 n = Some x -> nth_error (l1 ++ l2) n = Some x.
Proof.
intros A l1 l2 n x H. rewrite nth_error_app1; [exact H | apply nth_error_Some; congruence].
Qed.


Lemma has_type_extends : forall G S t T S', has_type G S t T -> extends S' S -> has_type G S' t T.
Proof.
intros G S t T S' Hty Hext. induction Hty; try (econstructor; eauto; fail).
destruct Hext as [S2 HS']. subst S'. apply T_Loc. apply nth_error_app_left. exact H.
Qed.


Lemma shift_preserves_typing : forall G S t T, has_type G S t T -> forall d U, has_type (firstn d G ++ U :: skipn d G) S (shift_at d t) T.
Proof.
intros G S t T Hty. induction Hty; intros d U0; simpl.
- (* Var *) destruct (Nat.ltb_spec x d).
  + apply T_Var. rewrite nth_error_app1. { rewrite nth_error_firstn. destruct (Nat.ltb_spec x d); [exact H | lia]. } { rewrite firstn_length. apply nth_error_Some in H. lia. }.
  + apply T_Var. rewrite nth_error_app2. { simpl. rewrite firstn_length. assert (Hlen : x < length G) by (apply nth_error_Some; congruence). replace (x + 1 - Nat.min d (length G)) with (S (x - d)) by lia. simpl. rewrite nth_error_skipn. replace (d + (x - d)) with x by lia. exact H. } { rewrite firstn_length. apply nth_error_Some in H. lia. }.
- constructor.
- constructor.
- constructor; auto.
- constructor; auto.
- constructor; auto.
- constructor; auto.
- apply T_Lam. exact (IHHty (Datatypes.S d) U0).
- econstructor; eauto.
- apply T_Fix. exact (IHHty (Datatypes.S d) U0).
- constructor; auto.
- constructor; auto.
- econstructor; eauto.
- apply T_Loc. exact H.
Qed.

Lemma subst_preserves_typing : forall G S t T, has_type G S t T -> forall G' U s, G = G' ++ [U] -> has_type G' S s U -> has_type G' S (subst (length G') s t) T.
Proof.
intros G S t T Hty. induction Hty; intros G' U0 s0 HG Hs; subst G; simpl.
- (* Var *) destruct (Nat.eqb_spec x (length G')).
  + subst x. rewrite nth_error_app2 in H by lia. replace (length G' - length G') with 0 in H by lia. simpl in H. injection H; intros; subst. exact Hs.
  + apply T_Var. assert (x < length G'). { apply nth_error_Some. assert (x < length (G' ++ [U0])) by (apply nth_error_Some; congruence). rewrite app_length in *; simpl in *; lia. } rewrite nth_error_app1 in H by lia. exact H.
- constructor.
- constructor.
- constructor; eapply IHHty; eauto.
- constructor; eapply IHHty; eauto.
- constructor; eapply IHHty; eauto.
- constructor; [eapply IHHty1 | eapply IHHty2 | eapply IHHty3]; eauto.
- apply T_Lam. eapply IHHty. { rewrite app_comm_cons. reflexivity. } { apply (shift_preserves_typing _ _ _ _ Hs 0). }
- econstructor; [eapply IHHty1 | eapply IHHty2]; eauto.
- apply T_Fix. eapply IHHty. { rewrite app_comm_cons. reflexivity. } { apply (shift_preserves_typing _ _ _ _ Hs 0). }
- constructor; eapply IHHty; eauto.
- constructor; eapply IHHty; eauto.
- econstructor; [eapply IHHty1 | eapply IHHty2]; eauto.
- apply T_Loc. exact H.
Qed.


Lemma heap_lookup_has_type : forall mu S l v T, heap_ok mu S -> heap_lookup l mu = Some v -> nth_error S l = Some T -> has_type [] S v T.
Proof.
intros mu S l v T Hok. revert l v T. induction Hok; intros l0 v0 T0 Hlook Hnth.
- simpl in Hlook. discriminate.
- simpl in Hlook. destruct (Nat.eqb_spec l0 l).
  + subst l0. injection Hlook; intros; subst. rewrite Hnth in H0. injection H0; intros; subst. exact H.
  + eapply IHHok; eassumption.
Qed.


Lemma heap_ok_update : forall mu S l v T, heap_ok mu S -> has_type [] S v T -> nth_error S l = Some T -> heap_ok (heap_update l v mu) S.
Proof.
intros mu S l v T Hok. revert l v T. induction Hok; intros l0 v0 T0 Hty Hnth; simpl.
- constructor.
- destruct (Nat.eqb_spec l0 l).
  + subst. econstructor; eassumption.
  + econstructor; eauto.
Qed.


Lemma heap_ok_extends : forall mu S S', heap_ok mu S -> extends S' S -> heap_ok mu S'.
Proof.
intros mu S S' Hok Hext. induction Hok.
- constructor.
- econstructor.
  + exact IHHok.
  + eapply has_type_extends; eassumption.
  + destruct Hext as [S2 HS']. subst S'. apply nth_error_app_left. exact H0.
Qed.

Theorem preservation :
  forall t mu t' mu' T S,
    has_type [] S t T ->
    step t mu t' mu' ->
    heap_ok mu S ->
    length mu >= length S ->
    exists S',
      extends S' S /\
      heap_ok mu' S' /\
      has_type [] S' t' T.
Proof.
intros t mu t' mu' T S Hty Hstep. revert T S Hty. induction Hstep; intros T0 S0 Hty Hok Hlen; inversion Hty; subst.
- (* S_Succ *) destruct (IHHstep _ _ H2 Hok Hlen) as [S' [Hext [Hok' Hty']]]. exists S'. repeat split; auto. constructor; auto.
- (* S_PredZero *) exists S0; repeat split; auto using extends_refl; constructor.
- (* S_PredSucc *) exists S0; repeat split; auto using extends_refl; constructor.
- (* S_Pred *) destruct (IHHstep _ _ H2 Hok Hlen) as [S' [Hext [Hok' Hty']]]. exists S'. repeat split; auto. constructor; auto.
- (* S_IsZeroZero *) exists S0; repeat split; auto using extends_refl; constructor.
- (* S_IsZeroSucc *) exists S0; repeat split; auto using extends_refl; constructor.
- (* S_IsZero *) destruct (IHHstep _ _ H2 Hok Hlen) as [S' [Hext [Hok' Hty']]]. exists S'. repeat split; auto. constructor; auto.
- (* S_IfTrue *) exists S0; repeat split; auto using extends_refl.
- (* S_IfFalse *) exists S0; repeat split; auto using extends_refl.
- (* S_If *) destruct (IHHstep _ _ H4 Hok Hlen) as [S' [Hext [Hok' Hty']]]. exists S'. repeat split; auto. apply T_If; auto; eapply has_type_extends; eauto.
- (* S_App1 *) destruct (IHHstep _ _ H3 Hok Hlen) as [S' [Hext [Hok' Hty']]]. exists S'. repeat split; auto. econstructor; eauto. eapply has_type_extends; eauto.
- (* S_App2 *) destruct (IHHstep _ _ H6 Hok Hlen) as [S' [Hext [Hok' Hty']]]. exists S'. repeat split; auto. econstructor; [eapply has_type_extends; eauto | auto].
- (* S_AppAbs *) exists S0; repeat split; auto using extends_refl. inversion H4; subst. eapply subst_preserves_typing; eauto. reflexivity.
- (* S_Fix *) exists S0; repeat split; auto using extends_refl. eapply subst_preserves_typing; eauto. apply T_Fix. exact H2.
- (* S_Ref cong *) destruct (IHHstep _ _ H2 Hok Hlen) as [S' [Hext [Hok' Hty']]]. exists S'. repeat split; auto. constructor; auto.
- (* S_RefV *) exists (S0 ++ repeat TyNat (length mu - length S0) ++ [T]).
  assert (Hext: extends (S0 ++ repeat TyNat (length mu - length S0) ++ [T]) S0) by (exists (repeat TyNat (length mu - length S0) ++ [T]); reflexivity).
  assert (Hnth: nth_error (S0 ++ repeat TyNat (length mu - length S0) ++ [T]) (length mu) = Some T).
  { rewrite app_assoc. rewrite nth_error_app2 by (rewrite app_length, repeat_length; lia). rewrite app_length, repeat_length. replace (length mu - (length S0 + (length mu - length S0))) with 0 by lia. reflexivity. }
  repeat split.
  + exact Hext.
  + econstructor; [eapply heap_ok_extends; eauto | eapply has_type_extends; eauto | exact Hnth].
  + apply T_Loc. exact Hnth.
- (* S_Deref cong *) destruct (IHHstep _ _ H2 Hok Hlen) as [S' [Hext [Hok' Hty']]]. exists S'. repeat split; auto. constructor; auto.
- (* S_DerefLoc *) exists S0; repeat split; auto using extends_refl. inversion H3; subst. eapply heap_lookup_has_type; eassumption.
- (* S_Assign1 *) destruct (IHHstep _ _ H3 Hok Hlen) as [S' [Hext [Hok' Hty']]]. exists S'. repeat split; auto. econstructor; eauto. eapply has_type_extends; eauto.
- (* S_Assign2 *) destruct (IHHstep _ _ H5 Hok Hlen) as [S' [Hext [Hok' Hty']]]. exists S'. repeat split; auto. econstructor; [eapply has_type_extends; eauto | auto].
- (* S_AssignV *) exists S0; repeat split; auto using extends_refl. { inversion H4; subst. eapply heap_ok_update; eassumption. } { constructor. }.
Qed.
