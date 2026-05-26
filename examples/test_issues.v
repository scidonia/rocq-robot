Require Import Arith List Compare_dec.
Import ListNotations.

(** * PCF with References — Template (all Admitted) *)

Inductive ty : Type :=
  | TyNat | TyBool | TyArrow : ty -> ty -> ty | TyRef : ty -> ty.

Inductive tm : Type :=
  | Var : nat -> tm | Num : nat -> tm | BOOL : bool -> tm
  | Succ : tm -> tm | Pred : tm -> tm | IsZero : tm -> tm
  | If : tm -> tm -> tm -> tm
  | Lam : ty -> tm -> tm | App : tm -> tm -> tm | Fix : tm -> tm
  | Ref : tm -> tm | Deref : tm -> tm | Assign : tm -> tm -> tm
  | Loc : nat -> tm.

Definition ctx := list ty.
Definition store_ty := list ty.

Inductive has_type : ctx -> store_ty -> tm -> ty -> Prop :=
  | T_Var : forall G S x T, nth_error G x = Some T -> has_type G S (Var x) T
  | T_Num : forall G S n, has_type G S (Num n) TyNat
  | T_Bool : forall G S b, has_type G S (BOOL b) TyBool
  | T_Succ : forall G S t, has_type G S t TyNat -> has_type G S (Succ t) TyNat
  | T_Pred : forall G S t, has_type G S t TyNat -> has_type G S (Pred t) TyNat
  | T_IsZero : forall G S t, has_type G S t TyNat -> has_type G S (IsZero t) TyBool
  | T_If : forall G S t1 t2 t3 T,
      has_type G S t1 TyBool -> has_type G S t2 T -> has_type G S t3 T -> has_type G S (If t1 t2 t3) T
  | T_Lam : forall G S T1 T2 t,
      has_type (T1 :: G) S t T2 -> has_type G S (Lam T1 t) (TyArrow T1 T2)
  | T_App : forall G S t1 t2 T1 T2,
      has_type G S t1 (TyArrow T1 T2) -> has_type G S t2 T1 -> has_type G S (App t1 t2) T2
  | T_Fix : forall G S t T,
      has_type (T :: G) S t T -> has_type G S (Fix t) T
  | T_Ref : forall G S t T, has_type G S t T -> has_type G S (Ref t) (TyRef T)
  | T_Deref : forall G S t T, has_type G S t (TyRef T) -> has_type G S (Deref t) T
  | T_Assign : forall G S t1 t2 T,
      has_type G S t1 (TyRef T) -> has_type G S t2 T -> has_type G S (Assign t1 t2) TyNat
  | T_Loc : forall G S l T, nth_error S l = Some T -> has_type G S (Loc l) (TyRef T).

Inductive value : tm -> Prop :=
  | V_Num : forall n, value (Num n) | V_Bool : forall b, value (BOOL b)
  | V_Lam : forall T t, value (Lam T t) | V_Loc : forall l, value (Loc l).

Fixpoint subst (j : nat) (s : tm) (t : tm) : tm :=
  match t with
  | Var x => if Nat.eqb x j then s else Var x
  | Num n => Num n | BOOL b => BOOL b
  | Succ t1 => Succ (subst j s t1) | Pred t1 => Pred (subst j s t1)
  | IsZero t1 => IsZero (subst j s t1)
  | If t1 t2 t3 => If (subst j s t1) (subst j s t2) (subst j s t3)
  | Lam T t1 => Lam T (subst (S j) s t1)
  | App t1 t2 => App (subst j s t1) (subst j s t2)
  | Fix t1 => Fix (subst (S j) s t1)
  | Ref t1 => Ref (subst j s t1) | Deref t1 => Deref (subst j s t1)
  | Assign t1 t2 => Assign (subst j s t1) (subst j s t2)
  | Loc l => Loc l
  end.

Definition heap := list (nat * tm).

Fixpoint heap_lookup (l : nat) (mu : heap) : option tm :=
  match mu with | [] => None | (l',v)::mu' => if Nat.eqb l l' then Some v else heap_lookup l mu' end.

Fixpoint heap_update (l : nat) (v : tm) (mu : heap) : heap :=
  match mu with | [] => [] | (l',v')::mu' => if Nat.eqb l l' then (l,v)::mu' else (l',v') :: heap_update l v mu' end.

Inductive heap_ok : heap -> store_ty -> Prop :=
  | heap_empty : forall S, heap_ok [] S
  | heap_cons : forall l v mu S T,
      heap_ok mu S -> has_type [] S v T -> nth_error S l = Some T ->
      heap_ok ((l, v) :: mu) S.

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

(* ---- Helper Lemmas ---- *)

Definition extends (S' S : store_ty) : Prop := exists S2, S' = S ++ S2.
Lemma extends_refl : forall S, extends S S.
Proof.
intro S.
unfold extends.
exists [].
rewrite app_nil_r.
reflexivity.
Qed.

Admitted.


Lemma nth_error_extends : forall S S' l T, extends S' S -> nth_error S l = Some T -> nth_error S' l = Some T.
Proof.
intros S S' l T Hext Hnth.
unfold extends in Hext.
destruct Hext as [S2 Heq].
subst.
rewrite nth_error_app1.
- assumption.
- apply nth_error_Some. rewrite Hnth. discriminate.
Qed.


Lemma weakening_store : forall G S t T, has_type G S t T -> forall S', extends S' S -> has_type G S' t T.
Proof.
intros G S t T Hty.
induction Hty; intros S' Hext.
- constructor. assumption.
- constructor.
- constructor.
- constructor. auto.
- constructor. auto.
- constructor. auto.
- econstructor; eauto.
- constructor. auto.
- econstructor; eauto.
- constructor. auto.
- constructor. auto.
- constructor. auto.
- econstructor; eauto.
- constructor. eapply nth_error_extends; eauto.
Qed.



Lemma substitution_preserves_typing_0 : forall G S t T v U,
  has_type (U :: G) S t T -> has_type [] S v U -> has_type G S (subst 0 v t) T.
Proof.
intros G S t T v U Ht Hv.
generalize dependent G. generalize dependent T.
induction t; intros T G Ht; inversion Ht; subst; simpl.
- destruct n; simpl in *. + injection H2 as H2. subst. assumption. + constructor. assumption.
- constructor.
- constructor.
- constructor. eauto.
- constructor. eauto.
- constructor. eauto.
- econstructor; eauto.
- admit.
- econstructor; eauto.
- admit.
- constructor. eauto.
- constructor. eauto.
- econstructor; eauto.
- constructor. assumption.
Qed.




Lemma heap_ok_locations_bound : forall mu S l v, heap_ok mu S -> In (l, v) mu -> l < length S.
Proof.
Admitted.

Lemma heap_ok_length : forall mu S, heap_ok mu S -> length mu = length S.
Proof.
Admitted.


Lemma heap_lookup_type : forall mu S l v T, heap_ok mu S -> heap_lookup l mu = Some v -> nth_error S l = Some T -> has_type [] S v T.
Proof.
intros mu S l v T Hok Hlookup Hnth.
induction Hok.
- simpl in Hlookup. discriminate.
- simpl in Hlookup. destruct (Nat.eqb l l0) eqn:Heq.
  + injection Hlookup as Hlookup. subst. apply Nat.eqb_eq in Heq. subst. rewrite H0 in Hnth. injection Hnth as Hnth. subst. assumption.
+ eauto.
Qed.



Lemma heap_update_ok : forall mu S l v T, heap_ok mu S -> has_type [] S v T -> nth_error S l = Some T -> heap_ok (heap_update l v mu) S.
Proof.
intros mu S l v T Hok Hv Hnth.
induction Hok.
- simpl. constructor. assumption.
- simpl. destruct (Nat.eqb l l0) eqn:Heq.
  + apply Nat.eqb_eq in Heq. subst. econstructor; eauto. rewrite Hnth in H0. injection H0 as H0. subst. assumption.
+ econstructor; eauto.
Qed.


Theorem preservation : forall t mu t' mu' T S,
  has_type [] S t T -> step t mu t' mu' ->
  heap_ok mu S ->
  exists S', extends S' S /\ heap_ok mu' S' /\ has_type [] S' t' T.
Proof.
intros t mu t' mu' T S Hty Hstep.
generalize dependent T.
generalize dependent S.
induction Hstep.
- intros S T0 Hty Hok. inversion Hty; subst. edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto. exists S'. repeat split; auto. constructor. assumption.
- intros S T0 Hty Hok. inversion Hty; subst. exists S. repeat split; auto. apply extends_refl. constructor.
- intros S T0 Hty Hok. inversion Hty; subst. exists S. repeat split; auto. apply extends_refl. constructor.
- intros S T0 Hty Hok. inversion Hty; subst. edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto. exists S'. repeat split; auto. constructor. assumption.
- intros S T0 Hty Hok. inversion Hty; subst. exists S. repeat split; auto. apply extends_refl. constructor.
- intros S T0 Hty Hok. inversion Hty; subst. exists S. repeat split; auto. apply extends_refl. constructor.
- intros S T0 Hty Hok. inversion Hty; subst. edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto. exists S'. repeat split; auto. constructor. assumption.
- intros S T0 Hty Hok. inversion Hty; subst. exists S. repeat split; auto. apply extends_refl.
- intros S T0 Hty Hok. inversion Hty; subst. exists S. repeat split; auto. apply extends_refl.
- intros S T0 Hty Hok. inversion Hty; subst. edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto. exists S'. repeat split; auto. econstructor; eauto.
  + eapply weakening_store; eauto.
+ eapply weakening_store; eauto.
- intros S T0 Hty Hok. inversion Hty; subst. edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto. exists S'. repeat split; auto. econstructor; eauto. eapply weakening_store; eauto.
- intros S T0 Hty Hok. inversion Hty; subst. edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto. exists S'. repeat split; auto. econstructor; eauto. eapply weakening_store; eauto.
- intros S T0 Hty Hok. inversion Hty; subst. inversion H3; subst. exists S. repeat split; auto. apply extends_refl. eapply substitution_preserves_typing_0; eauto.
- intros S T0 Hty Hok. inversion Hty; subst. exists S. repeat split; auto. apply extends_refl. eapply substitution_preserves_typing_0; eauto.
- intros S T0 Hty Hok. inversion Hty; subst. edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto. exists S'. repeat split; auto. constructor. assumption.
- intros S T0 Hty Hok. inversion Hty; subst. exists (S ++ [T]). repeat split.
  + unfold extends. exists [T]. reflexivity.
+ constructor; auto. eapply weakening_store; eauto. unfold extends. exists [T]. reflexivity. rewrite nth_error_app2. rewrite Nat.sub_diag. reflexivity. auto.
+ constructor. rewrite nth_error_app2. rewrite Nat.sub_diag. reflexivity. auto.
  * admit.
* admit.
- intros S T0 Hty Hok. inversion Hty; subst. edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto. exists S'. repeat split; auto. constructor. assumption.
- intros S T0 Hty Hok. inversion Hty; subst. inversion H2; subst. exists S. repeat split; auto. apply extends_refl. eapply heap_lookup_type; eauto.
inversion H3; subst. assumption.
- intros S T0 Hty Hok. inversion Hty; subst. edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto. exists S'. repeat split; auto. econstructor; eauto. eapply weakening_store; eauto.
- intros S T0 Hty Hok. inversion Hty; subst. edestruct IHHstep as [S' [Hext [Hok' Hty']]]; eauto. exists S'. repeat split; auto. econstructor; eauto. eapply weakening_store; eauto.
- intros S T0 Hty Hok. inversion Hty; subst. inversion H3; subst. inversion H2; subst. exists S. repeat split; auto. apply extends_refl. eapply heap_update_ok; eauto. constructor.
  + inversion H4; subst. assumption.
+ constructor.
Qed.

