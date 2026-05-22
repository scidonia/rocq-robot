Require Import Arith List Compare_dec.
Import ListNotations.

(** * PCF with References *)

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

Lemma ctx_lookup_app : forall G1 G2 x T,
  nth_error (G1 ++ G2) (length G1 + x) = Some T -> nth_error G2 x = Some T.
Proof. induction G1; simpl; intros H; [exact H | apply IHG1; exact H]. Qed.

Lemma ctx_lookup_skip : forall G1 G2 x T,
  nth_error (G1 ++ (T :: G2)) x = Some T -> x < length G1 -> nth_error G1 x = Some T.
Proof.
  induction G1 as [| T1 G1' IH]; simpl; intros x T2 H Hlen;
    [exfalso; exact (Lt.lt_n_O _ Hlen) | ].
Qed.

Lemma substitution_preserves_typing : forall G1 G2 S x s t T,
  has_type (G1 ++ G2) S s T ->
  has_type (G1 ++ (T :: G2)) S t T ->
  has_type (G1 ++ G2) S (subst (length G1) s t) T.
Proof.
  intros G1 G2 S x s t T Hs Ht. revert G1 G2 x s Hs.
  induction Ht; simpl; intros G1 G2 x s Hs.
Qed.

Definition extends (S' S : store_ty) : Prop := exists S2, S' = S ++ S2.
Lemma extends_refl : forall S, extends S S.
Proof. exists []; rewrite app_nil_r; reflexivity. Qed.

Lemma nth_error_app_l : forall A (l1 l2 : list A) n x,
  nth_error l1 n = Some x -> nth_error (l1 ++ l2) n = Some x.
Proof.
induction l1 as [| a l1' IH].
- intros l2 n x H; destruct n; simpl in H; discriminate.
- intros l2 n x H; destruct n; simpl in *; auto.
Qed.


Lemma has_type_weaken : forall G S1 S2 t T,
  has_type G S1 t T -> extends S2 S1 -> has_type G S2 t T.
Proof.
intros G S1 S2 t T Ht Hext. induction Ht; try (constructor; auto); try (constructor; apply IHHt; auto); try (constructor; [apply IHHt1 | apply IHHt2]; auto). destruct Hext as [S3 Heq]; subst; constructor; apply nth_error_app_l with (1 := H).
- constructor; [apply IHHt1; auto | apply IHHt2; auto].
- constructor; [apply IHHt1; auto | apply IHHt2; auto].
- constructor; [apply IHHt1; auto | apply IHHt2; auto].
- destruct Hext as [S3 Heq]. subst. apply nth_error_app_l. exact H.
Qed.

Qed.

Lemma extends_heap_ok : forall mu S S',
  heap_ok mu S -> extends S' S -> heap_ok mu S'.
Proof.
Proof.
Proof.
  intros mu S S' H Hok Hext. induction Hok.
  - apply heap_empty.
  - apply heap_cons; [apply IHHok; auto | apply has_type_weaken with (1 := H0); auto | ].
    destruct Hext as [S3 Heq]; subst; apply nth_error_app_l; exact H1.
Qed.


Lemma heap_ok_lookup : forall mu S l v,
Lemma heap_ok_lookup : forall mu S l v,
  heap_ok mu S -> heap_lookup l mu = Some v ->
  exists T, nth_error S l = Some T /\ has_type [] S v T.
Proof.
  induction 1 as [S | l v mu S T Hok IH Htv Hnth];
    simpl; intros Hlook.
  - discriminate.
  - destruct (Nat.eqb_spec l l0).
    + subst. injection Hlook as [= ->]. exists T. split; [exact Hnth | exact Htv].
    + apply IH; exact Hlook.
Qed.em preservation : forall t mu t' mu' T S,
  has_type [] S t T -> step t mu t' mu' ->
  heap_ok mu S ->
  exists S', extends S' S /\ heap_ok mu' S' /\ has_type [] S' t' T.
Proof.


intro Hok; inversion H; subst; destruct (IHstep H3 Hok) as [S' [Hext [Hok' Ht']]]; exists S'; split; [exact Hext | split; [exact Hok' | apply T_Succ; exact Ht']].
intro Hok; inversion H; subst.
eexists S; split; [apply extends_refl | split; [exact Hok | econstructor; eauto using T_Num, T_Bool, T_Succ, T_Pred, T_IsZero, T_If]].
Qed.
