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
intros S. unfold extends. exists []. symmetry. apply app_nil_r.
Qed.



Lemma nth_error_app_l : forall A (l1 l2 : list A) n x, nth_error l1 n = Some x -> nth_error (l1 ++ l2) n = Some x.
Proof.
induction l1 as [|h t IH]; simpl; intros l2 n x H.
- destruct n; simpl in H; [discriminate | discriminate].
- destruct n; simpl in *.
  + assumption.
  + apply (IH l2 n x). exact H.
Qed.



Lemma has_type_weaken : forall G S1 S2 t T, has_type G S1 t T -> extends S2 S1 -> has_type G S2 t T.
Proof.
  intros G S1 S2 t T Hty Hext.
  unfold extends in Hext. destruct Hext as [Sx ->].
  revert Sx.
  induction Hty; intros Sx.
  - apply T_Var; auto.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ; apply IHHty; unfold extends; exists Sx; reflexivity.
  - apply T_Pred; apply IHHty; unfold extends; exists Sx; reflexivity.
  - apply T_IsZero; apply IHHty; unfold extends; exists Sx; reflexivity.
  - apply T_If; [apply IHHty1 | apply IHHty2 | apply IHHty3];
    unfold extends; exists Sx; reflexivity.
  - apply T_Lam with (T1 := T1) (T2 := T2); apply IHHty;
    unfold extends; exists Sx; reflexivity.
  - apply T_App with (T1 := T1); [apply IHHty1 | apply IHHty2];
    unfold extends; exists Sx; reflexivity.
  - apply T_Fix; apply IHHty; unfold extends; exists Sx; reflexivity.
  - apply T_Ref; apply IHHty; unfold extends; exists Sx; reflexivity.
  - apply T_Deref; apply IHHty; unfold extends; exists Sx; reflexivity.
  - apply T_Assign; [apply IHHty1 | apply IHHty2];
    unfold extends; exists Sx; reflexivity.
  - apply T_Loc; apply nth_error_app_l with (l1 := S1); exact H.
Qed.


Lemma test_admits : True /\ True /\ True /\ True.
Proof.
split.
- 
- split.
  + split.
    * admit.
    * exact I.
  + split.
    * exact I.
    * admit.
    admit.
Admitted.




Lemma heap_ok_lookup : forall mu S l v, heap_ok mu S -> heap_lookup l mu = Some v -> exists T, nth_error S l = Some T /\ has_type [] S v T.
Proof.
  induction 1; intros k w Hlook; simpl in *.
  - discriminate.
  - destruct (Nat.eqb k l) eqn:Heq.
    + injection Hlook; intros; subst.
      exists T; split; auto. exact H0.
    + apply IHheap_ok. exact Hlook.
Qed.

Lemma extends_heap_ok : forall mu S S',
  heap_ok mu S -> extends S' S -> heap_ok mu S'.
Proof.
  intros mu S S' Hok Hext.
  unfold extends in Hext. destruct Hext as [Sx ->].
  induction Hok.
  - apply heap_empty.
  - apply heap_cons with (T := T); auto.
    apply nth_error_app_l; auto.
Qed.

Lemma heap_ok_update : forall mu S l v T,
  heap_ok mu S -> nth_error S l = Some T -> has_type [] S v T ->
  heap_ok (heap_update l v mu) S.
Proof.
  induction 1; intros k u T0 Hnth Hty; simpl.
  - inversion Hnth.
  - destruct (Nat.eqb l0 k) eqn:Heq.
    + apply heap_cons with (T := T0); auto.
      apply Nat.eqb_eq in Heq; subst.
      eapply nth_error_Some_nth. exact Hnth.
      exact Hty.
    + apply heap_cons with (T := T); auto.
      eapply IHheap_ok; eauto.
Qed.

Lemma substitution_preserves_typing : forall S t T U s,
  has_type [U] S t T -> has_type [] S s U -> has_type [] S (subst 0 s t) T.
Proof.
  intros S t T U s Hty Hsty. remember [U] as G. revert U HeqG.
  induction Hty; intros U' HeqU Hsty'; simpl; injection HeqU as ?; subst G.
  - (* T_Num *) apply T_Num.
  - (* T_Bool *) apply T_Bool.
  - (* T_Var *)
    destruct x; simpl in H.
    + injection H; intros; subst. exact Hsty'.
    + discriminate.
  - (* T_Succ *) apply T_Succ. apply IHHty; auto.
  - (* T_Pred *) apply T_Pred. apply IHHty; auto.
  - (* T_IsZero *) apply T_IsZero. apply IHHty; auto.
  - (* T_If *)
    apply T_If; [apply IHHty1 | apply IHHty2 | apply IHHty3]; auto.
  - (* T_Lam *)
    apply T_Lam. apply IHHty. reflexivity. exact Hsty'.
  - (* T_App *) apply T_App; [apply IHHty1 | apply IHHty2]; auto.
  - (* T_Fix *)
    apply T_Fix. apply IHHty. reflexivity. exact Hsty'.
  - (* T_Ref *) apply T_Ref. apply IHHty; auto.
  - (* T_Deref *) apply T_Deref. apply IHHty; auto.
  - (* T_Assign *)
    apply T_Assign with (T := T); [apply IHHty1 | apply IHHty2]; auto.
  - (* T_Loc *)
    apply T_Loc. exact H.
Qed.

Lemma nth_error_last : forall A (l : list A) (x : A),
  nth_error (l ++ [x]) (length l) = Some x.
Proof.
  intros A l x. rewrite nth_error_app2 by lia.
  replace (length l - length l) with 0 by lia. simpl. reflexivity.
Qed.


Lemma test_nested : (True /\ True) /\ (True /\ True).
Proof.
split.
- split.
  + exact I.
  + exact I.
- split.
  + exact I.
  + exact I.
Qed.
Theorem preservation : forall t mu t' mu' T S,
  has_type [] S t T -> step t mu t' mu' ->
  heap_ok mu S ->
  exists S', extends S' S /\ heap_ok mu' S' /\ has_type [] S' t' T.
Proof.
  intros t mu t' mu' T S Hty Hstep Hok. revert T S Hty Hok. induction Hstep.
  - (* S_Succ *) intros T S Hty Hok. inversion Hty; subst.
    destruct (IHHstep TyNat S H2 Hok) as [S' [Hext [Hok' Hty']]].
    exists S'; split; [exact Hext | split; [exact Hok' | apply T_Succ; exact Hty']].
  - (* S_PredZero *) intros T S Hty Hok. inversion Hty; subst.
    exists S; split; [apply extends_refl | split; [exact Hok | exact H2]].
  - (* S_PredSucc *) intros T S Hty Hok. inversion Hty; subst.
    exists S; split; [apply extends_refl | split; [exact Hok | apply T_Num]].
  - (* S_Pred *) intros T S Hty Hok. inversion Hty; subst.
    destruct (IHHstep TyNat S H2 Hok) as [S' [Hext [Hok' Hty']]].
    exists S'; split; [exact Hext | split; [exact Hok' | apply T_Pred; exact Hty']].
  - (* S_IsZeroZero *) intros T S Hty Hok. inversion Hty; subst.
    exists S; split; [apply extends_refl | split; [exact Hok | apply T_Bool]].
  - (* S_IsZeroSucc *) intros T S Hty Hok. inversion Hty; subst.
    exists S; split; [apply extends_refl | split; [exact Hok | apply T_Bool]].
  - (* S_IsZero *) intros T S Hty Hok. inversion Hty; subst.
    destruct (IHHstep TyNat S H2 Hok) as [S' [Hext [Hok' Hty']]].
    exists S'; split; [exact Hext | split; [exact Hok' | apply T_IsZero; exact Hty']].
  - (* S_IfTrue *) intros T S Hty Hok. inversion Hty; subst.
    exists S; split; [apply extends_refl | split; [exact Hok | eauto]].
  - (* S_IfFalse *) intros T S Hty Hok. inversion Hty; subst.
    exists S; split; [apply extends_refl | split; [exact Hok | eauto]].
  - (* S_If *) intros T S Hty Hok. inversion Hty; subst.
    destruct (IHHstep TyBool S H4 Hok) as [S' [Hext [Hok' Hty']]].
    exists S'; split; [exact Hext | split; [exact Hok' |
      apply T_If with (T := T); [exact Hty' |
        apply has_type_weaken with (S1 := S); [exact H6 | exact Hext] |
        apply has_type_weaken with (S1 := S); [exact H7 | exact Hext] ] ] ].
  - (* S_App1 *) intros T S Hty Hok. inversion Hty; subst.
    destruct (IHHstep (TyArrow T1 T) S H3 Hok) as [S' [Hext [Hok' Hty']]].
    exists S'; split; [exact Hext | split; [exact Hok' |
      apply T_App with (T1 := T1); [exact Hty' |
        apply has_type_weaken with (S1 := S); [exact H5 | exact Hext] ] ] ].
  - (* S_App2 *) intros T S Hty Hok. inversion Hty; subst.
    destruct (IHHstep T1 S H6 Hok) as [S' [Hext [Hok' Hty']]].
    exists S'; split; [exact Hext | split; [exact Hok' |
      apply T_App with (T1 := T1); [apply has_type_weaken with (S1 := S); [exact H4 | exact Hext] | exact Hty'] ] ].
  - (* S_AppAbs *)
    intros T S Hty Hok. inversion Hty; subst.
    inversion H; subst. inversion H2; subst.
    exists S; split; [apply extends_refl | split; [exact Hok |
      apply substitution_preserves_typing with (U := T1); [exact H6 | exact H7] ] ].
  - (* S_Fix *)
    intros T S Hty Hok. inversion Hty; subst.
    exists S; split; [apply extends_refl | split; [exact Hok |
      apply substitution_preserves_typing with (U := T); [exact H | apply T_Fix; exact H] ] ].
  - (* S_Ref *) intros T S Hty Hok. inversion Hty; subst.
    destruct (IHHstep T S H4 Hok) as [S' [Hext [Hok' Hty']]].
    exists S'; split; [exact Hext | split; [exact Hok' | apply T_Ref; exact Hty']].
  - (* S_RefV *)
    intros T S Hty Hok. inversion Hty; subst.
    inversion H2; subst.
    exists (S ++ [T]).
    split. { unfold extends. exists [T]. reflexivity. }
    split.
    { apply heap_cons with (T := T).
      - apply extends_heap_ok with (S := S); auto.
        unfold extends. exists []. apply app_nil_r.
      - apply has_type_weaken with (S1 := S); [exact H4 | unfold extends; exists [T]; reflexivity].
      - apply nth_error_last. }
    { apply T_Loc. apply nth_error_last. }
  - (* S_Deref *) intros T S Hty Hok. inversion Hty; subst.
    destruct (IHHstep (TyRef T) S H4 Hok) as [S' [Hext [Hok' Hty']]].
    exists S'; split; [exact Hext | split; [exact Hok' | apply T_Deref; exact Hty']].
  - (* S_DerefLoc *)
    intros T S Hty Hok. inversion Hty; subst.
    inversion H3; subst.
    destruct (heap_ok_lookup mu S l v Hok H) as [T0 [Hnth Htyv]].
    exists S; split; [apply extends_refl | split; [exact Hok |
      injection Hnth; intros; subst; exact Htyv] ].
  - (* S_Assign1 *) intros T S Hty Hok. inversion Hty; subst.
    destruct (IHHstep (TyRef T0) S H4 Hok) as [S' [Hext [Hok' Hty']]].
    exists S'; split; [exact Hext | split; [exact Hok' |
      apply T_Assign with (T := T0); [exact Hty' |
        apply has_type_weaken with (S1 := S); [exact H6 | exact Hext] ] ] ].
  - (* S_Assign2 *) intros T S Hty Hok. inversion Hty; subst.
    destruct (IHHstep T0 S H6 Hok) as [S' [Hext [Hok' Hty']]].
    exists S'; split; [exact Hext | split; [exact Hok' |
      apply T_Assign with (T := T0); [apply has_type_weaken with (S1 := S); [exact H4 | exact Hext] | exact Hty'] ] ].
  - (* S_AssignV *)
    intros T S Hty Hok. inversion Hty; subst.
    inversion H2; subst.
    exists S; split; [apply extends_refl | split; [
      apply heap_ok_update with (T := T0); [exact Hok | apply H4 | exact H5] |
      apply T_Num] ].
Qed.
