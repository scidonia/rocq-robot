From Stdlib Require Import Arith Lia.

(** * A simple dependently-typed language: Nat + Vec

    Types:
      T ::= Nat | Vec T n

    Terms:
      t ::= zero | succ t | nil | cons t t | head t | tail t
            | lit n       (* natural number literal *)
            | vlit n ts   (* vector literal of length n *)

    We keep it small: Nat and Vec Nat n only, no polymorphism.
    The key dependent case: [head] and [tail] require a non-zero length.

    Typing judgment: has_type t T
    Small-step reduction: step t t'

    Main theorem: type preservation — if has_type t T and step t t'
    then has_type t' T.
*)

(* ------------------------------------------------------------------ *)
(** ** Types *)

Inductive ty : Type :=
  | TNat  : ty
  | TVec  : nat -> ty.       (* TVec n = vector of nats of length n *)

(* ------------------------------------------------------------------ *)
(** ** Terms *)

Inductive tm : Type :=
  | tzero  : tm                    (* zero : Nat *)
  | tsucc  : tm -> tm              (* succ t : Nat *)
  | tlit   : nat -> tm             (* literal nat n : Nat *)
  | tnil   : tm                    (* nil : Vec 0 *)
  | tcons  : tm -> tm -> tm        (* cons hd tl : Vec (S n) when tl : Vec n *)
  | thead  : tm -> tm              (* head v : Nat when v : Vec (S n) *)
  | ttail  : tm -> tm.             (* tail v : Vec n when v : Vec (S n) *)

(* ------------------------------------------------------------------ *)
(** ** Typing *)

Inductive has_type : tm -> ty -> Prop :=
  | T_Zero  : has_type tzero TNat
  | T_Succ  : forall t,
      has_type t TNat ->
      has_type (tsucc t) TNat
  | T_Lit   : forall n,
      has_type (tlit n) TNat
  | T_Nil   : has_type tnil (TVec 0)
  | T_Cons  : forall hd tl n,
      has_type hd TNat ->
      has_type tl (TVec n) ->
      has_type (tcons hd tl) (TVec (S n))
  | T_Head  : forall v n,
      has_type v (TVec (S n)) ->
      has_type (thead v) TNat
  | T_Tail  : forall v n,
      has_type v (TVec (S n)) ->
      has_type (ttail v) (TVec n).

(* ------------------------------------------------------------------ *)
(** ** Values *)

Inductive value : tm -> Prop :=
  | V_Zero  : value tzero
  | V_Succ  : forall t, value t -> value (tsucc t)
  | V_Lit   : forall n, value (tlit n)
  | V_Nil   : value tnil
  | V_Cons  : forall hd tl, value hd -> value tl -> value (tcons hd tl).

(* ------------------------------------------------------------------ *)
(** ** Small-step reduction *)

Inductive step : tm -> tm -> Prop :=
  (* Congruence under succ *)
  | S_Succ  : forall t t',
      step t t' ->
      step (tsucc t) (tsucc t')
  (* Congruence: reduce head of cons *)
  | S_ConsHd : forall hd hd' tl,
      step hd hd' ->
      step (tcons hd tl) (tcons hd' tl)
  (* Congruence: reduce tail of cons *)
  | S_ConsTl : forall hd tl tl',
      value hd ->
      step tl tl' ->
      step (tcons hd tl) (tcons hd tl')
  (* Congruence: reduce argument of head *)
  | S_Head  : forall v v',
      step v v' ->
      step (thead v) (thead v')
  (* Congruence: reduce argument of tail *)
  | S_Tail  : forall v v',
      step v v' ->
      step (ttail v) (ttail v')
  (* head (cons hd tl) → hd *)
  | S_HeadCons : forall hd tl,
      value hd -> value tl ->
      step (thead (tcons hd tl)) hd
  (* tail (cons hd tl) → tl *)
  | S_TailCons : forall hd tl,
      value hd -> value tl ->
      step (ttail (tcons hd tl)) tl.

(* ------------------------------------------------------------------ *)
(** ** Preservation *)

Theorem preservation : forall t t' T,
  has_type t T ->
  step t t' ->
  has_type t' T.
Proof.
intros t t' T Hty Hstep. revert T Hty. induction Hstep.
- intros T Hty; inversion Hty; subst; apply T_Succ; apply IHHstep; assumption.
- intros T Hty; inversion Hty; subst; apply T_Cons; [apply IHHstep; assumption | assumption].
- intros T Hty; inversion Hty; subst; eapply T_Cons; [eassumption | apply IHHstep; eassumption].
- intros T Hty; inversion Hty; subst; eapply T_Head; apply IHHstep; eassumption.
- intros T Hty; inversion Hty; subst; eapply T_Tail; apply IHHstep; eassumption.
- intros T Hty; inversion Hty; subst; inversion H2; subst; assumption.
- intros T Hty; inversion Hty; subst; inversion H2; subst; assumption.
Qed.
