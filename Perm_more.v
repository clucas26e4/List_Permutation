(* ll library for yalla *)

Require Import CMorphisms.
Require Import Lia.
Require Import PeanoNat.
Require Import EqNat.
Require Import Injective.

Require Import Bool_more.
Require Import List_Type_more.
Require Import List_more2.
Require Import List_nat.
Require Import Fun_nat.
Require Import misc.
Require Import Perm.

(* First statement is not valid otherwise second one would be, see below
Lemma app_nat_fun_map_inv {A B} :
  forall (f : A -> B) g l1 l2,
    is_perm g = true ->
    app_nat_fun g l1 = (map f l2) ->
    { l : _ & l1 = map f l & app_nat_fun g l = l2}.
Proof with try assumption; try reflexivity.
intros f g; induction l1; intros l2 Hperm Heq.
- exists nil...
  destruct l2; inversion Heq...
- admit.
Qed.

Lemma app_nat_fun_image {A B} : forall (f : A -> B) g a l l',
    is_perm g = true ->
    app_nat_fun g (a :: l) = map f l' -> { a' | a = f a' }.
Proof.
intros f g a l l' Hperm HP.
apply app_nat_fun_map_inv in HP; [ | apply Hperm].
destruct HP as [l'' Heq _].
destruct l'' ; inversion Heq.
eexists ; reflexivity.
Qed.
*)

Goal (forall A B (f : A -> B) g a l l',
    is_perm g = true ->
    app_nat_fun g (a :: l) = map f l' -> { a' | a = f a' }) -> False.
Proof.
intros app_nat_fun_inv.
specialize app_nat_fun_inv with nat nat (fun _ => 0) nil 1 (nil) (nil).
assert (is_perm nil = true) as Hperm by (unfold is_perm; split).
apply app_nat_fun_inv in Hperm.
- inversion Hperm.
  inversion H.
- reflexivity.
Qed.

