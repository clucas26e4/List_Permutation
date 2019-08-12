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

Lemma app_nat_fun_map_inv {A B} :
  forall (f : A -> B) g l1 l2,
    is_perm g = true ->
    app_nat_fun g l1 = (map f l2) ->
    { l : _ & l1 = map f l & app_nat_fun g l = l2}.
Proof with try assumption; try reflexivity.
  intros f g l1 l2 Hperm Heq.
Admitted.

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