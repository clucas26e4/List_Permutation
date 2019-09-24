Require Import Lia.

Require Import List_more.
Require Import List_Type_more.

Require Import Fun_nat.
Require Import Perm.
Require Import misc.
Require Import Perm_solve.

Inductive formulas : Set :=
| var : nat -> formulas
| covar : nat -> formulas
| tens : formulas -> formulas -> formulas
| parr : formulas -> formulas -> formulas.

Fixpoint dual A :=
  match A with
  | var X => covar X
  | covar X => var X
  | tens A B => parr (dual B) (dual A)
  | parr A B => tens (dual B) (dual A)
  end.

Inductive mll_cut : list formulas -> Type :=
| ax_cut_r : forall X, mll_cut (covar X :: var X :: nil)
| ex_cut_r : forall l f, mll_cut l -> is_perm f = true -> length f = length l ->
                     mll_cut (app_nat_fun f l)
| tens_cut_r : forall A B l1 l2, mll_cut (A :: l1) -> mll_cut (B :: l2) ->
                             mll_cut (tens A B :: l2 ++ l1)
| parr_cut_r : forall A B l, mll_cut (A :: B :: l) -> mll_cut (parr A B :: l)
| cut_r : forall A l1 l2, mll_cut (dual A :: l1) -> mll_cut (A :: l2) ->
                          mll_cut (l2 ++ l1).

Inductive mll : list formulas -> Type :=
| ax_r : forall X, mll (covar X :: var X :: nil)
| ex_r : forall l f, mll l -> is_perm f = true -> length f = length l ->
                     mll (app_nat_fun f l)
| tens_r : forall A B l1 l2, mll (A :: l1) -> mll (B :: l2) ->
                             mll (tens A B :: l2 ++ l1)
| parr_r : forall A B l, mll (A :: B :: l) -> mll (parr A B :: l).