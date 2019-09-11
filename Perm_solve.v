Require Export all_lt_solve.
Require Export misc.
Require Import List_more.
Require Import Perm.
Require Import List_nat.
Require Import List_more2.
Require Import Fun_nat.

Ltac replace_perm perm L1 L2 :=
  let p := fresh "p" in
  let Hperm := fresh "Hperm" in
  let Hlenp := fresh "Hlenp" in
  let Heqp := fresh "Heqp" in
  destruct (perm_block perm L1 L2) as (p & (Hperm & (Hlenp & Heqp))) ; [ reflexivity | reflexivity | reflexivity | unfold concat at 1 in Heqp; symmetry in Heqp; unfold concat at 1 in Heqp; rewrite Heqp].

