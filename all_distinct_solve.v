(* Automatic tactic to solve all_distinct goals *)

Require Import List_more.
Require Import Lia.
Require Import Nat.
Require Import PeanoNat.
Require Import List_nat.
Require Import List_manip.
Require Import Perm.
Require Import misc.
Require Import Bool_more.
Require Import all_lt_solve.

Ltac neg_In_nat_bool_run :=
  match goal with
  | |- negb (In_nat_bool _ _) = true => apply negb_true_iff
  | |- In_nat_bool ?n (incr_all _ ?m) = false =>
    try (
        apply negb_In_incr_all; length_lia);
    try (
        let p := fresh "p" in
        let Heq := fresh "Heq" in
        destruct (Nat.le_exists_sub m n) as  (p & (Heq & _));
        [ length_lia |
          rewrite (Nat.add_comm p) in Heq;
          rewrite Heq; rewrite<- In_nat_bool_incr_all ]);
    fail
  end.

Ltac all_distinct_run :=
  match goal with
  | |- all_distinct (_ :: _) = true => unfold all_distinct; fold all_distinct; apply andb_true_intro; split; [ repeat neg_In_nat_bool_run | ]
  | |- all_distinct (incr_all _ _) = true => rewrite<- all_distinct_incr_all
  | |- all_distinct (Id _) = true => apply all_distinct_Id
  | |- all_distinct (cfun _ _) = true => apply all_distinct_cfun
  | |- all_distinct (_ ++ incr_all _ _) = true => apply all_distinct_app ; [repeat all_lt_run | | ]
  | |- all_distinct (incr_all _ _ ++ _) = true => rewrite all_distinct_app_commu
  | |- all_distinct nil = true => reflexivity
  | |- all_distinct (nil ++ _) = true => rewrite app_nil_l
  | |- all_distinct (_ ++ nil) = true => rewrite app_nil_r
  end.

Ltac all_distinct_reorg :=
  match goal with
  | |- all_distinct (incr_all _ _ ++ _) = true => rewrite all_distinct_app_commu; rewrite<- ? app_assoc
  end.

Ltac all_distinct_solve := repeat all_distinct_reorg; rewrite <- ? incr_all_app;
  match goal with
  | |- all_distinct (Id _) = true => apply all_distinct_Id
  | |- all_distinct (Id _ ++ _) = true => apply all_distinct_app ; [ repeat all_lt_run | apply all_distinct_Id | ]
  end.