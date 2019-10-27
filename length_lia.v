(* Tactic for automatic length computation *)

Require Import Lia.
Require Import PeanoNat.
Require Import List_more.
Require Import List_nat.
Require Import Fun_nat.
Require Import Transposition.

Ltac length_lia := repeat (try rewrite concat_app in *;
                           try rewrite shift_length in *;
                           try rewrite app_length in *;
                           try rewrite seq_length in *;
                           try rewrite cfun_length in *;
                           try rewrite shift_length in *;
                           try rewrite transpo_length in *;
                           try rewrite map_length in *; simpl in *); lia.

