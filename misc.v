(* Some useful tactics *)

Require Import Lia.
Require Import Nat.
Require Import PeanoNat.
Require Import List_more.
Require Import List_nat.
Require Import Fun_nat.
Require Import Transposition.

Ltac length_lia := repeat (try rewrite concat_app in *;
                           try rewrite incr_all_length in *;
                           try rewrite app_length in *;
                           try rewrite seq_length in *;
                           try rewrite cfun_length in *;
                           try rewrite transpo_length in *;
                           try rewrite map_length in *; simpl in *); lia.

Ltac specialize_hyps :=
  repeat match goal with
         | [ H1 : ?A, H2 : ?A -> ?B |- _ ] => specialize (H2 H1)
         end.

Ltac splitb := apply andb_true_intro; split.
