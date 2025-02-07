(* Tactic for automatic length computation *)

From Stdlib Require Import PeanoNat Lia.
From OLlibs Require Import List_more.
Require Import List_nat Fun_nat Transposition.

Ltac length_lia := repeat (try rewrite concat_app in *;
                           try rewrite shift_length in *;
                           try rewrite length_app in *;
                           try rewrite length_seq in *;
                           try rewrite cfun_length in *;
                           try rewrite shift_length in *;
                           try rewrite transpo_length in *;
                           try rewrite length_map in *; simpl in *); lia.
