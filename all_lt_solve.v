(* Automatic tactic to solve all_lt goals *)

From Stdlib Require Import PeanoNat Lia.
From OLlibs Require Import List_more.
Require Import List_nat Fun_nat Perm length_lia.

Ltac all_lt_run :=
  match goal with
  | |- all_lt (_ :: _) _ = true => unfold all_lt; fold all_lt; apply andb_true_intro; split; [apply Nat.ltb_lt; length_lia | ]
  | |- all_lt (cfun ?a ?b) _ = true => apply all_lt_leq with (a + b) ; [ apply all_lt_cfun | length_lia]
  | |- all_lt (?a ++ ?b) _ = true => rewrite all_lt_app; apply andb_true_intro; split
  | |- all_lt (incr_all ?a ?n) ?m = true => let p := fresh "p" in
                                            let Heq := fresh "Heq" in
                                            destruct (Nat.le_exists_sub n m) as  (p & (Heq & _));
                                            [ length_lia |
                                              rewrite (Nat.add_comm p) in Heq;
                                              rewrite Heq; rewrite all_lt_shift_true ]
  | |- all_lt (Id ?n) ?m = true => apply all_lt_leq with n ; [apply all_lt_seq | length_lia]
  | |- all_lt nil _ = true => reflexivity
  | |- all_lt (nil ++ _) _ = true => rewrite app_nil_l
  | |- all_lt (_ ++ nil) _ = true => rewrite app_nil_r
  end.
