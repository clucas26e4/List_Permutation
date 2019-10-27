(* Consecutive and non-consecutive transpositions.
   Decomposition of a non-consecutive transpositions into a composition of consecutive ones. *)
Require Import Lia.
Require Import PeanoNat.

Require Import Bool_more.
Require Import List_more.
Require Import List_nat.
Require Import Fun_nat.

Ltac length_lia := repeat (try rewrite concat_app;
                           try rewrite shift_length in *;
                           try rewrite app_length in *;
                           try rewrite seq_length in *;
                           try rewrite cfun_length in *;
                           try rewrite map_length in *; simpl in *); lia.




(** ** Transposition *)
Definition transpo m n :=
  if n <? m then
  (*[0...n-1,n+1   , n ,   n+2 ... m ]*)
    Id n ++ (S n) :: n :: (seq (2 + n) (S m - (2 + n))) else Id (S m).

Lemma transpo_decomp m n :
  n < m -> transpo m n = Id n ++ incr_all ((1 :: 0 :: nil) ++ incr_all (Id (S m - (2 + n))) 2) n.
Proof.
intros Hle.
apply Nat.ltb_lt in Hle.
unfold transpo; rewrite Hle.
f_equal.
rewrite shift_app.
change (S n :: n :: seq (2 + n) (S m - (2 + n)))
  with ((S n :: n :: nil) ++ seq (2 + n) (S m - (2 + n))).
f_equal.
- simpl; f_equal; [lia | f_equal; lia].
- rewrite <- shift_plus.
  rewrite incr_all_seq; reflexivity.
Qed.

Lemma transpo_decomp2 m n :
   { prod (transpo m n = Id (S m)) (m <= n) }
 + { prod (transpo m n = Id n ++ incr_all ((1 :: 0 :: nil) ++ incr_all (Id (S m - (2 + n))) 2) n)
          (n < m) }.
Proof.
case_eq (n <? m); intros Hle; unfold transpo; rewrite Hle; [ right | left ]; split.
- rewrite <- transpo_decomp.
  + unfold transpo; rewrite Hle; reflexivity.
  + apply Nat.ltb_lt; assumption.
- apply Nat.ltb_lt; assumption.
- reflexivity.
- apply Nat.ltb_ge in Hle; lia.
Qed.

Ltac decomp_transpo m n :=
  destruct (transpo_decomp2 m n) as [[Ht Hltb] | [Ht Hltb]]; rewrite Ht;
  [ assert (Hlt := (proj2 (Nat.ltb_ge _ _)) Hltb)
  | assert (Hlt := (proj2 (Nat.ltb_lt _ _)) Hltb) ].

Lemma transpo_length : forall m n, length (transpo m n) = (S m).
Proof.
intros m n; decomp_transpo m n.
- apply seq_length.
- rewrite app_length; simpl.
  rewrite 2 shift_length.
  rewrite 2 seq_length ; lia.
Qed.

Lemma all_lt_transpo : forall m n, all_lt (transpo m n) (S m) = true.
Proof.
intros m n; decomp_transpo m n.
- apply all_lt_seq; lia.
- rewrite all_lt_app.
  apply andb_true_iff; split.
  + apply all_lt_seq; lia.
  + replace (S m) with (n + (S m - n)) by lia.
    rewrite all_lt_shift_true; [ reflexivity | ].
    rewrite all_lt_app.
    apply andb_true_iff; split.
    * apply all_lt_leq with 2; [ reflexivity | lia].
    * replace (S m - n) with (2 + (S m - (2 + n))) at 2 by lia.
      rewrite all_lt_shift_true; [ reflexivity | ].
      apply all_lt_seq; lia.
Qed.

Lemma all_distinct_transpo : forall m n, all_distinct (transpo m n) = true.
Proof.
intros m n; decomp_transpo m n.
- apply all_distinct_seq.
- apply all_distinct_app; [ | | apply all_distinct_app ];
    try reflexivity; try apply all_distinct_seq.
  apply all_lt_seq; lia.
Qed.

Definition compo_transpo m := fold_right (fun i => app_nat_fun (transpo m i)) (Id (S m)).

Lemma compo_transpo_length : forall m l, length (compo_transpo m l) = S m.
Proof.
  intros m; induction l.
  - apply seq_length.
  - simpl; rewrite app_nat_fun_length; rewrite transpo_length; now try rewrite IHl.
Qed.

Lemma all_lt_compo_transpo : forall m l, all_lt (compo_transpo m l) (S m) = true.
Proof.
  intros m; induction l.
  - apply all_lt_seq; lia.
  - simpl; rewrite all_lt_app_nat_fun; [ reflexivity | | assumption ].
    rewrite compo_transpo_length.
    apply all_lt_transpo.
Qed.

Lemma app_compo_transpo : forall m l1 l2,
  compo_transpo m (l1 ++ l2) = app_nat_fun (compo_transpo m l1) (compo_transpo m l2).
Proof.
intros.
apply fold_right_app_assoc2.
- symmetry; apply asso_app_nat_fun.
- fold (compo_transpo m).
  rewrite <- (app_nil_r (compo_transpo _ _)) at 1.
  apply app_Id_ext, compo_transpo_length.
Qed.

Lemma compo_transpo_sg : forall m i,
  compo_transpo m (i :: nil) = transpo m i.
Proof.
intros m i.
unfold compo_transpo, fold_right.
apply app_nat_fun_Id_r, all_lt_transpo.
Qed.

(** ** nc_transpo *)
Definition nc_transpo m i j :=
  if (i <? j) && (j <=? m) then
 (*[0...i-1,j,   i+1...j-1 ,              i ,  j+1 ... m]*)
    Id i ++ j :: seq (S i) (j - (S i)) ++ i :: seq (S j) (m - j) else Id (S m).

Lemma nc_transpo_eq m i : nc_transpo m i i = Id (S m).
Proof.
unfold nc_transpo.
replace (i <? i) with false by (symmetry; apply Nat.ltb_ge; lia); reflexivity.
Qed.

Lemma nc_transpo_S m i : nc_transpo m i (S i) = transpo m i.
Proof.
case_eq (i <? m); intros Hlt; unfold nc_transpo, transpo.
- apply Nat.ltb_lt in Hlt.
  replace (i <? S i) with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (S i <=? m) with true by (symmetry; apply Nat.leb_le; lia).
  replace (i <? m) with true by (symmetry; apply Nat.ltb_lt; lia); simpl.
  replace (i - i) with 0 by lia; reflexivity.
- apply Nat.ltb_ge in Hlt.
  replace (S i <=? m) with false by (symmetry; apply Nat.leb_gt; lia).
  replace (i <? m) with false by (symmetry; apply Nat.leb_gt; lia); simpl.
  destruct (i <? S i); reflexivity.
Qed.

Lemma app_nc_transpo {A} : forall (a b : A) l1 l2 l3 m i j,
  m = 1 + length l1 + length l2 + length l3 ->
  i = length l1 ->
  j = 1 + length l1 + length l2 ->
     app_nat_fun (nc_transpo m i j) (l1 ++ a :: l2 ++ b :: l3)
   = l1 ++ b :: l2 ++ a :: l3.
Proof.
intros a b l1 l2 l3 m i j Hm Hi Hj.
unfold nc_transpo.
replace (i <? j) with true by (symmetry; apply Nat.ltb_lt; lia).
replace (j <=? m) with true by (symmetry; apply Nat.leb_le; lia); simpl.
rewrite app_nat_fun_app.
rewrite app_Id_ext by lia.
f_equal.
replace (j :: seq (S i) (j - S i) ++ i :: seq (S j) (m - j))
   with (incr_all (S (length l2) :: seq 1 (length l2) ++ 0 :: seq (S (S (length l2))) (length l3)) i)
  by (repeat (simpl; rewrite ? shift_app; rewrite incr_all_seq); repeat (f_equal; try lia)).
rewrite app_nat_fun_right; try lia.
- replace (S (length l2) :: seq 1 (length l2) ++ 0 :: seq (S (S (length l2))) (length l3))
     with ((S (length l2) :: seq 1 (length l2) ++ 0 :: nil) ++ seq (0 + length (a :: l2 ++ b :: nil)) (length l3))
    by (list_simpl; rewrite app_length; simpl; do 4 f_equal; lia).
  replace (a :: l2 ++ b :: l3) with ((a :: l2 ++ b :: nil) ++ l3) by (list_simpl; reflexivity).
  rewrite app_nat_fun_app.
  rewrite app_nat_fun_left.
  + rewrite <- incr_all_seq.
    rewrite app_nat_fun_right; [ | lia | apply all_lt_seq; lia ].
    rewrite app_Id.
    rewrite app_nat_fun_cons, <- app_comm_cons; f_equal.
    * rewrite app_comm_cons, app_nth2; simpl;
        replace (length l2 - length l2) with 0 by lia; [ reflexivity | lia ].
    * rewrite app_nat_fun_app.
      change (a :: l2 ++ b :: nil) with ((a :: nil) ++ l2 ++ b :: nil).
      replace 1 with (0 + length (a :: nil)) by (simpl; lia).
      rewrite <- incr_all_seq.
      rewrite app_nat_fun_right; [ | |
        rewrite app_length; simpl; apply all_lt_leq with (length l2); [ apply all_lt_seq | ] ]; try lia.
      rewrite app_nat_fun_left, app_Id; [ | apply all_lt_seq; lia ].
      list_simpl; reflexivity.
  + simpl length.
    rewrite app_length; simpl.
    apply andb_true_iff; split; [ apply Nat.ltb_lt; lia | rewrite all_lt_app ].
    apply andb_true_iff; split; [ | reflexivity ].
    apply all_lt_leq with (1 + length l2); [ apply all_lt_seq| ]; lia.
- simpl length.
  rewrite app_length; simpl.
  apply andb_true_iff; split; [ apply Nat.ltb_lt; lia | rewrite all_lt_app ].
  apply andb_true_iff; split; [ | simpl ].
  + apply all_lt_leq with (1 + length l2); [ apply all_lt_seq | ]; lia.
  + replace (S (length l2 + S (length l3)))
       with (S (S (length l2)) + length l3) by lia.
    apply all_lt_seq; lia.
Qed.

Lemma nc_transpo_idem : forall m i j,
  app_nat_fun (nc_transpo m i j) (nc_transpo m i j) = Id (S m).
Proof.
intros m i j; unfold nc_transpo at 2.
case_eq (i <? j); intros Hij; [ case_eq (j <=? m); intros Hjm | ]; unfold andb.
- apply Nat.ltb_lt in Hij; apply Nat.leb_le in Hjm.
  rewrite app_nc_transpo; try length_lia.
  replace (S m) with (i + (S ((j - S i) + S (m - j)))) by lia.
  repeat (rewrite ? seq_app; f_equal; simpl); lia.
- unfold nc_transpo; rewrite Hij, Hjm; unfold andb.
  rewrite <- (app_nil_r (Id (S m))) at 2.
  apply app_Id_ext with (l2 := nil); length_lia.
- unfold nc_transpo; rewrite Hij; unfold andb.
  rewrite <- (app_nil_r (Id (S m))) at 2.
  apply app_Id_ext with (l2 := nil); length_lia.
Qed.

Lemma app_transpo {A} : forall (a b : A) l1 l2 m i,
  m = 1 + length l1 + length l2 ->
  i = length l1 ->
   app_nat_fun (transpo m i) (l1 ++ a :: b :: l2)
 = l1 ++ b :: a :: l2.
Proof.
intros a b l1 l2 m i Hm Hi.
rewrite <- nc_transpo_S.
change (l1 ++ a :: b :: l2) with (l1 ++ a :: nil ++ b :: l2).
rewrite app_nc_transpo; simpl; try lia; reflexivity.
Qed.

Lemma transpo_idem : forall m i,
  app_nat_fun (transpo m i) (transpo m i) = Id (S m).
Proof. intros; rewrite <- nc_transpo_S; apply nc_transpo_idem. Qed.

Lemma nc_transpo_transpo : forall m i j, S i < j -> j <= m ->
  nc_transpo m i j = app_nat_fun (app_nat_fun (transpo m i) (nc_transpo m (S i) j)) (transpo m i).
Proof.
intros m i j Hlt Hle.
rewrite asso_app_nat_fun.
unfold transpo at 2.
replace (i <? m) with true by (symmetry; apply Nat.ltb_lt; lia).
replace (S m - (2 + i)) with ((j - (2 + i)) + (S (m - j))) by lia.
rewrite seq_app.
replace (2 + i + (j - (2 + i))) with j by lia.
simpl seq at 3.
rewrite <- (app_nil_l (i :: _)).
rewrite app_comm_cons, app_assoc.
rewrite app_nc_transpo; try length_lia.
rewrite <- app_assoc, <- app_comm_cons, app_nil_l.
rewrite app_transpo; try length_lia.
unfold nc_transpo.
replace (i <? j) with true by (symmetry; apply Nat.ltb_lt; lia).
replace (j <=? m) with true by (symmetry; apply Nat.leb_le; lia); simpl.
list_simpl; do 2 f_equal.
replace (j - S i) with (S (j - S (S i))) at 1 by lia.
reflexivity.
Qed.

Lemma nc_transpo_transpo_2 : forall m i j, i < j -> S j <= m ->
  nc_transpo m i (S j) = app_nat_fun (app_nat_fun (transpo m j) (nc_transpo m i j)) (transpo m j).
Proof.
intros m i j Hlt Hle.
rewrite asso_app_nat_fun.
unfold transpo at 2.
replace (j <? m) with true by (symmetry; apply Nat.ltb_lt; lia).
replace j with (i + (S (j - S i))) at 4 by lia.
rewrite seq_app; simpl seq.
rewrite <- app_assoc, <- app_comm_cons.
rewrite app_nc_transpo; try length_lia.
rewrite app_comm_cons, app_assoc.
rewrite app_transpo; try length_lia.
unfold nc_transpo.
replace (i <? S j) with true by (symmetry; apply Nat.ltb_lt; lia).
replace (S j <=? m) with true by (symmetry; apply Nat.leb_le; lia); simpl.
list_simpl; do 2 f_equal.
replace (j - i) with (S (j - S i)) at 1 by lia.
rewrite seq_S.
replace (S i + (j - S i)) with j by lia.
list_simpl; reflexivity.
Qed.

Lemma nc_transpo_compo_transpo : forall m i j, i < j -> j <= m ->
  nc_transpo m i j = compo_transpo m (seq i (j - i - 1) ++ rev (seq i (j - i))).
Proof.
intros m i j.
remember (j - i) as k; revert i j Heqk; induction k; intros i j Hk Hlt Hle;
  [ lia | destruct (Nat.eq_dec k 0); subst ].
- replace j with (S i) by lia.
  simpl seq; simpl rev.
  replace (S i - 1 :: i :: nil) with ((i :: nil) ++ i :: nil) by (simpl; f_equal; lia).
  rewrite nc_transpo_S.
  now rewrite app_nil_l, compo_transpo_sg.
- simpl seq; simpl rev.
  destruct k; [ now contradiction n | ].
  replace (compo_transpo m (seq i (S k - 0) ++ rev (seq (S i) (S k)) ++ i :: nil))
     with (app_nat_fun (transpo m i)
          (app_nat_fun (compo_transpo m (seq (S i) k ++ rev (seq (S i) (S k)))) (transpo m i)))
    by (unfold compo_transpo at 2; simpl; f_equal; rewrite <- compo_transpo_sg, <- app_compo_transpo;
        list_simpl; reflexivity).
  replace (S k - 1) with k in IHk by lia.
  rewrite <- (IHk (S i) j); try lia.
  rewrite <- asso_app_nat_fun.
  apply nc_transpo_transpo; lia.
Qed.

Lemma decomp_nc_transpo : forall m i j,
  { l & nc_transpo m i j = compo_transpo m l}.
Proof.
intros m i j.
case_eq ((i <? j) && (j <=? m)); intros Handb.
- apply andb_true_iff in Handb as [Hlt Hle].
  apply Nat.ltb_lt in Hlt.
  apply Nat.leb_le in Hle.
  exists (seq i (j - i - 1) ++ rev (seq i (j - i))).
  apply nc_transpo_compo_transpo; lia.
- unfold nc_transpo; rewrite Handb.
  exists nil; reflexivity.
Qed.

Lemma nc_transpo_length : forall m i j,
  length (nc_transpo m i j) = S m.
Proof.
intros m i j.
destruct (decomp_nc_transpo m i j) as [l Heq]; rewrite Heq.
apply compo_transpo_length.
Qed.

Lemma all_lt_nc_transpo : forall m i j,
  all_lt (nc_transpo m i j) (S m) = true.
Proof.
intros m i j.
destruct (decomp_nc_transpo m i j) as [l Heq]; rewrite Heq.
apply all_lt_compo_transpo.
Qed.

Definition compo_nc_transpo m := fold_right (fun i => app_nat_fun (nc_transpo m (fst i) (snd i))) (Id (S m)).

Lemma compo_nc_transpo_length : forall m l,
  length (compo_nc_transpo m l) = S m.
Proof.
  intros m; induction l.
  - apply seq_length.
  - simpl; rewrite app_nat_fun_length; rewrite nc_transpo_length; now try rewrite IHl.
Qed.

