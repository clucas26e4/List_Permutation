Require Import Lia.
Require Import PeanoNat.

Require Import Bool_more.
Require Import List_more.
Require Import List_more2.
Require Import List_nat.
Require Import Fun_nat.

(** ** Transposition *)
Definition transpo m n :=
  if n <? m then
  (*[0...n-1,n+1   , n ,   n+2 ... m ]*)
    Id n ++ (S n) :: n :: (incr_all (Id (S m - (2 + n))) (2 + n)) else Id (S m).

Lemma transpo_length : forall m n, length (transpo m n) = (S m).
Proof with try assumption; try reflexivity.
  intros m n.
  unfold transpo.
  case_eq (n <? m); intros Hcase.
  + rewrite app_length.
    simpl.
    rewrite incr_all_length.
    rewrite ? Id_length.
    apply Nat.ltb_lt in Hcase.
    lia.
  + apply Id_length.
Qed.

Lemma all_lt_transpo : forall m n, all_lt (transpo m n) (S m) = true.
Proof with try reflexivity; try assumption.
  intros m n.
  unfold transpo.
  case_eq (n <? m); intros Hcase.
  - apply Nat.ltb_lt in Hcase.
    rewrite all_lt_app.
    apply andb_true_intro; split.
    + apply all_lt_leq with n; [ | lia].
      apply all_lt_Id.
    + simpl.
      apply andb_true_intro; split; [ | apply andb_true_intro; split].
      * apply Nat.ltb_lt; lia.
      * apply Nat.ltb_lt; lia.
      * rewrite (Minus.le_plus_minus (S (S n)) (S m)) ; [ | lia].
        rewrite<- all_lt_incr_all.
        simpl.
        apply all_lt_Id.
  - apply all_lt_Id.
Qed.

Lemma all_distinct_transpo : forall m n, all_distinct (transpo m n) = true.
Proof with try reflexivity; try assumption.
  intros m n.
  unfold transpo.
  case_eq (n <? m); intros Hcase.
  - apply Nat.ltb_lt in Hcase.
    replace (S n) with (n + 1) by lia.
    replace n with (n + 0) at 3 by lia.
    rewrite incr_all_plus.
    change (n + 1 :: n + 0 :: incr_all (incr_all (Id (S m - (2 + n))) 2) n) with
        (incr_all (1 :: 0 :: incr_all (Id (S m - (2 + n))) 2) n).
    rewrite all_distinct_app...
    + apply all_lt_Id.
    + apply all_distinct_Id.
    + simpl; apply andb_true_intro; split; [ | apply andb_true_intro; split].
      * apply negb_true_iff.
        apply negb_In_incr_all...
        lia.
      * apply negb_true_iff.
        apply negb_In_incr_all...
        lia.
      * rewrite<- all_distinct_incr_all.
        apply all_distinct_Id.
  - apply all_distinct_Id.
Qed.

Fixpoint compo_transpo m l :=
  match l with
  | nil => Id (S m)
  | i :: l => app_nat_fun (transpo m i) (compo_transpo m l)
  end.

Lemma compo_transpo_length : forall m l, length (compo_transpo m l) = S m.
Proof.
  intros m; induction l.
  - apply Id_length.
  - simpl.
    unfold transpo.
    case_eq (a <? m); intro Hcase.
    + rewrite app_nat_fun_length.
      2:{ intros Heq.
          remember (compo_transpo m l).
          destruct l0; [ | inversion Heq].
          destruct m; [inversion Hcase | inversion IHl]. }
      rewrite app_length.
      simpl.
      rewrite incr_all_length.
      rewrite 2 Id_length.
      apply Nat.ltb_lt in Hcase.
      lia.
    + rewrite app_nat_fun_length.
      * apply Id_length.
      * remember (compo_transpo m l).
        destruct l0; try inversion IHl.
        intros Heq; inversion Heq.
Qed.

Lemma app_compo_transpo : forall m l1 l2,
  compo_transpo m (l1 ++ l2) = app_nat_fun (compo_transpo m l1) (compo_transpo m l2).
Proof with try reflexivity.
  intros m; induction l1; intros l2.
  - simpl.
    replace (0 :: seq 1 m) with (Id (length (compo_transpo m l2))).
    + symmetry; apply app_Id.
    + now rewrite compo_transpo_length.
  - simpl.
    rewrite asso_app_nat_fun.
    rewrite<- IHl1...
Qed.

(** ** nc_transpo *)
Definition nc_transpo m i j :=
  if (i <? j) && (j <=? m) then
 (*[0...i-1,j,               i+1...j-1             ,  i , j+1   .... m]*)
    Id i ++ j :: (incr_all (Id (j - (S i))) (S i)) ++ i :: (incr_all (Id (m - j)) (S j)) else Id (S m).

Lemma nc_transpo_length : forall m i j,
    length (nc_transpo m i j) = S m.
Proof with try reflexivity; try assumption.
  intros m i j.
  unfold nc_transpo.
  case_eq (i <? j); intros Hcase1; [case_eq (j <=? m); intros Hcase2 | ]; simpl.
  - repeat (rewrite app_length; simpl).
    rewrite ? incr_all_length.
    rewrite ? Id_length.
    apply Nat.ltb_lt in Hcase1.
    apply Nat.leb_le in Hcase2.
    lia.
  - rewrite seq_length...
  - rewrite seq_length...
Qed.

Lemma all_lt_nc_transpo : forall m i j,
    all_lt (nc_transpo m i j) (S m) = true.
Proof with try reflexivity; try assumption.
  intros m i j.
  unfold nc_transpo.
  case_eq (i <? j); intros Hcase1; [case_eq (j <=? m); intros Hcase2 | ]; unfold "&&".
  - apply Nat.ltb_lt in Hcase1; apply Nat.leb_le in Hcase2.
    rewrite all_lt_app.
    apply andb_true_intro; split.
    + apply all_lt_leq with i; [apply all_lt_Id | lia].
    + simpl.
      apply andb_true_intro; split; [apply Nat.ltb_lt; lia | ].
      rewrite all_lt_app.
      apply andb_true_intro; split.
      * rewrite (Minus.le_plus_minus (S i) (S m)); [ | lia].
        rewrite<- all_lt_incr_all.
        apply all_lt_leq with (j - S i); [apply all_lt_Id | lia].
      * simpl.
        apply andb_true_intro; split; [ apply Nat.ltb_lt; lia | ].
        rewrite (Minus.le_plus_minus (S j) (S m)); [ | lia].
        rewrite<- all_lt_incr_all.
        simpl.
        apply all_lt_Id.
  - apply all_lt_Id.
  - apply all_lt_Id.
Qed.

Lemma app_nc_transpo : forall {A} n i j (a : A) b l0 l1 l2,
    n = pred (length (l0 ++ a :: l1 ++ b :: l2)) ->
    i = length l0 ->
    j = length (l0 ++ a :: l1) ->
    i < j ->
    j <= n ->
    app_nat_fun (nc_transpo n i j) (l0 ++ a :: l1 ++ b :: l2) = (l0 ++ b :: l1 ++ a :: l2).
Proof with try reflexivity; try assumption.
  intros A n i j a b l0 l1 l2 Hlenn Hleni Hlenj Hij Hjn.
  unfold nc_transpo.
  replace (i <? j) with true by (symmetry; apply Nat.ltb_lt; apply Hij).
  replace (j <=? n) with true by (symmetry; apply Nat.leb_le; apply Hjn).
  change (if true && true
          then
            Id i ++
               j :: incr_all (Id (j - S i)) (S i) ++ i :: incr_all (Id (n - j)) (S j)
          else Id (S n))
    with (Id i ++
             j :: incr_all (Id (j - S i)) (S i) ++ i :: incr_all (Id (n - j)) (S j)).
  rewrite app_nat_fun_app.
  change (j :: incr_all (Id (j - S i)) (S i) ++ i :: incr_all (Id (n - j)) (S j))
    with ((j :: incr_all (Id (j - S i)) (S i)) ++ i :: incr_all (Id (n - j)) (S j)).
  rewrite app_nat_fun_app.
  replace (app_nat_fun (Id i) (l0 ++ a :: l1 ++ b :: l2)) with l0.
  2:{ rewrite app_nat_fun_left.
      - rewrite Hleni.
        rewrite app_Id...
      - rewrite Hleni.
        apply all_lt_Id. }
  change (j :: incr_all (Id (j - S i)) (S i)) with ((j :: nil) ++ incr_all (Id (j - S i)) (S i)).
  change (i :: incr_all (Id (n - j)) (S j)) with ((i :: nil) ++  incr_all (Id (n - j)) (S j)).
  rewrite ? app_nat_fun_app.
  replace (app_nat_fun (j :: nil) (l0 ++ a :: l1 ++ b :: l2)) with (b :: nil).
  2:{ rewrite Hlenj.
      replace (length (l0 ++ a :: l1) :: nil) with (incr_all (0 :: nil) (length (l0 ++ a :: l1))).
      2:{ simpl.
          rewrite Nat.add_0_r... }
      replace (l0 ++ a :: l1 ++ b :: l2)
         with ((l0 ++ a :: l1) ++ b :: l2) by (rewrite<- ? app_assoc; reflexivity).
      rewrite app_nat_fun_right... }
  replace ( app_nat_fun (incr_all (Id (j - S i)) (S i)) (l0 ++ a :: l1 ++ b :: l2)) with l1.
  2:{ rewrite Hleni at 2.
      replace (l0 ++ a :: l1 ++ b :: l2)
         with ((l0 ++ a :: nil) ++ l1 ++ b :: l2) by (rewrite<- ? app_assoc; reflexivity).
      replace (S (length l0)) with (length (l0 ++ a :: nil)) by (rewrite app_length; simpl; lia).
      replace (j - S i) with (length l1).
      2:{ rewrite app_length in Hlenj.
          simpl in Hlenj.
          lia. }
      rewrite app_nat_fun_right.
      - rewrite app_nat_fun_left.
        + rewrite app_Id...
        + apply all_lt_Id.
      - apply all_lt_leq with (length l1).
        + apply all_lt_Id.
        + rewrite app_length; lia. }
  replace (app_nat_fun (i :: nil) (l0 ++ a :: l1 ++ b :: l2)) with (a :: nil).
  2:{ rewrite Hleni.
      replace (length l0 :: nil) with (incr_all (0 :: nil) (length l0)).
      2:{ simpl.
          rewrite Nat.add_0_r... }
      rewrite app_nat_fun_right... }
  replace (app_nat_fun (incr_all (Id (n - j)) (S j)) (l0 ++ a :: l1 ++ b :: l2)) with l2...
  replace (S j) with (length (l0 ++ a :: l1 ++ (b :: nil))).
  2:{ repeat (rewrite app_length; simpl).
      repeat (rewrite app_length in Hlenj; simpl in Hlenj).
      lia. }
  replace (l0 ++ a :: l1 ++ b :: l2)
     with ((l0 ++ a :: l1 ++ b :: nil) ++ l2) by (repeat (rewrite<- app_assoc; simpl); reflexivity).
  replace (n - j) with (length l2).
  2:{ rewrite app_length in Hlenj.
      repeat (rewrite app_length in Hlenn; simpl in Hlenn).
      simpl in Hlenj.
      lia. }
  rewrite app_nat_fun_right.
  - rewrite app_Id...
  - apply all_lt_Id.
Qed.

Fixpoint compo_nc_transpo m l :=
  match l with
  | nil => Id (S m)
  | (i , j) :: l => app_nat_fun (nc_transpo m i j) (compo_nc_transpo m l)
  end.

Lemma compo_nc_transpo_length : forall m l,
    length (compo_nc_transpo m l) = S m.
Proof with try reflexivity; try assumption.
  intros m l.
  induction l.
  - simpl.
    rewrite seq_length...
  - destruct a; simpl.
    rewrite app_nat_fun_length.
    + apply nc_transpo_length.
    + intros H; rewrite H in IHl; inversion IHl.
Qed.

Lemma nc_transpo_decrease : forall m i j, i <> j -> i < S j -> S j <= m ->
  nc_transpo m i (S j) = app_nat_fun (app_nat_fun (transpo m j) (nc_transpo m i j)) (transpo m j).
Proof with try reflexivity; try assumption.
  intros m i j nHij HiSj HSjm.
  assert (i < j) as Hij by lia.
  assert (j <= m) as Hjm by lia.
  unfold nc_transpo.
  unfold transpo.
  replace (i <? S j) with true; [ | symmetry; apply Nat.ltb_lt]...
  replace (S j <=? m) with true; [ | symmetry; apply Nat.leb_le]...
  replace (i <? j) with true; [ | symmetry; apply Nat.ltb_lt]...
  replace (j <=? m) with true; [ | symmetry; apply Nat.leb_le]...
  replace (j <? m) with true ; [ | symmetry; apply Nat.ltb_lt]...
  simpl.
  rewrite ? app_nat_fun_app.
  replace (app_nat_fun (Id j)
                       (Id i ++
                           j :: incr_all (Id (j - S i)) (S i) ++ i :: incr_all (Id (m - j)) (S j)))
    with
      (Id i ++ j :: incr_all (Id (j - S i)) (S i)).
  2:{ transitivity (app_nat_fun (Id j) (Id i ++ j :: incr_all (Id (j - S i)) (S i))).
      - symmetry.
        replace j with (length (Id i ++ j :: incr_all (Id (j - S i)) (S i))) at 1.
        2:{ rewrite app_length.
            simpl; rewrite incr_all_length.
            rewrite? Id_length.
            lia. }
        apply app_Id.
      - replace (Id i ++ j :: incr_all (Id (j - S i)) (S i) ++ i :: incr_all (Id (m - j)) (S j))
           with ((Id i ++ j :: incr_all (Id (j - S i)) (S i)) ++ i :: incr_all (Id (m - j)) (S j))
          by (rewrite<- ? app_assoc; reflexivity).
        symmetry; rewrite app_nat_fun_left...
        rewrite app_length.
        simpl; rewrite incr_all_length.
        rewrite ? Id_length.
        apply all_lt_leq with j.
        + apply all_lt_Id.
        + lia. }
  rewrite ? app_nat_fun_app.
  replace (app_nat_fun (Id i) (Id j ++ S j :: j :: incr_all (Id (m - S j)) (S (S j)))) with (Id i).
  2:{ symmetry.
      rewrite app_nat_fun_left.
      2:{ rewrite Id_length.
          apply all_lt_leq with i; [apply all_lt_Id | lia]. }
      apply app_nat_fun_Id_r.
      apply all_lt_leq with i; [ | lia ].
      apply all_lt_Id. }
  change (S j :: j :: incr_all (Id (m - S j)) (S (S j)))
    with ((S j :: nil) ++ (j :: nil) ++ (incr_all (Id (m - S j)) (S (S j)))).
  rewrite ? app_nat_fun_app.
  replace (app_nat_fun (S j :: nil)
                       (Id i ++
                           j :: incr_all (Id (j - S i)) (S i) ++ i :: incr_all (Id (m - j)) (S j)))
    with
      (S j :: nil).
  2:{ symmetry.
      rewrite (Minus.le_plus_minus (length (Id i ++ j :: (incr_all (Id (j - S i)) (S i)))) (S j)) at 1.
      2:{ rewrite app_length.
          simpl.
          rewrite incr_all_length.
          rewrite ? Id_length.
          lia. }
      change (length (Id i ++ j :: incr_all (Id (j - S i)) (S i)) +
              (S j - length (Id i ++ j :: incr_all (Id (j - S i)) (S i))) :: nil)
        with (incr_all ((S j - length (Id i ++ j :: incr_all (Id (j - S i)) (S i))) :: nil)
                       (length (Id i ++ j :: incr_all (Id (j - S i)) (S i)))).
      replace (Id i ++ j :: incr_all (Id (j - S i)) (S i) ++ i :: incr_all (Id (m - j)) (S j))
        with ((Id i ++ j :: incr_all (Id (j - S i)) (S i)) ++ i :: incr_all (Id (m - j)) (S j))
        by (rewrite <- ? app_assoc; reflexivity).
      rewrite app_nat_fun_right.
      2:{ simpl.
          rewrite app_length.
          simpl.
          rewrite ? incr_all_length.
          rewrite ? Id_length.
          replace (match i + S (j - S i) with
                   | 0 => S j
                   | S l => j - l
                   end <? S (m - j)) with true...
          symmetry.
          apply Nat.ltb_lt.
          change (match i + S (j - S i) with
                  | 0 => S j
                  | S l => j - l
                  end)
            with (S j - (i + S (j - S i))).
          lia. }
      rewrite app_length; simpl; rewrite incr_all_length; rewrite ? Id_length.
      change (match i + S (j - S i) with
              | 0 => S j
              | S l => j - l
              end)
        with (S j - (i + S (j - S i))).
      replace (S j - (i  + S (j - S i))) with (S (j - (i + S (j - S i)))) by lia.
      replace (nth (j - (i + S (j - S i))) (incr_all (Id (m - j)) (S j)) i) with (S j)...
      replace (nth (j - (i + S (j - S i))) (incr_all (Id (m - j)) (S j)) i) with
          (nth (j - (i + S (j - S i))) (incr_all (Id (m - j)) (S j)) ((S j) + 0)).
      2:{ apply nth_indep.
          rewrite incr_all_length.
          rewrite Id_length.
          lia. }
      unfold incr_all.
      rewrite map_nth.
      rewrite nth_Id; lia. }
  replace (app_nat_fun (S j :: nil)
                       (Id j ++ (S j :: nil) ++ (j :: nil) ++ incr_all (Id (m - S j)) (S (S j))))
     with (j :: nil).
  2:{ replace (S j :: nil) with (incr_all (1 :: nil) (length (Id j))) at 1.
      2:{ simpl.
          rewrite Id_length.
          rewrite Nat.add_comm... }
      rewrite app_nat_fun_right... }
  replace (app_nat_fun (j :: nil)
                       (Id i ++
                           j :: incr_all (Id (j - S i)) (S i) ++ i :: incr_all (Id (m - j)) (S j))) with
      (i :: nil).
  2:{ replace (j :: nil) with (incr_all (0 :: nil) (length (Id i ++ j :: incr_all (Id (j - S i)) (S i)))).
      2:{ simpl.
          rewrite app_length.
          simpl.
          rewrite incr_all_length.
          rewrite 2 Id_length.
          replace (i + S (j - S i) + 0) with j by lia... }
      replace (Id i ++ j :: incr_all (Id (j - S i)) (S i) ++ i :: incr_all (Id (m - j)) (S j))
        with ((Id i ++ j :: incr_all (Id (j - S i)) (S i)) ++ i :: incr_all (Id (m - j)) (S j))
        by (rewrite <- ? app_assoc; reflexivity).
      rewrite app_nat_fun_right... }
  replace (app_nat_fun (i :: nil) (Id j ++ (S j :: nil) ++ (j :: nil) ++ incr_all (Id (m - S j)) (S (S j))))
     with (i :: nil).
  2:{ rewrite app_nat_fun_left.
      - rewrite app_nat_fun_Id_r...
        apply Nat.ltb_lt in Hij; apply andb_true_iff; split...
      - rewrite Id_length.
        simpl.
        replace (i <? j) with true...
        symmetry; rewrite Nat.ltb_lt... }
  replace (app_nat_fun (incr_all (Id (m - S j)) (S (S j)))
                       (Id i ++
                           j :: incr_all (Id (j - S i)) (S i) ++ i :: incr_all (Id (m - j)) (S j)))
    with (incr_all (Id (m - S j)) (S (S j))).
  2:{ replace (Id i ++
                  j :: incr_all (Id (j - S i)) (S i) ++ i :: incr_all (Id (m - j)) (S j))
        with
          ((Id i ++
               j :: incr_all (Id (j - S i)) (S i) ++ i :: (S j) :: nil) ++ incr_all (Id (m - (S j))) (S (S j))).
      2:{ rewrite <- ? app_assoc.
          simpl.
          rewrite <- ? app_assoc.
          simpl.
          replace (S j :: incr_all (Id (m - S j)) (S (S j)))
            with (incr_all (Id (m - j)) (S j))...
          destruct m ; [ exfalso; lia | ].
          replace (S m - j) with (S (m - j)) by lia.
          simpl.
          f_equal; [ lia | ].
          rewrite 2 incr_all_seq; f_equal. }
      replace (S (S j)) with (length (Id i ++ j :: incr_all (Id (j - S i)) (S i) ++ i :: S j :: nil)) at 2.
      2:{ rewrite app_length; simpl; rewrite app_length.
          rewrite incr_all_length; simpl.
          rewrite 2 Id_length.
          lia. }
      rewrite app_nat_fun_right.
      2:{ rewrite incr_all_length; rewrite Id_length.
          apply all_lt_Id. }
      replace (m - S j) with (length (incr_all (Id (m - S j)) (S (S j)))) at 2.
      - rewrite app_Id...
      - rewrite incr_all_length; rewrite Id_length... }
  replace (app_nat_fun (incr_all (Id (m - S j)) (S (S j)))
                       (Id j ++ (S j :: nil) ++ (j :: nil) ++ incr_all (Id (m - S j)) (S (S j))))
     with (incr_all (Id (m - S j)) (S (S j))).
  2:{ replace (Id j ++ (S j :: nil) ++ (j :: nil) ++ incr_all (Id (m - S j)) (S (S j)))
        with ((Id j ++ (S j :: j :: nil)) ++ incr_all (Id (m - S j)) (S (S j)))
        by (rewrite<- ? app_assoc; reflexivity).
      replace (S (S j)) with (length (Id j ++ S j :: j :: nil)) at 2.
      2:{ rewrite app_length; rewrite Id_length; simpl; lia. }
      rewrite app_nat_fun_right.
      2:{ rewrite incr_all_length; rewrite Id_length.
          apply all_lt_Id. }
      replace (m - S j) with (length (incr_all (Id (m - S j)) (S (S j)))) at 2.
      - rewrite app_Id...
      - rewrite incr_all_length; rewrite Id_length... }
  change (S j :: incr_all (Id (j - i)) (S i) ++ i :: incr_all (Id (m - S j)) (S (S j)))
   with ((S j :: incr_all (Id (j - i)) (S i)) ++ i :: incr_all (Id (m - S j)) (S (S j))).
  replace (S j :: incr_all (Id (j - i)) (S i)) with
      ((app_nat_fun (j :: incr_all (Id (j - S i)) (S i))
                    (Id j ++ (S j :: nil) ++ (j :: nil) ++ incr_all (Id (m - S j)) (S (S j)))) ++ (j :: nil)).
  { repeat (simpl; rewrite <- app_assoc)... }
  change (j :: incr_all (Id (j - S i)) (S i)) with ((j :: nil) ++ incr_all (Id (j - S i)) (S i)).
  rewrite app_nat_fun_app.
  replace (j :: nil) with (incr_all (0 :: nil) (length (Id j))) at 1.
  2:{ rewrite Id_length.
      simpl.
      rewrite Nat.add_0_r... }
  rewrite app_nat_fun_right...
  simpl.
  replace (incr_all (Id (j - i)) (S i))
     with (app_nat_fun (incr_all (Id (j - S i)) (S i))
                       (Id j ++ S j :: j :: incr_all (Id (m - S j)) (S (S j))) ++ j :: nil)...
  rewrite app_nat_fun_left.
  2:{ rewrite Id_length.
      rewrite (Minus.le_plus_minus (S i) j) at 2.
      2:{ lia. }
      rewrite<- all_lt_incr_all.
      apply all_lt_Id. }
  remember (j - S i); destruct n.
  + simpl.
    replace j with (S i) by lia.
    replace (S i - i) with 1 by lia.
    simpl.
    rewrite Nat.add_0_r...
  + rewrite app_nat_fun_Id_r.
    2:{ rewrite incr_all_seq; simpl.
        apply andb_true_iff; split; [ apply Nat.ltb_lt; lia | ].
        apply all_lt_leq with (S (S i) + n); [ | lia ].
        apply all_lt_seq. }
    replace (j - i) with (S (j - S i)) by lia.
    rewrite (Id_S (j - S i)).
    rewrite incr_all_app.
    rewrite Heqn.
    simpl.
    replace (S (i + (j - S i))) with j by lia...
Qed.

Lemma decomp_nc_transpo : forall m i j,
    { l & nc_transpo m i j = compo_transpo m l}.
Proof with try reflexivity; try assumption.
  intros m i j.
  case_eq (i <? j); intros Hij ; [case_eq (j <=? m) ; intros Hjm | ].
  - apply Nat.ltb_lt in Hij.
    apply Nat.leb_le in Hjm.
    revert i Hij Hjm; induction j; intros i Hij Hjm.
    + exfalso.
      lia.
    + case_eq (i =? j); intros Hcase.
      * split with (i :: nil).
        unfold nc_transpo.
        replace (i <? S j) with true by (symmetry; apply Nat.ltb_lt; apply Hij).
        replace (S j <=? m) with true by (symmetry; apply Nat.leb_le; apply Hjm).
        unfold "&&".
        unfold compo_transpo.
        unfold transpo.
        replace (i <? m) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite app_nat_fun_Id_r.
        2:{ rewrite ? fold_left_max_app.
            simpl.
            rewrite all_lt_app; apply andb_true_iff; split.
            - apply all_lt_leq with i; [ apply all_lt_Id | lia ].
            - do 2 (try (apply andb_true_iff; split)).
              + apply Nat.ltb_lt; lia.
              + apply Nat.ltb_lt; lia.
              + rewrite incr_all_seq; simpl.
                replace (S m) with (S (S i) + (m - S i)) by lia.
                apply all_lt_seq. }
        apply Nat.eqb_eq in Hcase.
        rewrite Hcase.
        rewrite Nat.sub_diag.
        simpl...
      * destruct (IHj i) as (l & Heq).
        -- apply Nat.eqb_neq in Hcase.
           lia.
        -- lia.
        -- split with (j :: l ++ j :: nil).
           change (j :: l ++ j :: nil) with ((j :: l) ++ j :: nil).
           rewrite app_compo_transpo.
           unfold compo_transpo; fold compo_transpo.
           replace (S m) with (length (transpo m j)).
           2:{ unfold transpo.
               case (j <? m).
               - rewrite app_length.
                 simpl.
                 rewrite incr_all_length.
                 rewrite 2 Id_length.
                 lia.
               - apply Id_length. }
           rewrite app_nat_fun_Id_r.
           2:{ rewrite transpo_length.
               apply all_lt_transpo. }
           rewrite nc_transpo_decrease...
           ++ rewrite Heq...
           ++ apply Nat.eqb_neq...
  - split with nil.
    unfold nc_transpo.
    rewrite Hij, Hjm...
  - split with nil.
    unfold nc_transpo.
    rewrite Hij...
Qed.

