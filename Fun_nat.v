Require Import Lia.
Require Import PeanoNat.

Require Import Bool_more.
Require Import List_more.
Require Import List_more2.
Require Import List_nat.



(* APP_NAT_FUN *)
Definition app_nat_fun_dflt {A} (p : list nat) (l : list A) a :=
  map (fun x => nth x l a) p.

Lemma app_nat_fun_dflt_indep {A} :
 forall p l (d d' : A), all_lt p (length l) = true -> app_nat_fun_dflt p l d = app_nat_fun_dflt p l d'.
Proof.
induction p; intros l d d' Hlt; simpl; f_equal; simpl in Hlt; apply andb_true_iff in Hlt.
- apply nth_indep, Nat.ltb_lt, Hlt.
- apply IHp, Hlt.
Qed.

Lemma app_nat_fun_dflt_nil {A} : forall p (d : A),
    app_nat_fun_dflt p nil d = map (fun _ => d) p.
Proof.
  intros p d; induction p; [ reflexivity | ].
  simpl; rewrite IHp.
  f_equal; destruct a; reflexivity.
Qed.

Definition app_nat_fun {A} (p : list nat) (l : list A) :=
  match l with
  | nil => nil
  | a :: l => app_nat_fun_dflt p (a :: l) a
  end.

Ltac app_nat_fun_unfold l1 l2 n a :=
  change (app_nat_fun (n :: l1) (a :: l2)) with ((nth n (a :: l2) a) :: (app_nat_fun l1 (a :: l2))) in *.

Lemma app_nat_fun_nil {A} : forall (l : list A),
    app_nat_fun nil l = nil.
Proof.
  destruct l; reflexivity.
Qed.

Lemma app_nat_fun_not_nil {A} : forall p (l : list A) a,
  l <> nil -> app_nat_fun p l = app_nat_fun_dflt p l (hd a l).
Proof.
  intros p l a Hnil.
  destruct l; [ contradiction Hnil | ]; reflexivity.
Qed.

Lemma app_nat_fun_app_nat_fun_dflt {A} : forall p (l : list A) d,
  all_lt p (length l) = true -> app_nat_fun p l = app_nat_fun_dflt p l d.
Proof.
intros p l d Hlen.
destruct l.
- destruct p.
  + reflexivity.
  + exfalso.
    apply andb_true_iff in Hlen as [Hlen _].
    apply Nat.ltb_lt in Hlen; simpl in Hlen; lia.
- simpl.
  now apply app_nat_fun_dflt_indep.
Qed.

Lemma app_nat_fun_middle {A} : forall l1 l2 (a : A) p,
    app_nat_fun (length l1 :: p) (l1 ++ a :: l2) = a :: (app_nat_fun p (l1 ++ a :: l2)).
Proof with try reflexivity; try assumption.
  destruct l1...
  intros l2 a0 p.
  change (app_nat_fun (length (a :: l1) :: p) ((a :: l1) ++ a0 :: l2))
    with ((nth (length (a :: l1)) ((a :: l1) ++ a0 :: l2) a) :: app_nat_fun p ((a :: l1) ++ a0 :: l2)).
  replace a0 with (nth (length (a :: l1)) ((a :: l1) ++ a0 :: l2) a);
    f_equal; apply nth_middle.
Qed.

Lemma app_nat_fun_length {A} : forall f (l : list A), l <> nil -> length (app_nat_fun f l) = length f.
Proof.
  intros f l Hnnil.
  destruct l; [ exfalso; apply Hnnil; reflexivity | apply map_length ].
Qed.

Lemma app_nat_fun_dflt_shift {A} : forall la lb (a : A) p d, length (la ++ lb) <> 0 ->
  app_nat_fun_dflt (shift p (length la)) (la ++ a :: lb) d = app_nat_fun_dflt p (la ++ lb) d.
Proof.
  intros la lb a p d Hlen.
  induction p; simpl; [ reflexivity | ].
  rewrite <- IHp.
  case_eq (a0 <? length la); intros Ha0; subst; list_simpl; f_equal.
  - rewrite 2 app_nth1; try (apply Nat.ltb_lt; assumption).
    reflexivity.
  - apply Nat.ltb_ge in Ha0.
    rewrite 2 app_nth2; try lia.
    replace (S a0 - length la) with (S (a0 - length la)) by lia.
    reflexivity.
Qed.

Lemma app_nat_fun_shift {A} : forall la lb (a : A) p
                                     (H : length (la ++ lb) <> 0)
                                     (Halt : all_lt p (length (la ++ lb)) = true),
    app_nat_fun (shift p (length la)) (la ++ a :: lb) = app_nat_fun p (la ++ lb).
Proof.
intros la lb a p Hlen Hlt.
rewrite 2 app_nat_fun_not_nil with _ _ a.
- replace (app_nat_fun_dflt p (la ++ lb) (hd a (la ++ lb)))
     with (app_nat_fun_dflt p (la ++ lb) (hd a (la ++ a :: lb))).
  + apply app_nat_fun_dflt_shift; assumption.
  + apply app_nat_fun_dflt_indep; assumption.
- intros Heq; apply Hlen; rewrite Heq; reflexivity.
- intros Heq; destruct la; inversion Heq.
Qed.

Lemma app_nat_fun_dflt_downshift {A} : forall la lb (a : A) p d, In_nat_bool (length la) p = false ->
  app_nat_fun_dflt p (la ++ a :: lb) d = app_nat_fun_dflt (downshift p (length la)) (la ++ lb) d.
Proof.
  intros la lb a p d Hlen.
  induction p; simpl; [ reflexivity | ].
  simpl in Hlen; apply orb_false_iff in Hlen.
  rewrite IHp; [ | apply Hlen ].
  case_eq (a0 <? length la); intros Ha0; subst; list_simpl; f_equal.
  - rewrite 2 app_nth1; try (apply Nat.ltb_lt; assumption).
    reflexivity.
  - assert (length la < a0) as Ha.
    { apply Nat.ltb_ge in Ha0.
      destruct Hlen as [Hlen _].
      apply Nat.eqb_neq in Hlen; lia. }
    rewrite app_nth2; try lia.
    assert (beq_nat a0 (length la) = false) as Ha1 by (apply Nat.eqb_neq; lia); rewrite Ha1.
    simpl; f_equal.
    rewrite app_nth2; try lia.
    replace (Init.Nat.pred a0 - length la) with (Init.Nat.pred (a0 - length la)) by lia.
    assert (a0 - length la > 0) as Hnz by lia.
    remember (a0 - length la) as n; clear - Hnz.
    destruct n; [ inversion Hnz | reflexivity ].
Qed.

Lemma app_nat_fun_downshift {A} : forall la lb (a : A) p
                                         (nHin : In_nat_bool (length la) p = false)
                                         (Halt : all_lt p (S (length (la ++ lb))) = true),
    app_nat_fun p (la ++ a :: lb) = app_nat_fun (downshift p (length la)) (la ++ lb).
Proof.
intros la lb a p Hlen Hlt.
case_eq p.
- intros Hp; subst.
  rewrite 2 app_nat_fun_nil; reflexivity.
- intros x l Hl; rewrite <- Hl in *.
  rewrite 2 app_nat_fun_not_nil with _ _ a.
  + replace (app_nat_fun_dflt p (la ++ a :: lb) (hd a (la ++ a :: lb)))
       with (app_nat_fun_dflt p (la ++ a :: lb) (hd a (la ++ lb))).
    * apply app_nat_fun_dflt_downshift; assumption.
    * apply app_nat_fun_dflt_indep.
      rewrite app_length in *; simpl.
      rewrite <- Hlt; f_equal; lia.
  + intros Heq; subst.
    rewrite Heq in Hlt; simpl in Hlt.
    apply app_eq_nil in Heq.
    destruct Heq as [Heq _]; subst; simpl in Hlen.
    apply andb_true_iff in Hlt.
    apply orb_false_iff in Hlen.
    destruct Hlt as [Hlt _]; destruct Hlen as [Hlen _].
    destruct x; [ inversion Hlen | inversion Hlt].
  + intros Heq; destruct la; inversion Heq.
Qed.

Lemma app_nat_fun_dflt_downshift_commu : forall l f k d,
  all_lt f (length l) = true ->
  In_nat_bool k l = false ->
  app_nat_fun_dflt f (downshift l k) d = downshift (app_nat_fun_dflt f l d) k.
Proof.
intros l f; revert l.
induction f; intros l k d Hlt Hnin; [ reflexivity | ].
simpl in Hlt; apply andb_true_iff in Hlt; destruct Hlt as [Hlt Hlt'].
simpl; case_eq (nth a l d <? k); intros Hlt2.
- rewrite IHf; [ f_equal | assumption | assumption ].
  apply Nat.ltb_lt in Hlt2.
  apply nth_downshift_lt; assumption.
- apply Nat.ltb_lt in Hlt; apply Nat.ltb_ge in Hlt2.
  replace (beq_nat (nth a l d) k) with false; simpl.
  + rewrite IHf; [ f_equal | assumption | assumption ].
    apply nth_downshift_ge; assumption.
  + clear - Hlt Hnin; revert a Hlt; induction l; intros b Hlt.
    * exfalso; simpl in Hlt; lia.
    * simpl in Hnin; apply orb_false_iff in Hnin; destruct Hnin as [Hnin1 Hnin2].
      destruct b; simpl.
      -- symmetry; apply Nat.eqb_neq; intros H; subst; apply Nat.eqb_neq in Hnin1; auto.
      -- simpl in Hlt; apply IHl; [assumption | lia].
Qed.

Lemma app_nat_fun_downshift_commu : forall a l f k,
  In_nat_bool k (a :: l) = false ->
  all_lt f (length (a :: l)) = true ->
  app_nat_fun f (downshift (a :: l) k) = downshift (app_nat_fun f (a :: l)) k.
Proof.
intros a l f k Hlen Hnin.
rewrite 2 app_nat_fun_not_nil with _ _ 0.
- rewrite app_nat_fun_dflt_downshift_commu; auto.
  f_equal; apply app_nat_fun_dflt_indep; assumption.
- intros H; inversion H.
- intros H; simpl in H.
  simpl in Hlen; apply orb_false_iff in Hlen; destruct Hlen as [Hlen _].
  case_eq (a <? k); intros Hlt; rewrite Hlt in H.
  + inversion H.
  + replace (beq_nat a k) with false in H; [ inversion H | ].
    symmetry; apply Nat.eqb_neq; intros H'; rewrite H' in Hlen; apply Nat.eqb_neq in Hlen; now apply Hlen.
Qed.

Lemma asso_app_nat_fun_dflt {A} : forall l1 l2 (l3 : list A) n d,
   app_nat_fun_dflt (app_nat_fun_dflt l1 l2 n) l3 d
 = app_nat_fun_dflt l1 (app_nat_fun_dflt l2 l3 d) (nth n l3 d).
Proof.
intros l1 l2 l3 n d; unfold app_nat_fun_dflt.
rewrite map_map.
apply map_ext; intros x.
revert l2; induction x; intros l2; destruct l2; simpl; try reflexivity.
rewrite IHx; reflexivity.
Qed.

Lemma asso_app_nat_fun {A} : forall l1 l2 (l3 : list A),
    app_nat_fun (app_nat_fun l1 l2) l3 = app_nat_fun l1 (app_nat_fun l2 l3).
Proof.
intros l1 l2 l3.
destruct l3; [ reflexivity | ].
destruct l2; [ reflexivity | ].
unfold app_nat_fun.
remember (app_nat_fun_dflt (n :: l2) (a :: l3) a) as l.
destruct l.
- exfalso.
  destruct n; simpl in Heql; inversion Heql.
- rewrite Heql.
  replace a0 with (nth n (a :: l3) a) by (destruct n; simpl in Heql; simpl; now inversion Heql).
  apply asso_app_nat_fun_dflt.
Qed.

Lemma app_nat_fun_dflt_right {A} : forall (l1 l2 : list A) f d,
    all_lt f (length l2) = true ->
    app_nat_fun_dflt (incr_all f (length l1)) (l1 ++ l2) d = app_nat_fun_dflt f l2 d.
Proof.
intros l1 l2 f; revert l1 l2; induction f; intros l1 l2 d Hlen; [ reflexivity | ].
simpl in Hlen; apply andb_true_iff in Hlen as [Hlen1 Hlen2]; apply Nat.ltb_lt in Hlen1.
simpl; rewrite IHf; [ | assumption ].
f_equal.
rewrite app_nth2; f_equal; lia.
Qed.

Lemma app_nat_fun_right {A} : forall (l1 l2 : list A) f,
    all_lt f (length l2) = true ->
    app_nat_fun (incr_all f (length l1)) (l1 ++ l2) = app_nat_fun f l2.
Proof.
intros l1 l2 f Hlen.
induction l1; simpl.
- rewrite incr_all_0; reflexivity.
- change (S (length l1)) with (length (a :: l1)).
  rewrite app_comm_cons.
  rewrite app_nat_fun_dflt_right; [ | assumption ].
  symmetry; apply app_nat_fun_app_nat_fun_dflt; assumption.
Qed.

Lemma app_nat_fun_dflt_left {A} : forall (l1 l2 : list A) f d1 d2,
    all_lt f (length l1) = true ->
    app_nat_fun_dflt f (l1 ++ l2) d1 = app_nat_fun_dflt f l1 d2.
Proof.
intros l1 l2 f d1 d2 Hlen.
unfold app_nat_fun_dflt.
apply map_ext_in; intros x Hin.
assert (x < length l1) as Hx.
{ revert Hlen Hin; induction f; intros Hlen Hin; inversion Hin; subst.
  - apply andb_true_iff in Hlen as [Hlen _].
    now apply Nat.ltb_lt.
  - apply IHf; try assumption.
    now apply andb_true_iff in Hlen as [_ Hlen]. }
rewrite app_nth1; [ | apply Hx ].
apply nth_indep, Hx.
Qed.

Lemma app_nat_fun_left {A} : forall (l1 l2 : list A) f,
    all_lt f (length l1) = true ->
    app_nat_fun f (l1 ++ l2) = app_nat_fun f l1.
Proof.
intros l1 l2 f Hlen.
destruct l2; [ list_simpl; reflexivity | ].
rewrite 2 app_nat_fun_app_nat_fun_dflt with _ _ a.
- now apply app_nat_fun_dflt_left.
- assumption.
- apply all_lt_leq with (length l1); [ assumption | rewrite app_length; lia ].
Qed.

Lemma app_nat_fun_dflt_app {A} : forall (l : list A) f1 f2 d,
  app_nat_fun_dflt (f1 ++ f2) l d = app_nat_fun_dflt f1 l d ++ app_nat_fun_dflt f2 l d.
Proof.
intros l f1 f2 d; apply map_app.
Qed.

Lemma app_nat_fun_app {A} : forall (l : list A) f1 f2,
    app_nat_fun (f1 ++ f2) l = app_nat_fun f1 l ++ app_nat_fun f2 l.
Proof.
intros l f1 f2.
destruct l; [ reflexivity | ].
apply app_nat_fun_dflt_app.
Qed.

Lemma append_fun_eq {A} : forall (l1 l2 : list A) f1 f2,
    all_lt f1 (length l1) = true ->
    all_lt f2 (length l2) = true ->
    app_nat_fun (f1 ++ (incr_all f2 (length l1))) (l1 ++ l2) = (app_nat_fun f1 l1) ++ (app_nat_fun f2 l2).
Proof.
intros l1 l2 f1 f2 Hlen1 Hlen2.
rewrite app_nat_fun_app; f_equal.
- now apply app_nat_fun_left.
- now apply app_nat_fun_right.
Qed.

Lemma app_nat_fun_downshift_shift : forall l f n0 n,
    all_distinct l = true ->
    all_distinct f = true ->
    all_lt f (pred (length l)) = true ->
    n < length l ->
    app_nat_fun f (downshift l (nth n l n0)) = downshift (app_nat_fun (shift f n) l) (nth n l n0).
Proof with try reflexivity; try assumption.
  intros l f n0 n Had Hadf Hal Hlen.
  destruct (@nth_split _ n l n0) as (la & (lb & (Heql & Hlenla)))...
  pattern l at 1 3.
  rewrite Heql.
  pattern n at 4.
  rewrite<- Hlenla.
  rewrite Heql in Hal.
  destruct la.
  - destruct lb.
    { destruct n; try now inversion Hlenla.
      change (length nil) with 0.
      rewrite? app_nil_l.
      clear.
      rewrite downshift_eq.
      induction f...
      change (shift (a :: f) 0) with (S a :: (shift f 0)).
      app_nat_fun_unfold (shift f 0) (@nil nat) (S a) (nth 0 l n0).
      replace (nth (S a) (nth 0 l n0 :: nil) (nth 0 l n0)) with (nth 0 l n0).
      2:{ destruct a... }
      rewrite downshift_eq... }
    rewrite <- Hlenla.
    rewrite app_nat_fun_shift...
    2:{ intros H; inversion H. }
    rewrite 2 app_nil_l.
    rewrite downshift_eq.
    apply app_nat_fun_downshift_commu...
    apply all_distinct_right with (@nil nat).
    rewrite Hlenla.
    rewrite <- Heql...
  - simpl in Hal.
    rewrite <- Hlenla.
    rewrite app_nat_fun_shift.
    + rewrite downshift_app.
      rewrite downshift_eq.
      rewrite<- downshift_app.
      change ((n1 :: la) ++ lb) with (n1 :: la ++ lb).
      rewrite app_nat_fun_downshift_commu...
      * change (n1 :: la ++ lb) with ((n1 :: la) ++ lb).
        rewrite In_nat_bool_app.
        apply orb_false_iff.
        split.
        -- apply all_distinct_left with lb.
           rewrite Hlenla; rewrite<- Heql...
        -- apply all_distinct_right with (n1 :: la).
           rewrite Hlenla; rewrite<- Heql...
      * simpl.
        rewrite app_length in Hal |- *.
        simpl in Hal.
        rewrite Nat.add_succ_r in Hal...
    + intros H; inversion H.
    + simpl.
      rewrite app_length in Hal |- * .
      simpl in Hal.
      rewrite Nat.add_succ_r in Hal...
Qed.

Lemma app_nat_fun_incr_all : forall n l p,
    app_nat_fun p (incr_all l n) = incr_all (app_nat_fun p l) n.
Proof with try reflexivity.
  intros n l p.
  destruct l...
  induction p...
  change (incr_all (n0 :: l) n) with (n + n0 :: incr_all l n).
  app_nat_fun_unfold p (incr_all l n) a (n + n0).
  app_nat_fun_unfold p l a n0.
  change (n + n0 :: incr_all l n) with (incr_all (n0 :: l) n).
  rewrite IHp.
  change (incr_all (nth a (n0 :: l) n0 :: app_nat_fun p (n0 :: l)) n)
    with (n + nth a (n0 :: l) n0 :: incr_all (app_nat_fun p (n0 :: l)) n).
  replace (n + nth a (n0 :: l) n0) with (nth a (incr_all (n0 :: l) n) (n + n0))...
  apply nth_incr_all.
Qed.

Lemma In_nat_bool_shift_false : forall l f n0 n,
    all_lt f (pred (length l)) = true ->
    n < length l ->
    all_distinct l = true ->
    In_nat_bool (nth n l n0) (app_nat_fun (shift f n) l) = false.
Proof with try reflexivity; try assumption.
  intros l f n0 n Hal Hlen Had.
  destruct l; try now inversion Hlen.
  induction f...
  unfold shift.
  change ((fix shift (l0 : list nat) (k : nat) {struct l0} : 
             list nat :=
             match l0 with
             | nil => nil
             | n2 :: l1 =>
               if n2 <? k then n2 :: shift l1 k else S n2 :: shift l1 k
             end) f n)
    with (shift f n).
  simpl in Hal.
  apply andb_prop in Hal as (Hlt & Hal).
  case_eq (a <? n); intros Hlt'.
  - app_nat_fun_unfold l (shift f n) n1 a.
    apply orb_false_iff.
    split ; [ | apply IHf]...
    case_eq (nth n (n1 :: l) n0 =? nth a (n1 :: l) n1); intros Heq...
    exfalso.
    apply Nat.ltb_lt in Hlt'.
    apply (Nat.lt_neq a n)...
    symmetry.
    apply Nat.eqb_eq in Heq.
    replace (nth a (n1 :: l) n1) with (nth a (n1 :: l) n0) in Heq.
    2:{ apply nth_indep.
        simpl.
        apply Nat.ltb_lt in Hlt.
        lia. }
    apply cond_all_distinct_inv with (n1 :: l) n0...
    simpl.
    apply Nat.ltb_lt in Hlt.
    lia.
  - app_nat_fun_unfold l (shift f n) n1 (S a).
    apply orb_false_iff.
    split ; [ | apply IHf]...
    assert (n <> S a).
    { apply Nat.ltb_nlt in Hlt'.
      lia. }
    replace (nth (S a) (n1 :: l) n1) with (nth (S a) (n1 :: l) n0).
    2:{ apply nth_indep.
        simpl.
        apply Nat.ltb_lt... }
    case_eq (nth n (n1 :: l) n0 =? nth (S a) (n1 :: l) n0); intros Heq...
    exfalso.
    apply H.
    apply Nat.eqb_eq in Heq.
    apply cond_all_distinct_inv with (n1 :: l) n0...
    simpl; apply Nat.ltb_lt...
Qed.

Lemma app_nat_fun_map {A B} : forall (f : A -> B) l p,
    app_nat_fun p (map f l) = map f (app_nat_fun p l).
Proof with try reflexivity.
  intros f l p.
  destruct l...
  induction p...
  rewrite map_cons.
  app_nat_fun_unfold p (map f l) a0 (f a).
  rewrite<- ? map_cons.
  rewrite IHp.
  app_nat_fun_unfold p l a0 a.
  change (map f (nth a0 (a :: l) a :: app_nat_fun p (a :: l)))
    with (f (nth a0 (a :: l) a) :: map f (app_nat_fun p (a :: l))).
  rewrite map_nth...
Qed.

(* ID *)
(* TODO vs (seq 0) ? *)
Fixpoint Id n :=
  match n with
  | 0 => nil
  | (S n) => 0 :: (incr_all (Id n) 1)
  end.

Lemma Id_max : forall n k, fold_left max (Id (S n)) k = max n k.
Proof with try reflexivity; try assumption.
  induction n; intros k.
  - destruct k...
  - change (fold_left max (Id (S (S n))) k) with (fold_left max (incr_all (Id (S n)) 1) (max k 0)).
    rewrite incr_all_max.
    2:{ simpl.
        intro H; inversion H. }
    rewrite IHn.
    lia.
Qed.

Lemma Id_incr_all_Id : forall n m,
    Id n ++ (incr_all (Id m) n) = Id (n + m).
Proof with try reflexivity; try assumption.
  induction n; intros m.
  - rewrite incr_all_0...
  - simpl.
    replace (incr_all (Id (n + m)) 1) with (incr_all (Id n) 1 ++ incr_all (Id m) (S n))...
    replace (S n) with (n + 1) by lia.
    rewrite incr_all_plus.
    rewrite<- incr_all_app.
    rewrite IHn...
Qed.  

Lemma Id_length : forall n, length (Id n) = n.
Proof with try reflexivity; try assumption.
  induction n...
  simpl; rewrite incr_all_length; rewrite IHn...
Qed.

Lemma Id_S : forall n, Id (S n) = Id n ++ n :: nil.
Proof with try reflexivity; try assumption.
  induction n...
  simpl.
  change (1 :: incr_all (incr_all (Id n) 1) 1) with (incr_all (Id (S n)) 1).
  rewrite IHn.
  rewrite incr_all_app...
Qed.

Lemma nth_Id : forall i n a0, i < n -> nth i (Id n) a0 = i.
Proof with try reflexivity.
  intros i n a0.
  revert n.
  induction i; intros n Hlt.
  - destruct n...
    exfalso.
    lia.
  - destruct n.
    + exfalso.
      lia.
    + simpl.
      replace (nth i (incr_all (Id n) 1) a0)
        with
          (nth i (incr_all (Id n) 1) (1 + a0)).
      2:{ apply nth_indep...
          rewrite incr_all_length.
          rewrite Id_length.
          lia. }
      unfold incr_all.
      rewrite map_nth.
      rewrite IHi...
      lia.
Qed.

Lemma In_Id_lt : forall n x, In x (Id n) -> x < n.
Proof.
enough (forall n k x, In x (incr_all (Id n) k) -> x < n + k).
{ intros n x Hin.
  replace n with (n + 0) by lia; apply H.
  rewrite incr_all_0; assumption. }
induction n; intros k x Hin; inversion Hin; try lia.
replace (S n + k) with (n + S k) by lia.
apply IHn.
change (S k) with (1 + k).
rewrite incr_all_plus; assumption.
Qed.

Lemma all_lt_Id : forall n, all_lt (Id n) n = true.
Proof with try reflexivity; try assumption.
  induction n...
  simpl; rewrite<- all_lt_incr_all...
Qed.

Lemma all_distinct_Id : forall n,
    all_distinct (Id n) = true.
Proof with try reflexivity; try assumption.
  induction n...
  apply andb_true_intro; split.
  + apply negb_true_iff.
    apply negb_In_incr_all.
    apply Nat.lt_0_1.
  + rewrite<- all_distinct_incr_all...
Qed.

Lemma nth_correct_map_Id {A} : forall a1 a2 a3 (l : list A),
    map (fun x => nth x (a1 :: l) a2) (Id (S (length l))) = map (fun x => nth x (a1 :: l) a3) (Id (S (length l))).
Proof with try reflexivity; try assumption.
  intros a1 a2 a3 l; revert a1 a2 a3; induction l; intros a1 a2 a3...
  change (map (fun x : nat => nth x (a1 :: a :: l) a2) (Id (S (length (a :: l)))))
    with (a1 :: map (fun x : nat => nth x (a1 :: a :: l) a2) (incr_all (Id (S (length l))) 1)).
  change (map (fun x : nat => nth x (a1 :: a :: l) a3) (Id (S (length (a :: l)))))
    with (a1 :: map (fun x : nat => nth x (a1 :: a :: l) a3) (incr_all (Id (S (length l))) 1)).
  rewrite 2 map_incr_all.
  change (map (fun x : nat => nth (1 + x) (a1 :: a :: l) a2) (Id (S (length l))))
    with (map (fun x : nat => nth x (a :: l) a2) (Id (S (length l)))).
  change (map (fun x : nat => nth (1 + x) (a1 :: a :: l) a3) (Id (S (length l))))
    with (map (fun x : nat => nth x (a :: l) a3) (Id (S (length l)))).
  rewrite IHl with a a2 a3...
Qed.

Lemma app_Id {A} : forall (l : list A),
    app_nat_fun (Id (length l)) l = l.
Proof with try reflexivity; try assumption.
  induction l...
  simpl; unfold app_nat_fun_dflt.
  rewrite map_incr_all.
  simpl; f_equal.
  unfold app_nat_fun, app_nat_fun_dflt in IHl; destruct l...
  etransitivity; [ | apply IHl ].
  apply map_ext_in; intros x Hin.
  now apply nth_indep, In_Id_lt.
Qed.

Lemma app_nat_fun_Id_r : forall f k, fold_left max f 0 < k -> app_nat_fun f (Id k) = f.
Proof with try assumption; try reflexivity.
  intros f k Hlt.
  unfold app_nat_fun; unfold app_nat_fun_dflt.
  destruct k.
  { exfalso.
    lia. }
  change (Id (S k)) with (0 :: incr_all (Id k) 1).
  unfold app_nat_fun.
  change (0 :: incr_all (Id k) 1) with (Id (S k)).
  apply list_ext.
  - rewrite map_length... 
  - intros n0 a0.
    case_eq (n0 <? length f); intro Hcase.
    + replace (nth n0 (map (fun x : nat => nth x (Id (S k)) 0) f) a0)
         with (nth n0 (map (fun x : nat => nth x (Id (S k)) 0) f) (nth 0 (Id (S k)) 0)).
      2:{ apply nth_indep.
          rewrite map_length.
          apply Nat.ltb_lt... }
      change (nth 0 (Id (S k)) 0) with ((fun x => nth x (Id (S k)) 0) 0).
      rewrite map_nth.
      rewrite nth_Id.
      * apply nth_indep.
        apply Nat.ltb_lt...
      * apply cond_all_lt_inv.
        -- apply Nat.ltb_lt...
        -- apply all_lt_max with 0...
    + transitivity a0.
      * apply nth_overflow.
        rewrite map_length.
        apply Nat.ltb_nlt in Hcase.
        lia.
      * symmetry.
        apply nth_overflow.
        apply Nat.ltb_nlt in Hcase.
        lia.
Qed.

(* CFUN *)
Definition cfun n m := incr_all (Id m) n ++ (Id n).

Lemma cfun_length : forall n m, length (cfun n m) = n + m.
Proof with try reflexivity.
  intros.
  unfold cfun.
  rewrite app_length; rewrite incr_all_length; rewrite 2 Id_length.
  apply Nat.add_comm.
Qed.

Lemma all_lt_cfun : forall n m, all_lt (cfun n m) (n + m) = true.
Proof with try assumption; try reflexivity.
  intros n m.
  unfold cfun.
  rewrite all_lt_app.
  apply andb_true_intro; split.
  - rewrite <- all_lt_incr_all.
    apply all_lt_Id.
  - apply all_lt_leq with n; [apply all_lt_Id | lia].
Qed.

Lemma all_distinct_cfun : forall n m, all_distinct (cfun n m) = true.
Proof with try assumption; try reflexivity.
  intros n m.
  unfold cfun.
  rewrite all_distinct_app_commu.
  apply all_distinct_app; try apply all_lt_Id; try apply all_distinct_Id.
Qed.

Lemma app_cfun_eq {A} : forall (l1 : list A) l2,
    app_nat_fun (cfun (length l1) (length l2)) (l1 ++ l2) = l2 ++ l1.
Proof with try reflexivity; try assumption.
  intros l1 l2; revert l1.
  induction l2; intros l1.
  - simpl.
    change (cfun (length l1) 0) with (Id (length l1)).
    rewrite app_nil_r.
    rewrite app_Id...
  - simpl.
    unfold cfun.
    change (Id (S (length l2))) with (0 :: (incr_all (Id (length l2)) 1)).
    replace (incr_all (0 :: incr_all (Id (length l2)) 1) (length l1))
       with ((length l1) :: incr_all (incr_all (Id (length l2)) (length l1)) 1).
    2:{ simpl.
        rewrite Nat.add_0_r.
        rewrite incr_all_incr_all... }
    simpl.
    rewrite app_nat_fun_middle.
    replace (app_nat_fun (incr_all (incr_all (Id (length l2)) (length l1)) 1 ++ Id (length l1)) (l1 ++ a :: l2))
       with (l2 ++ l1)...
    rewrite app_nat_fun_downshift.
    + rewrite downshift_app.
      rewrite<- incr_all_plus.
      replace (length l1 + 1) with (S (length l1)) by lia.
      rewrite downshift_incr_all.
      rewrite<- IHl2.
      replace (downshift (Id (length l1)) (length l1)) with (Id (length l1))...
      rewrite downshift_if_all_lt...
      apply all_lt_Id.
    + rewrite In_nat_bool_app.
      apply orb_false_iff.
      split.
      * rewrite<- incr_all_plus.
        apply negb_In_incr_all.
        lia.
      * apply all_lt_In_nat_bool_false.
        apply all_lt_Id.
    + rewrite all_lt_app.
      apply andb_true_iff.
      split.
      * rewrite<- incr_all_plus.
        replace (length l1 + 1) with (S (length l1)) by lia.
        rewrite app_length.
        change (S (length l1 + length l2)) with ((S (length l1)) + length l2).
        rewrite<- all_lt_incr_all.
        apply all_lt_Id.
      * apply all_lt_leq with (length l1).
        -- apply all_lt_Id.
        -- rewrite app_length.
           lia.
Qed.

Lemma cfun_inv : forall n m, app_nat_fun (cfun n m) (cfun m n) = Id (m + n).
Proof with try reflexivity.
  intros n m; unfold cfun.
  rewrite app_nat_fun_app.
  pattern n at 1.
  replace n with (length (incr_all (Id n) m)).
  2:{ rewrite incr_all_length; rewrite Id_length... }
  rewrite app_nat_fun_right.
  2:{ rewrite Id_length; apply all_lt_Id. }
  pattern m at 1.
  replace m with (length (Id m)) by apply Id_length.
  rewrite app_Id.
  rewrite app_nat_fun_left.
  2:{ rewrite incr_all_length; rewrite Id_length; apply all_lt_Id. }
  rewrite app_nat_fun_incr_all.
  pattern n at 1.
  replace n with (length (Id n)) by apply Id_length.
  rewrite app_Id.
  apply Id_incr_all_Id.
Qed.

Lemma cfun_arg_inj : forall n1 n2 m1 m2,
    cfun (S n1) (S m1) = cfun (S n2) (S m2) ->
    n1 = n2 /\ m1 = m2.
Proof with try reflexivity.
  induction n1; intros n2 m1 m2 Heq.
  - unfold cfun in Heq.
    destruct n2, m1, m2; simpl in Heq; try now inversion Heq.
    split...
    inversion Heq.
    apply app_inv_tail in H0.
    clear Heq; rename H0 into Heq.
    revert m2 Heq; induction m1; intros m2 Heq; destruct m2; try now inversion Heq.
    rewrite IHm1 with m2...
    simpl in Heq.
    inversion Heq.
    clear Heq; rename H0 into Heq.
    apply incr_all_inj in Heq.
    apply Heq.
  - destruct n2.
    + unfold cfun in Heq.
      simpl in Heq.
      inversion Heq.
    + unfold cfun in Heq.
      assert (n1 = n2) as Heqn.
      { inversion Heq.
        rewrite<- 2 plus_n_O in H0.
        apply H0. }
      subst.
      apply app_inv_tail in Heq.
      apply incr_all_inj in Heq.
      split...
      apply Nat.succ_inj.
      transitivity (length (Id (S m1))).
      { rewrite Id_length... }
      transitivity (length (Id (S m2))).
      { rewrite Heq... }
      apply Id_length.
Qed.

