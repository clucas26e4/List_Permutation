Require Import Lia.
Require Import PeanoNat.
Require Import EqNat.
Require Import Injective.

Require Import Bool_more.
Require Import List_more.
Require Import List_more2.
Require Import List_nat.

(* APP_NAT_FUN *)
Definition app_nat_fun {A} (p : list nat) (l : list A) :=
  match l with
  | nil => nil
  | a :: l => map (fun x => nth x (a :: l) a) p
  end.

Ltac app_nat_fun_unfold l1 l2 n a :=
  change (app_nat_fun (n :: l1) (a :: l2)) with ((nth n (a :: l2) a) :: (app_nat_fun l1 (a :: l2))) in *.

Lemma app_nat_fun_middle {A} : forall l1 l2 (a : A) (p : list nat),
    app_nat_fun (length l1 :: p) (l1 ++ a :: l2) = a :: (app_nat_fun p (l1 ++ a :: l2)).
Proof with try reflexivity; try assumption.
  destruct l1...
  intros l2 a0 p.
  change (app_nat_fun (length (a :: l1) :: p) ((a :: l1) ++ a0 :: l2)) with ((nth (length (a :: l1)) ((a :: l1) ++ a0 :: l2) a) :: app_nat_fun p ((a :: l1) ++ a0 :: l2)).
  pattern a0 at 3.
  replace a0 with (nth (length (a :: l1)) ((a :: l1) ++ a0 :: l2) a)...
  apply nth_middle.
Qed.

Lemma app_nat_fun_nil {A} : forall (l : list A),
    app_nat_fun nil l = nil.
Proof with try reflexivity.
  destruct l...
Qed.

Lemma app_nat_fun_length {A} : forall f (l : list A), l <> nil -> length (app_nat_fun f l) = length f.
Proof with try reflexivity.
  intros f l Hnnil.
  destruct l; [ exfalso; apply Hnnil | ]...
  apply map_length.
Qed.

Lemma app_nat_fun_shift {A} : forall la lb (a : A) p
                                     (H : length (la ++ lb) <> 0)
                                     (Halt : all_lt p (length (la ++ lb)) = true),
    app_nat_fun (shift p (length la)) (la ++ a :: lb) = app_nat_fun p (la ++ lb).
Proof with try reflexivity; try assumption.
  intros la lb a p;
    revert la lb a;
    induction p;
    intros la lb b H Halt.
  - destruct la; destruct lb...
  - destruct la; [destruct lb | ].
    + exfalso.
      apply H...
    + rewrite ? app_nil_l.
      change (length nil) with 0.
      unfold app_nat_fun.
      change (shift (a :: p) 0) with ((S a) :: shift p 0).
      rewrite 2 map_cons.
      change (nth (S a) (b :: a0 :: lb) b) with (nth a (a0 :: lb) b).
      specialize (IHp nil (a0 :: lb) b).
      rewrite 2 app_nil_l in IHp.
      unfold app_nat_fun in IHp.
      change (length nil) with 0 in IHp.
      rewrite IHp.
      * replace (nth a (a0 :: lb) b) with (nth a (a0 :: lb) a0)...
        apply nth_indep.
        apply andb_prop in Halt as (Hlt & _).
        apply Nat.ltb_lt in Hlt...
      * intros Heq; inversion Heq.
      * apply andb_prop in Halt as (_ & Halt)...
    + change ((a0 :: la) ++ b :: lb) with (a0 :: la ++ b :: lb).
      change ((a0 :: la) ++ lb) with (a0 :: la ++ lb).
      unfold app_nat_fun.
      specialize (IHp (a0 :: la) lb b).
      remember (length (a0 :: la)) as n.
      apply andb_prop in Halt as (Hlt & Halt).
      change ((fix all_lt (l : list nat) (n : nat) {struct l} : bool :=
            match l with
            | nil => true
            | k :: l0 => (k <? n) && all_lt l0 n
            end) p (length ((a0 :: la) ++ lb))) with (all_lt p (length ((a0 :: la) ++ lb))) in Halt.
      case_eq (a <? n); intros Hltan.
      * replace (shift (a :: p) n) with (a :: shift p n).
        2:{ simpl.
            rewrite Hltan... }
        rewrite 2 map_cons.
        rewrite Heqn in Hltan.
        apply Nat.ltb_lt in Hltan.
        change (a0 :: la ++ b :: lb) with ((a0 :: la) ++ b :: lb).
        rewrite (app_nth1 (a0 :: la) (b :: lb) a0 Hltan).
        change (a0 :: la ++ lb) with ((a0 :: la) ++ lb).
        rewrite (app_nth1 (a0 :: la) lb a0 Hltan).
        change (map (fun x : nat => nth x ((a0 :: la) ++ lb) a0) p) with (app_nat_fun p ((a0 :: la) ++ lb)).
        change (map (fun x : nat => nth x ((a0 :: la) ++ b :: lb) a0) (shift p n)) with
            (app_nat_fun (shift p n) ((a0 :: la) ++ b :: lb)).
        rewrite IHp...
      * destruct a.
        { destruct n.
          - inversion Heqn.
          - apply Nat.ltb_nlt in Hltan.
            lia. }
        replace (shift (S a :: p) n) with (S (S a) :: shift p n).
        2:{ simpl.
            rewrite Hltan... }
        rewrite 2 map_cons.
        change (map (fun x : nat => nth x (a0 :: la ++ lb) a0) p) with (app_nat_fun p ((a0 :: la) ++ lb)).
        change (map (fun x : nat => nth x (a0 :: la ++ b :: lb) a0) (shift p n)) with (app_nat_fun (shift p n) ((a0 :: la) ++ b :: lb)).
        rewrite IHp...
        replace (nth (S (S a)) (a0 :: la ++ b :: lb) a0) with (nth (S a) (a0 :: la ++ lb) a0)...
        rewrite Heqn in Hltan.
        clear - Hltan.
        apply Nat.ltb_nlt in Hltan.
        change (a0 :: la ++ lb) with ((a0 :: la) ++ lb).
        change (a0 :: la ++ b :: lb) with ((a0 :: la) ++ b :: lb).
        remember (a0 :: la).
        clear Heql la.
        revert a Hltan.
        induction l; intros n nHlt...
        simpl in nHlt.
        simpl.
        destruct n.
        { destruct l...
          simpl in nHlt.
          exfalso.
          apply nHlt.
          lia. }
        apply IHl; try lia.
Qed.

Lemma app_nat_fun_downshift {A} : forall la lb (a : A) p
                                         (nHin : In_nat_bool (length la) p = false)
                                         (Halt : all_lt p (S (length (la ++ lb))) = true),
    app_nat_fun p (la ++ a :: lb) = app_nat_fun (downshift p (length la)) (la ++ lb).
Proof with try reflexivity; try assumption.
  intros la lb a p;
    revert la lb a;
    induction p;
    intros la lb b nHin Halt.
  - destruct la; destruct lb...
  - destruct la; [destruct lb | ].
    + destruct a; try now inversion nHin.
    + rewrite ? app_nil_l.
      change (length nil) with 0.
      unfold app_nat_fun.
      destruct a ; try now inversion nHin.
      change (downshift ((S a) :: p) 0) with (a :: downshift p 0).
      rewrite 2 map_cons.
      change (nth (S a) (b :: a0 :: lb) b) with (nth a (a0 :: lb) b).
      specialize (IHp nil (a0 :: lb) b).
      rewrite 2 app_nil_l in IHp.
      unfold app_nat_fun in IHp.
      change (length nil) with 0 in IHp.
      rewrite IHp.
      * replace (nth a (a0 :: lb) b) with (nth a (a0 :: lb) a0)...
        apply nth_indep.
        apply andb_prop in Halt as (Hlt & _).
        apply Nat.ltb_lt in Hlt.
        rewrite app_nil_l in Hlt; lia.
      * apply orb_false_iff in nHin as (_ & H)...
      * apply andb_prop in Halt as (_ & Halt)...
    + change ((a0 :: la) ++ b :: lb) with (a0 :: la ++ b :: lb).
      change ((a0 :: la) ++ lb) with (a0 :: la ++ lb).
      unfold app_nat_fun.
      specialize (IHp (a0 :: la) lb b).
      remember (length (a0 :: la)) as n.
      apply orb_false_iff in nHin as (nHeq & nHin).
      change ((fix In_nat_bool (n : nat) (l : list nat) {struct l} : bool :=
            match l with
            | nil => false
            | k :: l0 => (n =? k) || In_nat_bool n l0
            end) n p) with (In_nat_bool n p) in nHin.
      apply andb_prop in Halt as (Hlt & Halt).
      change ((fix all_lt (l : list nat) (n : nat) {struct l} : bool :=
            match l with
            | nil => true
            | k :: l0 => (k <? n) && all_lt l0 n
            end) p (S (length ((a0 :: la) ++ lb)))) with (all_lt p (S (length ((a0 :: la) ++ lb)))) in Halt.
      case_eq (a <? n); intros Hltan.
      * replace (downshift (a :: p) n) with (a :: downshift p n).
        2:{ simpl.
            rewrite Hltan... }
        rewrite 2 map_cons.
        rewrite Heqn in Hltan.
        apply Nat.ltb_lt in Hltan.
        change (a0 :: la ++ b :: lb) with ((a0 :: la) ++ b :: lb).
        rewrite (app_nth1 (a0 :: la) (b :: lb) a0 Hltan).
        change (a0 :: la ++ lb) with ((a0 :: la) ++ lb).
        rewrite (app_nth1 (a0 :: la) lb a0 Hltan).
        change (map (fun x : nat => nth x ((a0 :: la) ++ b :: lb) a0) p) with (app_nat_fun p ((a0 :: la) ++ b :: lb)).
        rewrite IHp...
      * rewrite Nat.eqb_sym in nHeq.
        destruct a.
        { destruct n.
          - apply Nat.eqb_neq in nHeq.
            exfalso; apply nHeq...
          - apply Nat.ltb_nlt in Hltan.
            lia. }
        replace (downshift (S a :: p) n) with (a :: downshift p n).
        2:{ simpl.
            rewrite Hltan.
            simpl in nHeq;rewrite nHeq... }
        rewrite 2 map_cons.
        change (map (fun x : nat => nth x (a0 :: la ++ b :: lb) a0) p) with (app_nat_fun p ((a0 :: la) ++ b :: lb)).

        change (map (fun x : nat => nth x (a0 :: la ++ lb) a0) (downshift p n)) with (app_nat_fun (downshift p n) ((a0 :: la) ++ lb)).
        rewrite IHp...
        replace (nth (S a) (a0 :: la ++ b :: lb) a0) with (nth a (a0 :: la ++ lb) a0)...
        rewrite Heqn in Hltan, nHeq.
        clear - Hltan nHeq.
        apply Nat.eqb_neq in nHeq.
        apply Nat.ltb_nlt in Hltan.
        change (a0 :: la ++ lb) with ((a0 :: la) ++ lb).
        change (a0 :: la ++ b :: lb) with ((a0 :: la) ++ b :: lb).
        remember (a0 :: la).
        clear Heql la.
        revert a nHeq Hltan.
        induction l; intros n nHeq nHlt...
        simpl in nHeq, nHlt.
        simpl.
        destruct n.
        { destruct l; try lia. }
        apply IHl; try lia.
Qed.

Lemma app_nat_fun_downshift_commu : forall a l f k,
    In_nat_bool k (a :: l) = false ->
    all_lt f (length (a :: l)) = true ->
    all_distinct f = true ->
    app_nat_fun f (downshift (a :: l) k) = downshift (app_nat_fun f (a :: l)) k.
Proof with try reflexivity; try assumption.
  intros a l f k nHin Hal Had.
  revert a l k nHin Hal Had; induction f; intros b l k nHin Hal Had.
  { rewrite app_nat_fun_nil... }
  case_eq (b <? k); intros Hlt.
  - assert (downshift (b :: l) k = b :: downshift l k).
    { simpl; rewrite Hlt... }
    rewrite H.
    app_nat_fun_unfold f (downshift l k) a b.
    app_nat_fun_unfold f l a b.
    rewrite<- H.
    simpl in Hal, Had.
    apply andb_prop in Hal as (Hlt' & Hal)...
    apply andb_prop in Had as (nHin' & Had)...
    rewrite IHf...
    rewrite H.
    clear - Hlt nHin Hal Had Hlt' nHin'.
    destruct a.
    + change (nth 0 (b :: downshift l k) b) with b.
      change (nth 0 (b :: l) b) with b.
      simpl; rewrite Hlt...
    + change (nth (S a) (b :: downshift l k) b) with (nth a (downshift l k) b).
      change (nth (S a) (b :: l) b) with (nth a l b).
      rewrite downshift_nth...
      * apply Lt.lt_S_n.
        apply Nat.ltb_lt...
      * apply orb_false_iff in nHin as (_ & nHin)...
  - rewrite downshift_gt.
    2:{ apply orb_false_iff in nHin as (nHeq & _).
        apply Nat.eqb_neq in nHeq.
        apply Nat.ltb_nlt in Hlt.
        apply Nat.ltb_lt.
        lia. }
    app_nat_fun_unfold f (downshift l k) a (pred b).
    pattern (pred b :: downshift l k) at 2.
    rewrite <- downshift_gt.
    2:{ apply orb_false_iff in nHin as (nHeq & _).
        apply Nat.eqb_neq in nHeq.
        apply Nat.ltb_nlt in Hlt.
        apply Nat.ltb_lt.
        lia. }
    simpl in Hal, Had.
    apply andb_prop in Hal as (Hlt' & Hal)...
    apply andb_prop in Had as (nHin' & Had)...
    rewrite IHf...
    app_nat_fun_unfold f l a b.
    destruct a.
    + change (nth 0 (pred b :: downshift l k) (pred b)) with (pred b).
      change (nth 0 (b :: l) b) with b.
      rewrite downshift_gt...    
      apply orb_false_iff in nHin as (nHeq & _).
      apply Nat.eqb_neq in nHeq.
      apply Nat.ltb_nlt in Hlt.
      apply Nat.ltb_lt.
      lia.
    + change (nth (S a) ((pred b) :: downshift l k) (pred b)) with (nth a (downshift l k) (pred b)).
      change (nth (S a) (b :: l) b) with (nth a l b).
      apply Nat.ltb_lt in Hlt'.
      apply Lt.lt_S_n in Hlt'.
      apply orb_false_iff in nHin as (_ & nHin). 
      replace (nth a (downshift l k) (Init.Nat.pred b)) with (nth a (downshift l k) b).
      2:{ apply nth_indep.
          rewrite downshift_length... }
      rewrite downshift_nth...
Qed.

Lemma asso_app_nat_fun {A} : forall l1 l2 (l3 : list A),
    app_nat_fun (app_nat_fun l1 l2) l3 = app_nat_fun l1 (app_nat_fun l2 l3).
Proof with try reflexivity; try assumption.
  intros l1 l2 l3.
  destruct l3...
  rename a into n.
  destruct l2...
  unfold app_nat_fun.
  change (match map (fun x0 : nat => nth x0 (n :: l3) n) (n0 :: l2) with
          | nil => nil
          | a :: l => map (fun x : nat => nth x (a :: l) a) l1
          end)
    with (map (fun x0 => nth x0 ((nth n0 (n :: l3) n) :: map (fun x1 => nth x1 (n :: l3) n) l2) (nth n0 (n :: l3) n)) l1).
  revert n l3 n0 l2; induction l1; intros n l3 n0 l2...
  change (map (fun x0 : nat => nth x0 (n :: l3) n)
              (map (fun x1 : nat => nth x1 (n0 :: l2) n0) (a :: l1))) with
      (nth (nth a (n0 :: l2) n0) (n :: l3) n :: (map (fun x0 : nat => nth x0 (n :: l3) n)
                                                     (map (fun x1 : nat => nth x1 (n0 :: l2) n0) l1))).
  change (map
    (fun x0 : nat =>
     nth x0 (nth n0 (n :: l3) n :: map (fun x1 : nat => nth x1 (n :: l3) n) l2)
         (nth n0 (n :: l3) n)) (a :: l1)) with
      (nth a (nth n0 (n :: l3) n :: (map (fun x1 => nth x1 (n :: l3) n) l2)) (nth n0 (n :: l3) n) :: map
    (fun x0 : nat =>
     nth x0 (nth n0 (n :: l3) n :: map (fun x1 : nat => nth x1 (n :: l3) n) l2)
         (nth n0 (n :: l3) n)) l1).
  replace (nth a (nth n0 (n :: l3) n :: map (fun x1 : nat => nth x1 (n :: l3) n) l2)
               (nth n0 (n :: l3) n)) with
      (nth (nth a (n0 :: l2) n0) (n :: l3) n).
  2:{ case_eq (a <? (length (n0 :: l2))); intros Hlt.
      - clear - Hlt.
        revert a n0 Hlt.
        induction l2; intros b n0 Hlt.
        + destruct b; try destruct b...
        + destruct b...
          change (nth (S b) (n0 :: a :: l2) n0) with (nth b (a :: l2) n0).
          change (nth (S b) (nth n0 (n :: l3) n :: map (fun x1 : nat => nth x1 (n :: l3) n) (a :: l2))
                      (nth n0 (n :: l3) n))
            with (nth b (nth a (n :: l3) n :: map (fun x1 => nth x1 (n :: l3) n) l2) (nth n0 (n :: l3) n)).
          replace (nth b (a :: l2) n0) with (nth b (a :: l2) a).
          2:{ apply nth_indep.
              apply Nat.ltb_lt in Hlt.
              simpl in Hlt.
              simpl.
              lia. }
          replace (nth b (nth a (n :: l3) n :: map (fun x1 : nat => nth x1 (n :: l3) n) l2)
                       (nth n0 (n :: l3) n))
            with (nth b (nth a (n :: l3) n :: map (fun x1 : nat => nth x1 (n :: l3) n) l2)
                      (nth a (n :: l3) n)).
          2:{ apply nth_indep.
              apply Nat.ltb_lt in Hlt.
              simpl in Hlt.
              simpl.
              rewrite map_length.
              lia. }
          apply IHl2...
      - apply Nat.ltb_nlt in Hlt.
        replace (nth a (n0 :: l2) n0) with n0.
        2:{ symmetry.
            apply nth_overflow.
            lia. }
        symmetry.
        apply nth_overflow.
        simpl.
        rewrite map_length.
        simpl in Hlt.
        lia. }
  replace (map
       (fun x0 : nat =>
        nth x0 (nth n0 (n :: l3) n :: map (fun x1 : nat => nth x1 (n :: l3) n) l2)
            (nth n0 (n :: l3) n)) l1) with
      (map (fun x : nat => nth x (n :: l3) n)
           (map (fun x : nat => nth x (n0 :: l2) n0) l1))...
  apply IHl1.
Qed.        

Lemma app_nat_fun_right {A} : forall (l1 : list A) l2 f,
    all_lt f (length l2) = true ->
    app_nat_fun (incr_all f (length l1)) (l1 ++ l2) = app_nat_fun f l2.
Proof with try reflexivity; try assumption.
  intros l1 l2 f; revert l1 l2.
  induction f; intros l1 l2 Hal; destruct l1; try now destruct l2.
  - rewrite incr_all_0...
  - change (app_nat_fun (incr_all (a :: f) (length (a0 :: l1))) ((a0 :: l1) ++ l2))
      with
        ((nth ((length (a0 :: l1)) + a)) ((a0 :: l1) ++ l2) a0 :: (app_nat_fun  (incr_all f (length (a0 :: l1))) ((a0 :: l1) ++ l2))).
    destruct l2.
    { inversion Hal. }
    change (app_nat_fun (a :: f) (a1 :: l2)) with ((nth a (a1 :: l2) a1) :: (app_nat_fun f (a1 :: l2))).
    apply andb_prop in Hal as (Hlt & Hal).
    rewrite (IHf _ _ Hal).
    replace (nth a (a1 :: l2) a1) with (nth (length (a0 :: l1) + a) ((a0 :: l1) ++ a1 :: l2) a0)...
    rewrite nth_plus.
    apply nth_indep.
    simpl.
    apply Nat.ltb_lt...
Qed.

Lemma app_nat_fun_left {A} : forall (l1 l2 : list A) f,
    all_lt f (length l1) = true ->
    app_nat_fun f (l1 ++ l2) = app_nat_fun f l1.
Proof with try reflexivity; try assumption.
  intros l1 l2; induction f; intros Hal.
  - destruct l1; destruct l2...
  - destruct l1; try now inversion Hal.
    change (app_nat_fun (a :: f) ((a0 :: l1) ++ l2)) with (nth a ((a0 :: l1) ++ l2) a0 :: app_nat_fun f ((a0 :: l1) ++ l2)).
    rewrite IHf.
    2:{ apply andb_prop in Hal as (_ & Hal)... }
    app_nat_fun_unfold f l1 a a0.
    replace (nth a (a0 :: l1) a0) with (nth a ((a0 :: l1) ++ l2) a0)...
    rewrite app_nth1...
    apply andb_prop in Hal as (Hlt & _).
    apply Nat.ltb_lt in Hlt...
Qed.

Lemma app_nat_fun_app {A} : forall (l : list A) f1 f2,
    app_nat_fun (f1 ++ f2) l = app_nat_fun f1 l ++ app_nat_fun f2 l.
Proof with try reflexivity; try assumption.
  intros l f1; revert l.
  induction f1; intros l f2; destruct l...
  change (app_nat_fun ((a :: f1) ++ f2) (a0 :: l)) with
      (nth a (a0 :: l) a0 :: app_nat_fun (f1 ++ f2) (a0 :: l)).
  change (app_nat_fun (a :: f1) (a0 :: l)) with
      (nth a (a0 :: l) a0 :: app_nat_fun f1 (a0 :: l)).
  rewrite IHf1...
Qed.  

Lemma append_fun_eq {A} : forall (l1 : list A) l2 f1 f2,
    all_lt f1 (length l1) = true ->
    all_lt f2 (length l2) = true ->
    app_nat_fun (f1 ++ (incr_all f2 (length l1))) (l1 ++ l2) = (app_nat_fun f1 l1) ++ (app_nat_fun f2 l2).
Proof with try reflexivity; try assumption.
  intros l1 l2 f1; revert l1 l2.
  induction f1; intros l1 l2 f2 Hal1 Hal2; destruct l1.
  - simpl.
    rewrite incr_all_0...
  - rewrite 2 app_nil_l.
    apply app_nat_fun_right...
  - inversion Hal1.
  - rewrite app_nat_fun_app.
    rewrite app_nat_fun_right...
    rewrite app_nat_fun_left...
Qed.

Lemma app_nat_fun_downshift_shift : forall l f n0 n,
    all_distinct l = true ->
    all_distinct f = true ->
    all_lt f (pred (length l)) = true ->
    n < length l ->
    app_nat_fun f (downshift l (nth n l n0))= downshift (app_nat_fun (shift f n) l) (nth n l n0).
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
  change (incr_all (nth a (n0 :: l) n0 :: app_nat_fun p (n0 :: l)) n) with (n + nth a (n0 :: l) n0 :: incr_all (app_nat_fun p (n0 :: l)) n).
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
  change ( map f (nth a0 (a :: l) a :: app_nat_fun p (a :: l))) with (f (nth a0 (a :: l) a) :: map f (app_nat_fun p (a :: l))).
  rewrite map_nth...
Qed.

(* ID *)
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
  change (map (fun x : nat => nth (1 + x) (a1 :: a :: l) a2) (Id (S (length l)))) with (map (fun x : nat => nth x (a :: l) a2) (Id (S (length l)))).
  change (map (fun x : nat => nth (1 + x) (a1 :: a :: l) a3) (Id (S (length l)))) with (map (fun x : nat => nth x (a :: l) a3) (Id (S (length l)))).
  rewrite IHl with a a2 a3...
Qed.

Lemma app_Id {A} : forall (l : list A),
    app_nat_fun (Id (length l)) l = l.
Proof with try reflexivity; try assumption.
  induction l...
  simpl.
  change (fun x0 : nat => match x0 with
                          | 0 => a
                          | S n => nth n l a
                          end) with (fun x0 => nth x0 (a :: l) a).
  rewrite map_incr_all.
  change (map (fun x : nat => nth (1 + x) (a :: l) a) (Id (length l))) with (map (fun x : nat => nth x l a) (Id (length l))).
  replace (map (fun x : nat => nth x l a) (Id (length l))) with l...
  symmetry.
  transitivity (app_nat_fun (Id (length l)) l)...
  unfold app_nat_fun.
  destruct l...
  apply nth_correct_map_Id. 
Qed.

Lemma app_nat_fun_Id_r : forall f k, fold_left max f 0 < k -> app_nat_fun f (Id k) = f.
Proof with try assumption; try reflexivity.
  intros f k Hlt.
  unfold app_nat_fun.
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
    + replace (nth n0 (map (fun x : nat => nth x (Id (S k)) 0) f) a0) with (nth n0 (map (fun x : nat => nth x (Id (S k)) 0) f) (nth 0 (Id (S k)) 0)).
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
    replace (incr_all (0 :: incr_all (Id (length l2)) 1) (length l1)) with ((length l1) :: incr_all (incr_all (Id (length l2)) (length l1)) 1).
    2:{ simpl.
        rewrite Nat.add_0_r.
        rewrite incr_all_incr_all... }
    simpl.
    rewrite app_nat_fun_middle.
    replace (app_nat_fun (incr_all (incr_all (Id (length l2)) (length l1)) 1 ++ Id (length l1)) (l1 ++ a :: l2)) with (l2 ++ l1)...
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
