Require Import Lia.
Require Import PeanoNat.

Require Import List_Type_more.

(* Properties on nth *)
Lemma nth_nth {A} : forall (l1 : list nat) (l2 : list A) a0 k0 k,
    k < length l1 ->
    nth (nth k l1 k0) l2 a0 = nth k (map (fun x => nth x l2 a0) l1) a0.
Proof with try assumption; try reflexivity.
  induction l1; intros l2 a0 k0 k Hlt.
  - inversion Hlt.
  - destruct k...
    simpl.
    apply IHl1.
    simpl in Hlt.
    lia.
Qed.

Lemma nth_plus {A} : forall (l1 : list A) l2 k0 k,
    nth (length l1 + k) (l1 ++ l2) k0 = nth k l2 k0.
Proof with try reflexivity; try assumption.
  induction l1; intros k2 k0 k...
  simpl.
  apply IHl1...
Qed.

Lemma nth_middle {A} : forall la lb (a : A) a0,
    nth (length la) (la ++ a :: lb) a0 = a.
Proof with try reflexivity.
  induction la; intros lb a' a0...
  simpl.
  apply IHla.
Qed.

Lemma list_ext {A} : forall l1 l2,
    length l1 = length l2 ->
    (forall n (a0 : A), nth n l1 a0 = nth n l2 a0) ->
    l1 = l2.
Proof with try reflexivity.
  induction l1; intros l2 Hlen H.
  - destruct l2; try now inversion Hlen...
  - destruct l2; try now inversion Hlen.
    replace a0 with a.
    2:{ change a with (nth 0 (a :: l1) a).
        change a0 with (nth 0 (a0 :: l2) a).
        apply H. }
    apply Nat.succ_inj in Hlen.
    specialize (IHl1 l2 Hlen).
    clear Hlen.
    replace l2 with l1...
    apply IHl1.
    intros n a1.
    refine (H (S n) a1).
Qed.


Lemma cond_In {A} :
  forall l (x : A),
    (exists p, prod (fst p < length l) (nth (fst p) l (snd p) = x)) ->
    In x l.
Proof with try reflexivity; try assumption.
  induction l; intros x [(k , a0) (Hlen & Heq)]; simpl in Hlen, Heq.
  - inversion Hlen.
  - destruct k.
    + left...
    + simpl in Hlen; apply Lt.lt_S_n in Hlen.
      right.
      apply IHl.
      exists (k , a0).
      split...
Qed.

Lemma cond_In_inv {A} :
  forall l (x : A),
    In x l ->
    exists p, prod (fst p < length l) (nth (fst p) l (snd p) = x).
Proof with try reflexivity; try assumption.
  induction l; intros x Hin.
  - inversion Hin.
  - refine (@or_ind (a = x) (In x l) _ _ _ _).
    + intros H.
      exists (0 , a).
      simpl.
      split...
      lia.
    + clear Hin; intros Hin.
      destruct (IHl x Hin) as [(k & a0) (Hlen & Heq)].
      exists (S k , a0).
      split...
      simpl in Hlen |- *; lia.
    + apply in_inv...
Qed.

Lemma cond_In_Type {A} :
  forall l (x : A),
    {' (k , a0) : _ & prod (k < length l) (nth k l a0 = x) } ->
    In_Type x l.
Proof with try reflexivity; try assumption.
  induction l; intros x ((k , a0) & (Hlen & Heq)); simpl in Hlen, Heq.
  - exfalso.
    inversion Hlen.
  - destruct k.
    + left...
    + simpl in Hlen; apply Lt.lt_S_n in Hlen.
      right.
      apply IHl.
      split with (k , a0).
      split...
Qed.

Lemma cond_In_Type_inv {A} :
  forall l (x : A),
    In_Type x l ->
    {' (k , a0) : _ & prod (k < length l) (nth k l a0 = x)}.
Proof with try reflexivity; try assumption.
  induction l; intros x Hin.
  - inversion Hin.
  - destruct Hin.
    + exists (0 , a).
      simpl.
      split...
      lia.
    + destruct (IHl x i) as [(k & a0) (Hlen & Heq)].
      exists (S k , a0).
      split...
      simpl in Hlen |- *; lia.
Qed.

Lemma map_nth {A B} : forall (f : A -> B) l a0 k,
    nth k (map f l) (f a0) = f (nth k l a0).
Proof with try reflexivity.
  intros f.
  induction l; intros a0 k.
  - destruct k...
  - destruct k...
    rewrite map_cons.
    apply IHl.
Qed.

Lemma nth_decomp {A} : forall l (a0 : A) k,
    k < length l ->
    {' (la , lb) : _ & prod (length la = k) (l = la ++ (nth k l a0) :: lb)}.
Proof with try reflexivity; try assumption.
  induction l; intros a0 k Hlt.
  - exfalso; simpl in Hlt; lia.
  - destruct k.
    + split with (nil, l).
      split...
    + simpl in Hlt.
      apply Lt.lt_S_n in Hlt.
      specialize (IHl a0 k Hlt) as ((la & lb) & (Hlen & Heq)).
      split with (a :: la, lb).
      split.
      * rewrite<- Hlen...
      * pattern l at 1.
        rewrite Heq...
Qed.     


(* fold_left max *)
Lemma fold_left_max_r : forall f a, a <= fold_left max f a.
Proof with try reflexivity.
  induction f; intros k...
  simpl.
  transitivity (max k a).
  - apply Nat.le_max_l.
  - apply IHf.
Qed.

Lemma fold_left_max_le_r : forall l i j, i <= j -> fold_left max l i <= fold_left max l j.
Proof with try reflexivity; try assumption.
  clear; induction l; intros i j Hle...
  simpl.
  apply IHl.
  lia.
Qed.

Lemma fold_left_max_indep : forall i l, i < fold_left max l i -> forall j, fold_left max l i <= fold_left max l j.
Proof with try assumption; try reflexivity.
  intros i l; revert i; induction l; intros i Hlt j.
  - simpl in Hlt.
    exfalso; lia.
  - simpl in *.
    case_eq (max i a <? fold_left max l (max i a)); intros Hcase.
    + apply Nat.ltb_lt in Hcase.
      apply IHl...
    + apply Nat.ltb_nlt in Hcase.
      assert (i < a) by lia.
      replace (max i a) with a in * by lia.
      apply fold_left_max_le_r.
      lia.
Qed.

Lemma fold_left_max_le : forall l i j, fold_left max l i <= j -> fold_left max l j <= j.
Proof with try assumption;try reflexivity.
  induction l; intros i j Hle...
  simpl.
  simpl in Hle.
  replace j with (max j a) at 2.
  2:{ apply Nat.max_l.
      transitivity (max i a) ; [lia | ].
      transitivity (fold_left max l (max i a)).
      - apply fold_left_max_r.
      - apply Hle. }
  apply IHl with (max i a).
  transitivity j; lia.
Qed.
  
Lemma fold_left_max_app : forall k l1 l2, fold_left max (l1 ++ l2) k = max (fold_left max l1 k) (fold_left max l2 k).
Proof with try assumption; try reflexivity.
  intros k l1; revert k; induction l1; intros k l2.
  - simpl.
    symmetry.
    apply Nat.max_r.
    apply fold_left_max_r.
  - simpl.
    rewrite IHl1.
    case_eq (fold_left max l2 k <=? max k a); intros Hcase.
    + transitivity (fold_left max l1 (max k a)).
      * apply Nat.max_l.
        apply Nat.leb_le in Hcase.
        transitivity (max k a).
        -- apply fold_left_max_le with k...
        -- apply fold_left_max_r.
      * symmetry.
        apply Nat.max_l.
        apply Nat.leb_le in Hcase.
        transitivity (max k a)...
        apply fold_left_max_r.
    + replace (fold_left max l2 k) with (fold_left max l2 (max k a))...
      apply Nat.le_antisymm.
      * apply fold_left_max_indep.
        apply Nat.leb_nle in Hcase.
        apply Nat.lt_le_trans with (fold_left max l2 k).
        -- lia.
        -- apply fold_left_max_le_r.
           lia.
      * apply fold_left_max_le_r.
        lia.
Qed.

(* Properties on list nat *)
Lemma UIP_list_nat : forall (l1 l2 : list nat) (p1 p2 : l1 = l2),
    p1 = p2.
Proof with try reflexivity; try assumption.
  intros l1 l2 p1 p2.
  apply Eqdep_dec.UIP_dec.
  apply list_eq_dec.
  apply Nat.eq_dec.
Qed.    
