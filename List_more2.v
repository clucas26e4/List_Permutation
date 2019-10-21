Require Import Lia.
Require Import PeanoNat.

Require Export List.


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

Lemma nth_split_Type {A} n l (d:A) : n < length l ->
    {' (l1,l2) : _ & l = l1 ++ nth n l d :: l2 & length l1 = n }.
  Proof.
    revert l.
    induction n as [|n IH]; intros [|a l] H; try (exfalso; easy).
    - exists (nil,l); now simpl.
    - destruct (IH l) as [(l1,l2) Hl Hl1]; auto with arith.
      exists (a::l1,l2); simpl; now f_equal.
  Qed.

(* fold_right *)
Lemma fold_right_app_assoc2 {A B} f (g : B -> A) h (e : A) l1 l2 :
    (forall x y z, h (g x) (f y z) = f (h (g x) y) z) ->
    (f e (fold_right (fun x => h (g x)) e l2) = (fold_right (fun x => h (g x)) e l2)) ->
  fold_right (fun x => h (g x)) e (l1 ++ l2) =
  f (fold_right (fun x => h (g x)) e l1) (fold_right (fun x => h (g x)) e l2).
Proof.
intros Hassoc Hunit.
rewrite fold_right_app.
remember (fold_right (fun x => f (g x)) e l2) as r.
induction l1; simpl.
- symmetry; apply Hunit.
- rewrite <- Hassoc.
  f_equal; assumption.
Qed.

Lemma fold_right_app_assoc {A} f (e : A) l1 l2 :
  (forall x y z, f x (f y z) = f (f x y) z) -> (forall x, f e x = x) ->
  fold_right f e (l1 ++ l2) = f (fold_right f e l1) (fold_right f e l2).
Proof. intros Hassoc Hunit; apply fold_right_app_assoc2; [ assumption | apply Hunit ]. Qed.

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

Lemma fold_left_max_indep : forall i l, i < fold_left max l i ->
  forall j, fold_left max l i <= fold_left max l j.
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

Lemma fold_left_max_app : forall k l1 l2,
  fold_left max (l1 ++ l2) k = max (fold_left max l1 k) (fold_left max l2 k).
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


(* seq *)

(* exists in recent versions of stdlib cf 8.10 *)
Lemma seq_app : forall len1 len2 start,
  seq start (len1 + len2) = seq start len1 ++ seq (start + len1) len2.
Proof.
induction len1; intros start len2.
- simpl; f_equal; lia.
- simpl; rewrite IHlen1.
  f_equal; f_equal; f_equal; lia.
Qed.

Lemma seq_cons : forall s l, s :: seq (S s) l = seq s (S l).
Proof. intros s l; revert s; induction l; intros s; simpl; now rewrite ? IHl. Qed.

Lemma seq_S : forall s l, seq s (S l) = seq s l ++ s + l :: nil.
Proof.
intros s l.
change (s + l :: nil) with (seq (s + l) 1).
rewrite <- seq_app.
f_equal; lia.
Qed.


(* skipn *)
(* exists in recent versions of stdlib cf 8.10 *)
(* note in these versions skipn_none = skipn_all *)
Lemma skipn_all2 {A} : forall n (l : list A),
  length l <= n -> skipn n l = nil.
Proof with try reflexivity.
  induction n; intros l Hle.
  - destruct l; inversion Hle...
  - destruct l; simpl in Hle...
    apply IHn.
    lia.
Qed.

(* exists in recent versions of stdlib cf 8.10 *)
Lemma skipn_length {A} : forall n (l : list A),
    length (skipn n l) = length l - n.
Proof with try reflexivity.
  induction n; intros l.
  - simpl; lia.
  - destruct l...
    simpl; rewrite IHn...
Qed.
