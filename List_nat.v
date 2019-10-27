(* Booleans and operators used to represent functions as lists of natural numbers. *)
Require Import Lia.
Require Import PeanoNat.
Require Import Injective.

Require Import Bool_more.
Require Import List_more.

Notation beq_nat := Nat.eqb.


(** ** In_nat_bool *)

Fixpoint In_nat_bool (n : nat) (l : list nat) :=
  match l with
  | nil => false
  | k :: l => (beq_nat n k) || (In_nat_bool n l)
  end.

Lemma In_nat_bool_In n l : In_nat_bool n l = true <-> In n l.
Proof.
split; intros H; induction l.
- exfalso; inversion H.
- apply orb_true_iff in H as [H|H].
  + apply Nat.eqb_eq in H; subst; now constructor.
  + now constructor; apply IHl.
- exfalso; inversion H.
- apply orb_true_iff; inversion H; subst.
  + now left; apply Nat.eqb_eq.
  + now right; apply IHl.
Qed.

Lemma not_In_nat_bool_In n l : In_nat_bool n l = false <-> ~ In n l.
Proof.
split; intros H; induction l.
- intros Hin; inversion Hin.
- apply orb_false_iff in H as [H1 H2].
  intros Hin; inversion Hin; subst.
  + now apply Nat.eqb_neq in H1.
  + now apply IHl.
- reflexivity.
- apply orb_false_iff; split.
  + apply Nat.eqb_neq; intros Heq; subst.
    apply H; now constructor.
  + apply IHl.
    intros Hin.
    apply H; now constructor.
Qed.

Lemma In_nat_bool_false_tail : forall l n k,
    In_nat_bool n (k :: l) = false ->
    In_nat_bool n l = false.
Proof.
intros l n k nHin.
apply (proj2 (proj1 (orb_false_iff _ _) nHin)).
Qed.

Lemma In_nat_bool_true_tail : forall l n k,
    In_nat_bool n (k :: l) = true ->
    n = k \/ In_nat_bool n l = true.
Proof with try assumption.
intros l n k Hin.
apply orb_true_iff in Hin; destruct Hin; [left|right]...
apply Nat.eqb_eq...
Qed.

Lemma cond_negb_In_nat_bool : forall l n,
    (forall k k0,
        k < length l ->
        nth k l k0 <> n) <->
    In_nat_bool n l = false.
Proof.
intros l n; split; intros H.
- apply not_In_nat_bool_In.
  intros Hin.
  apply In_nth with _ _ _ n in Hin as [p [Hlen Heq]].
  apply H in Heq; assumption.
- apply not_In_nat_bool_In in H.
  intros k k0 Hlen Hnth.
  apply H.
  rewrite <- Hnth.
  apply nth_In; assumption.
Qed.

Lemma cond_In_nat_bool : forall l n,
    {'(k0 , k) : _ & k < length l & nth k l k0 = n } ->
    In_nat_bool n l = true.
Proof with try assumption; try reflexivity.
  intros l n x.
  destruct x as [(k0,k) Hlt Heq].
  revert k Hlt Heq; induction l; intros k Hlt Heq.
  - inversion Hlt.
  - destruct k.
    + simpl in Heq.
      symmetry in Heq; apply Nat.eqb_eq in Heq.
      unfold In_nat_bool.
      rewrite Heq...
    + simpl in Heq.
      simpl in Hlt; apply Lt.lt_S_n in Hlt.
      unfold In_nat_bool.
      case (n =? a)...
      change ( (fix In_nat_bool (n0 : nat) (l0 : list nat) {struct l0} : bool :=
        match l0 with
        | nil => false
        | k1 :: l1 => (n0 =? k1) || In_nat_bool n0 l1
        end) n l) with (In_nat_bool n l).
      refine (IHl k _ _)...
Qed.

Lemma cond_In_nat_bool_inv : forall l n k0,
    In_nat_bool n l = true -> 
    {k : _ & prod (k < length l) (nth k l k0 = n) }.
Proof with try assumption; try reflexivity.
  intros l n k0; induction l; intros Hin; try now inversion Hin.
  unfold In_nat_bool in Hin.
  change ((fix In_nat_bool (n : nat) (l : list nat) {struct l} : bool :=
              match l with
              | nil => false
              | k :: l0 => (n =? k) || In_nat_bool n l0
              end) n l) with (In_nat_bool n l) in Hin.
  case_eq (n =? a); intros Heq.
  - apply Nat.eqb_eq in Heq; subst.
    split with 0.
    split...
    simpl; lia.
  - rewrite Heq in Hin.
    clear Heq.
    specialize (IHl Hin) as (k & (Hlt & Heq)).
    split with (S k).
    split...
    simpl; lia.
Qed.

Lemma In_nat_bool_neq : forall l n k,
    n <> k ->
    In_nat_bool k (n :: l) = In_nat_bool k l.
Proof with try reflexivity; try assumption.
  intros l n k nHeq.
  simpl.
  replace (k =? n) with false...
  symmetry; apply Nat.eqb_neq.
  intros Heq; apply nHeq; symmetry...
Qed.

Lemma In_nat_bool_app : forall l1 l2 k,
    In_nat_bool k (l1 ++ l2) = (In_nat_bool k l1) || (In_nat_bool k l2).
Proof with try reflexivity; try assumption.
  induction l1; intros l2 k...
  simpl.
  case (k =? a)...
  rewrite IHl1...
Qed.

Lemma In_nat_bool_middle_true : forall l1 l2 a a0,
                 In_nat_bool a (l1 ++ a0 :: l2) = true ->
                 (a =? a0) || (In_nat_bool a (l1 ++ l2)) = true.
Proof with try reflexivity; try assumption.
  induction l1; intros l2 b a0 Hin...
  simpl in Hin.
  case_eq (b =? a); intros Heq.
  - case (b =? a0)...
    simpl.
    rewrite Heq...
  - rewrite Heq in Hin.
    simpl.
    replace ((b =? a0) || ((b =? a) || In_nat_bool b (l1 ++ l2)))
       with (((b =? a0) || In_nat_bool b (l1 ++ l2)) || (b =? a)).
    2:{ case (b =? a0); case (In_nat_bool b (l1 ++ l2)) ; case (b =? a)... }
    rewrite IHl1...
Qed.

Lemma In_nat_bool_middle_false : forall l1 l2 a a0,
           In_nat_bool a (l1 ++ a0 :: l2) = false ->
           (a =? a0 = false) /\ (In_nat_bool a (l1 ++ l2) = false).
Proof with try reflexivity; try assumption.
  induction l1; intros l2 b a0 nHin.
  - apply orb_false_iff in nHin...
  - case_eq (b =? a0); intros Heq.
    + apply orb_false_iff in nHin as (_ & nHin).
      specialize (IHl1 l2 b a0 nHin) as (H & _).
      rewrite Heq in H.
      inversion H.
    + split...
      apply orb_false_iff in nHin as (nHeq & nHin).
      apply orb_false_iff.
      split...
      specialize (IHl1 l2 b a0 nHin) as (_ & H)...
Qed.

Lemma In_nat_bool_app_commu : forall l1 l2 a,
  In_nat_bool a (l1 ++ l2) = In_nat_bool a (l2 ++ l1).
Proof with try reflexivity; try assumption.
  induction l1; intros l2 b.
  - rewrite app_nil_r...
  - simpl.
    case_eq (In_nat_bool b (l2 ++ a :: l1)); intros Hin.
    + apply In_nat_bool_middle_true in Hin.
      rewrite IHl1...
    + apply In_nat_bool_middle_false in Hin as (nHeq & nHin).
      rewrite nHeq.
      rewrite IHl1.
      rewrite nHin...
Qed.

(** ** all_lt *)

Definition all_lt l n := forallb (fun k => k <? n) l.

Lemma all_lt_Forall l n : all_lt l n = true <-> Forall (fun x => x < n) l.
Proof.
split; intros H; induction l; simpl.
- constructor.
- apply andb_true_iff in H as [H1 H2]; apply Nat.ltb_lt in H1.
  constructor; [ | apply IHl ]; assumption.
- reflexivity.
- inversion H; subst.
  apply andb_true_iff; split; [ apply Nat.ltb_lt | apply IHl ]; assumption.
Qed.

Lemma all_lt_leq : forall l k n,
    all_lt l k = true ->
    k <= n ->
    all_lt l n = true.
Proof with try reflexivity; try assumption.
  induction l; intros k n Hal Hleq...
  destruct (andb_prop _ _ Hal).
  apply andb_true_intro; split.
  - apply Nat.ltb_lt.
    unfold lt.
    transitivity k...
    apply Nat.ltb_lt in H...
  - apply IHl with k...
Qed.

Lemma cond_all_lt_false : forall l n k k0,
    k < length l ->
    n <= nth k l k0 ->
    all_lt l n = false.
Proof with try reflexivity; try assumption.
  induction l; intros n k k0 H Hgeq.
  - inversion H.
  - destruct k.
    + simpl.
      replace (a <? n) with false...
      symmetry.
      apply Nat.ltb_nlt.
      intros Hlt.
      simpl in Hgeq; lia.
    + simpl in H.
      apply Lt.lt_S_n in H.
      simpl in Hgeq.
      unfold all_lt; simpl.
      case (a <? n)...
      simpl.
      apply IHl with k k0...
Qed.

Lemma cond_all_lt_false_inv : forall l n,
    all_lt l n = false ->
    forall k0,
      { k & prod (k < length l) (n <= nth k l k0)}.
Proof with try reflexivity; try assumption.
  induction l; intros n nHalt k0.
  - inversion nHalt.
  - unfold all_lt in nHalt; simpl in nHalt.
    case_eq (a <? n); intros Hlt.
    + rewrite Hlt in nHalt.
      simpl in nHalt.
      destruct (IHl n nHalt k0) as (k & (Hlen & Hgeq)).
      exists (S k); split; simpl; lia.
    + apply Nat.ltb_nlt in Hlt.
      exists 0; split; simpl; lia.
Qed.

Lemma all_lt_middle_true : forall l1 l2 a k,
  all_lt (l1 ++ a :: l2) k = true -> all_lt (l1 ++ l2) k = true.
Proof with try reflexivity; try assumption.
  induction l1; intros l2 b k H.
  - apply andb_prop in H as (_ & H)...
  - apply andb_prop in H as (H1 & H2).
    simpl.
    rewrite H1.
    refine (IHl1 _ _ _ H2).
Qed.

Lemma cond_all_lt : forall l n,
  (forall k0 k, k < length l -> nth k l k0 < n) ->
  all_lt l n = true.
Proof with try reflexivity; try assumption.
  intros l n.
  induction l; intros H...
  apply andb_true_intro; split.
  - apply Nat.ltb_lt.
    change a with (nth 0 (a :: l) 0).
    apply H.
    simpl; lia.
  - apply IHl.
    intros k0 k Hlt.
    change (nth k l k0) with (nth (S k) (a :: l) k0).
    apply H.
    simpl; lia.
Qed.

Lemma cond_all_lt_inv : forall l n k0 k,
    k < length l ->
    all_lt l n = true ->
    nth k l k0 < n.
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k Hlt Halt; try now inversion Hlt.
  destruct k.
  - apply andb_prop in Halt as (H & _).
    apply Nat.ltb_lt...
  - apply andb_prop in Halt as (_ & Halt).
    apply IHl...
    simpl in Hlt; lia.
Qed.

Lemma all_lt_app : forall l1 l2 n,
    all_lt (l1 ++ l2) n = (all_lt l1 n) && (all_lt l2 n).
Proof with try reflexivity; try assumption.
  induction l1; intros l2 n...
  simpl.
  case (a <? n)...
  rewrite IHl1...
Qed.

Lemma all_lt_In_nat_bool_false : forall l n,
    all_lt l n = true ->
    In_nat_bool n l = false.
Proof with try reflexivity; try assumption.
  induction l; intros n Hal...
  apply andb_prop in Hal as (Hlt & Hal).
  simpl; rewrite (IHl _ Hal).
  replace (n =? a) with false...
  symmetry.
  apply Nat.eqb_neq.
  apply Nat.ltb_lt in Hlt; lia.
Qed.

Lemma all_lt_max : forall l, all_lt l (S (fold_left max l 0)) = true.
Proof.
  induction l; [reflexivity | ].
  simpl; apply andb_true_intro; split.
  - apply Nat.ltb_lt.
    apply le_n_S; apply fold_left_max_r.
  - apply all_lt_leq with (S (fold_left Init.Nat.max l 0)); [ assumption | ].
    apply le_n_S.
    apply fold_left_max_le_r; lia.
Qed.

(** ** all_distinct *)

Fixpoint all_distinct (l : list nat) :=
  match l with
  | nil => true
  | n :: l => (negb (In_nat_bool n l)) && (all_distinct l)
  end.

Lemma all_distinct_NoDup l : all_distinct l = true <-> NoDup l.
Proof.
split; intros H; induction l; simpl.
- constructor.
- apply andb_true_iff in H as [H1 H2].
  constructor. 
  + apply negb_true_iff in H1.
    now apply not_In_nat_bool_In.
  + now apply IHl.
- reflexivity.
- inversion H; subst.
  apply andb_true_iff; split.
  + apply negb_true_iff.
    now apply not_In_nat_bool_In.
  + now apply IHl.
Qed.

Lemma cond_all_distinct : forall l,
  (forall n1 n2 k, n1 < length l -> n2 < length l -> (nth n1 l k) = (nth n2 l k) -> n1 = n2) ->
  all_distinct l = true.
Proof.
  induction l; intros H; [ reflexivity | ].
  simpl; apply andb_true_intro; split.
  - apply negb_true_iff.
    apply cond_negb_In_nat_bool.
    intros k k0 Hlt Heq.
    refine (Nat.neq_succ_0 k _).
    apply H with k0; simpl; lia.
  - apply IHl.
    intros n1 n2 k Hlt1 Hlt2 Heq.
    apply Nat.succ_inj.
    apply H with k; simpl; lia.
Qed.

Lemma cond_all_distinct_inv : forall l, all_distinct l = true ->
  forall n1 n2 k, n1 < length l -> n2 < length l -> nth n1 l k = nth n2 l k -> n1 = n2.
Proof with try assumption; try reflexivity.
  induction l; intros Hal n1 n2 k Hlt1 Hlt2 Heq.
  - destruct n1; inversion Hlt1.
  - destruct n1; destruct n2...
    + simpl in Heq.
      simpl in Hlt2; apply Lt.lt_S_n in Hlt2.
      exfalso.
      refine (proj2 (cond_negb_In_nat_bool l a) _ n2 k _ _)...
      * apply andb_prop in Hal as (H1 & _).
        apply negb_true_iff in H1...
      * symmetry...
    + simpl in Heq.
      simpl in Hlt1; apply Lt.lt_S_n in Hlt1.
      exfalso.
      refine (proj2 (cond_negb_In_nat_bool l a) _ n1 k _ _)...
      apply andb_prop in Hal as (H1 & _).
      apply negb_true_iff in H1...
    + simpl in *.
      apply eq_S.
      refine (IHl _ _ _ k _ _ _); try lia.
      apply (andb_prop _ _ Hal).
Qed.

Lemma all_distinct_no_head : forall l n,
  all_distinct (n :: l) = true ->
  forall k k0, k < length l -> nth k l k0 <> n.
Proof with try reflexivity; try assumption.
  intros l n Hal k k0 Hlt.
  apply andb_prop in Hal as (nHin & Hal).
  change ((fix all_distinct (l : list nat) : bool :=
           match l with
           | nil => true
           | n :: l0 => negb (In_nat_bool n l0) && all_distinct l0
           end) l) with (all_distinct l) in Hal.
  refine (proj2 (cond_negb_In_nat_bool l n) _ k k0 _)...
  apply negb_true_iff...
Qed.

Lemma cond_all_distinct_false : forall l k0 k1 k2, k1 < length l ->  k2 < length l ->  k1 <> k2 ->
  nth k1 l k0 = nth k2 l k0 -> all_distinct l = false.
Proof with try reflexivity; try assumption.
  induction l; intros k0 k1 k2 Hlt1 Hlt2 nHeq Heq; try now inversion Hlt1.
  destruct k1; destruct k2.
  - exfalso.
    apply nHeq...
  - simpl.
    replace (negb (In_nat_bool a l)) with false...
    symmetry.
    apply negb_false_iff.
    apply cond_In_nat_bool.
    split with (k0 , k2).
    + simpl in Hlt2; lia.
    + simpl in Heq; rewrite Heq...
  - simpl.
    replace (negb (In_nat_bool a l)) with false...
    symmetry.
    apply negb_false_iff.
    apply cond_In_nat_bool.
    split with (k0 , k1).
    + simpl in Hlt1; lia.
    + simpl in Heq; rewrite Heq...
  - simpl.
    case (In_nat_bool a l)...
    apply IHl with k0 k1 k2...
    + simpl in Hlt1; lia.
    + simpl in Hlt2; lia.
    + intros H; apply nHeq; rewrite H...
Qed.

Lemma cond_all_distinct_false_inv : forall l k0,
  all_distinct l = false ->
  {' (k1 , k2) : _ & prod (k1 < length l) (prod (k2 < length l)
                    (prod (k1 <> k2) (nth k1 l k0 = nth k2 l k0)))}.
Proof with try reflexivity; try assumption.
  induction l; intros k0 nHalt; try now inversion nHalt.
  apply andb_false_elim in nHalt as [Hin | nHalt].
  - apply negb_false_iff in Hin.
    apply cond_In_nat_bool_inv with _ _ k0 in Hin as (k2 & (Hlt & Heq)).
    split with (0 , S k2).
    split; [ | split ; [ | split]].
    + simpl; lia.
    + simpl; lia.
    + intros H; inversion H.
    + simpl; rewrite Heq...
  - destruct (IHl k0 nHalt) as ((k1 & k2) & (Hlt1 & (Hlt2 & (nHeq & Heq)))).
    split with (S k1 , S k2).
    split; [ | split ; [ | split]].
    + simpl; lia.
    + simpl; lia.
    + intros H; inversion H; apply nHeq...
    + simpl; rewrite Heq...
Qed.

Lemma all_distinct_app_commu : forall l1 l2,
  all_distinct (l1 ++ l2) = all_distinct (l2 ++ l1).
Proof with try reflexivity; try assumption.
  induction l1; intros l2.
  - rewrite app_nil_r...
  - simpl.
    induction l2.
    + rewrite app_nil_r...
    + simpl.
      rewrite<- IHl2.
      case_eq (In_nat_bool a (l1 ++ a0 :: l2)) ; intros Hin.
      * apply In_nat_bool_middle_true in Hin.
        rewrite In_nat_bool_app_commu.
        simpl.
        case_eq (a0 =? a); intros Heq...
        replace (In_nat_bool a (l1 ++ l2)) with true.
        2:{ rewrite Nat.eqb_sym in Heq.
            rewrite Heq in Hin.
            rewrite<- Hin... }
        case (In_nat_bool a0 (l1 ++ l2))...
      * apply In_nat_bool_middle_false in Hin as (nHeq & nHin).
        rewrite nHin.
        rewrite (IHl1 (a0 :: l2)).
        simpl.
        rewrite<- (IHl1 l2).
        rewrite (In_nat_bool_app_commu _ (a :: l1)).
        simpl.
        rewrite Nat.eqb_sym.
        rewrite nHeq.
        rewrite In_nat_bool_app_commu...
Qed.

Lemma all_distinct_map : forall f p, injective f ->
  all_distinct (map f p) = all_distinct p.
Proof.
intros f p Hinj; induction p; [ reflexivity | ]; simpl.
remember (In_nat_bool a p) as b; symmetry in Heqb; destruct b; simpl.
- enough (In_nat_bool (f a) (map f p) = true) as Hf by (rewrite Hf; reflexivity).
  clear - Heqb; induction p; [ inversion Heqb | ].
  simpl in Heqb.
  apply orb_true_iff; apply orb_true_iff in Heqb as [Hin|Hin].
  + left; apply Nat.eqb_eq in Hin; apply Nat.eqb_eq; subst; reflexivity.
  + right; apply IHp; assumption.
- remember (all_distinct p) as b'; symmetry in Heqb'; destruct b'; simpl.
  + apply andb_true_iff; split; [ | assumption ].
    enough (In_nat_bool (f a) (map f p) = false) as Hf by (rewrite Hf; reflexivity).
    clear - Hinj Heqb; induction p; [ reflexivity | ]; simpl in Heqb.
    apply orb_false_iff; apply orb_false_iff in Heqb as [Hin1 Hin2]; split.
    * apply Nat.eqb_neq in Hin1; apply Nat.eqb_neq; intros H; subst; apply Hin1, Hinj; assumption.
    * apply IHp; assumption.
  + apply andb_false_iff; right; assumption.
Qed.

Lemma all_distinct_left : forall la lb k,
  all_distinct (la ++ k :: lb) = true -> In_nat_bool k la = false.
Proof with try reflexivity; try assumption.
  induction la; intros lb k Had...
  apply andb_prop in Had as (nHin & Had).  
  apply orb_false_iff.
  split.
  - apply negb_true_iff in nHin.
    rewrite Nat.eqb_sym.
    destruct (In_nat_bool_middle_false _ _ _ _ nHin)...
  - apply IHla with lb...
Qed.

Lemma all_distinct_right : forall la lb k,
  all_distinct (la ++ k :: lb) = true -> In_nat_bool k lb = false.
Proof with try reflexivity; try assumption.
  induction la; intros lb k Had.
  - apply andb_prop in Had as (nHin & Had).
    apply negb_true_iff in nHin...
  - apply andb_prop in Had as (_ & Had).
    apply IHla...
Qed.

Lemma all_distinct_elt_inv : forall k l1 l2,
  all_distinct (l1 ++ k :: l2) = true -> all_distinct (l1 ++ l2) = true.
Proof.
  intros k l1; induction l1; intros l2 Had.
  - apply andb_prop in Had as [ _ Had]; assumption.
  - simpl in Had |- *.
    apply andb_prop in Had as [nHin Had].
    apply andb_true_intro; split.
    + apply negb_true_iff in nHin.
      apply In_nat_bool_middle_false in nHin as [_ nHin].
      apply negb_true_iff; assumption.
    + apply IHl1; assumption.
Qed.

(** ** shift *)
Lemma incr_inj n i : injective (fun x => if x <? n then x else i + x).
Proof.
intros x1 x2; case_eq (x1 <? n); case_eq (x2 <? n); intros H1 H2 Heq; try now lia.
- apply Nat.ltb_ge in H1; apply Nat.ltb_lt in H2; lia.
- apply Nat.ltb_lt in H1; apply Nat.ltb_ge in H2; lia.
Qed.

Definition shift l n i := map (fun x => if x <? n then x else i + x) l.

Lemma shift_length : forall l n i,
  length (shift l n i) = length l.
Proof. intros; apply map_length. Qed.

Lemma shift_app : forall l1 l2 n i,
  shift (l1 ++ l2) n i = shift l1 n i ++ shift l2 n i.
Proof. intros; apply map_app. Qed.

Lemma shift_inj : forall l1 l2 n i,
  shift l1 n i = shift l2 n i -> l1 = l2.
Proof. intros l1 l2 n i Hi; refine (map_inj _ _ _ _ Hi); apply incr_inj. Qed.

Lemma shift_0 : forall l n, shift l n 0 = l.
Proof.
intros l n.
rewrite <- (map_id l) at 2.
apply map_ext.
intros a; destruct (a <? n); lia.
Qed.

Lemma shift_hole : forall l n i a, In a (shift l n i) ->
  a < n \/ a >= i + n.
Proof.
intros l n i; induction l; intros x Hin; inversion Hin.
- case_eq (a <? n); intros Heq; rewrite Heq in H; subst.
  + left; apply Nat.ltb_lt in Heq; lia.
  + right; apply Nat.ltb_ge in Heq; lia.
- now apply IHl.
Qed.

Lemma shift_holeb : forall l n i a, In_nat_bool a (shift l n i) = true ->
  (a <? i + n) = (a <? n).
Proof.
intros l n i a Hin.
apply In_nat_bool_In, shift_hole in Hin.
destruct Hin.
- rewrite (proj2 (Nat.ltb_lt _ _) H).
  apply Nat.ltb_lt; lia.
- rewrite (proj2 (Nat.ltb_ge _ _) H).
  symmetry; apply Nat.ltb_ge; lia.
Qed.

Lemma shift_plus_plus : forall l n i j,
  shift l n (i + j) = shift (shift l n i) (i + n) j.
Proof.
  induction l; intros n i j; [ reflexivity | ].
  simpl; rewrite IHl; f_equal; case_eq (a <? n); intros Heq.
  - case_eq (a <? i + n); intros Heq2; [ reflexivity | ].
    exfalso; apply Nat.ltb_lt in Heq; apply Nat.ltb_ge in Heq2; lia.
  - apply Nat.ltb_ge in Heq.
    case_eq (i + a <? i + n); intros Heq2; [ | lia ].
    exfalso; apply Nat.ltb_lt in Heq2; lia.
Qed.

Lemma shift_plus : forall l n i j,
  shift l n (i + j) = shift (shift l n i) n j.
Proof.
intros l n i j.
rewrite shift_plus_plus.
apply map_ext_in; intros a Hin.
apply In_nat_bool_In, shift_holeb in Hin.
now destruct (a <? n); rewrite Hin.
Qed.

Lemma shift_shift : forall l n i j,
  shift (shift l n i) n j = shift (shift l n j) n i.
Proof. intros; rewrite <- 2 shift_plus; f_equal; lia. Qed.

Lemma not_In_nat_bool_shift : forall l k i n, k <= n < i + k ->
  In_nat_bool n (shift l k i) = false.
Proof.
  induction l; intros k i n [Hle Hlt]; [ reflexivity | simpl ].
  case_eq (a <? k); intros Hlt2; simpl.
  - replace (n =? a) with false; [apply IHl; lia | ].
    symmetry; apply Nat.eqb_neq.
    apply Nat.ltb_lt in Hlt2; lia.
  - replace (n =? i + a) with false; [apply IHl; lia | ].
    symmetry; apply Nat.eqb_neq.
    apply Nat.ltb_nlt in Hlt2; lia.
Qed.

Lemma shift_In_nat_bool_lt : forall l n k i, n <? k = true ->
  In_nat_bool n (shift l k i) = In_nat_bool n l.
Proof with try reflexivity; try assumption.
  intros l; induction l; intros n k i Hlt...
  simpl.
  case_eq (a <? k); intros Hlt'.
  - case (n =? a)...
    rewrite IHl...
  - rewrite IHl...
    apply Nat.ltb_lt in Hlt.
    apply Nat.ltb_nlt in Hlt'.
    replace (n =? a) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (n =? i + a) with false...
    symmetry; apply Nat.eqb_neq; lia.
Qed.

Lemma shift_In_nat_bool_ge : forall l n k i, k <=? n = true ->
  In_nat_bool (i + n) (shift l k i) = In_nat_bool n l.
Proof with try reflexivity; try assumption.
  intros l; induction l; intros n k i Hge...
  simpl.
  case_eq (a <? k); intros Hlt.
  - rewrite IHl...
    apply Nat.ltb_lt in Hlt.
    apply Nat.leb_le in Hge.
    replace (i + n =? a) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (n =? a) with false...
    symmetry; apply Nat.eqb_neq; lia.
  - rewrite IHl...
    induction i...
Qed.

Lemma nth_shift_ge : forall l n k0 k i, n <= nth k l k0 ->
  nth k (shift l n i) (i + k0) = i + (nth k l k0).
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k i Hge.
  - simpl; destruct k; reflexivity.
  - destruct k; simpl; case_eq (a <? n); intros Hlt...
    + apply Nat.ltb_lt in Hlt.
      simpl in Hge.
      exfalso; lia.
    + now apply IHl.
    + now apply IHl.
Qed.

Lemma nth_shift_lt : forall l n k0 k i, nth k l k0 < n ->
  nth k (shift l n i) k0 = nth k l k0.
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k i Hlt; [ reflexivity | ].
  destruct k; simpl; case_eq (a <? n); intros Hlt'...
  - exfalso.
    simpl in Hlt.
    apply Nat.ltb_nlt in Hlt'; lia.
  - now apply IHl.
  - now apply IHl.
Qed.

Lemma le_nth_shift : forall l n k0 k i,
  nth k l k0 <= nth k (shift l n i) k0.
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k i...
  destruct k ; simpl.
  - case (a <? n); simpl; lia.
  - apply IHl.
Qed.

Lemma nth_ge_shift : forall l n k0 k i, n <= nth k (shift l n i) k0 ->
  nth k (shift l n i) (i + k0) = i + (nth k l k0).
Proof.
  induction l; intros n k0 k i Hgt; simpl; destruct k; try lia.
  - simpl in Hgt.
    case_eq (a <? n); intros Hlt; rewrite Hlt in Hgt; [ | reflexivity ].
    apply Nat.ltb_lt in Hlt.
    simpl in Hgt; lia.
  - now apply IHl.
Qed.

Lemma nth_lt_shift : forall l n k0 k i, nth k (shift l n i) k0 < n ->
  nth k (shift l n i) k0 = nth k l k0.
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k i Hlt; [ reflexivity | ].
  simpl; simpl in Hlt.
  destruct k.
  - case_eq (a <? n); intros Hlt'; rewrite Hlt' in Hlt...
    simpl in Hlt.
    apply Nat.ltb_nlt in Hlt'; lia.
  - now apply IHl.
Qed.

Lemma all_lt_shift : forall l n k i, k <=? n = true ->
  all_lt (shift l k i) (i + n) = all_lt l n.
Proof with try reflexivity; try assumption.
  intros l n k i Hleq; induction l...
  simpl.
  case_eq (a <? k); intros Hlt; simpl; rewrite IHl...
  - apply Nat.leb_le in Hleq.
    apply Nat.ltb_lt in Hlt.
    replace (a <? n) with true by (symmetry; apply Nat.ltb_lt; lia).
    replace (a <? i + n) with true by (symmetry; apply Nat.ltb_lt; lia)...
  - replace (i + a <? i + n) with (a <? n)...
    clear; induction i...
Qed.

Lemma all_lt_shift_true : forall l n k i,
  all_lt l n = true -> all_lt (shift l k i) (i + n) = true.
Proof.
intros l n k i.
induction l; simpl; intros Hlt; [ assumption | ].
apply andb_prop in Hlt as (Hlt & Hal).
apply andb_true_iff; split.
- apply Nat.ltb_lt in Hlt.
  destruct (a <? k); apply Nat.ltb_lt; lia.
- now apply IHl.
Qed.

Lemma shift_if_all_lt : forall l n i,
  all_lt l n = true -> shift l n i = l.
Proof with try reflexivity; try assumption.
  induction l; intros n i Hal...
  apply andb_prop in Hal as (Hlt & Hal); simpl.
  rewrite Hlt, IHl...
Qed.

Lemma all_distinct_shift : forall l k i,
  all_distinct (shift l k i) = all_distinct l.
Proof. intros l n i; apply all_distinct_map, incr_inj. Qed.

Lemma append_fun_all_lt : forall l1 l2 k n1 n2,
  all_lt l1 n1 = true -> all_lt l2 n2 = true ->
  all_lt (l1 ++ (shift l2 k n1)) (n1 + n2) = true.
Proof.
  intros l1 l2 k n1 n2 Hal1 Hal2.
  rewrite all_lt_app.
  apply andb_true_iff; split.
  - now apply all_lt_leq with n1; try lia.
  - now rewrite all_lt_shift_true.
Qed.

Lemma all_distinct_app_shift : forall l1 l2 k i,
  all_distinct l1 = true -> all_distinct l2 = true ->
  all_lt l2 i = true ->
  all_distinct (shift l1 k i ++ shift l2 0 k) = true.
Proof with try assumption.
  induction l1; intros l2 k i Had1 Had2 Hal2...
  - simpl; rewrite all_distinct_shift...
  - simpl in Had1; apply andb_prop in Had1 as [nHin Had1].
    specialize (IHl1 l2 k i Had1 Had2 Hal2).
    simpl; apply andb_true_intro; split...
    case_eq (a <? k); intros Hcase; apply negb_true_iff; rewrite In_nat_bool_app; apply orb_false_intro.
    + rewrite shift_In_nat_bool_lt...
      apply negb_true_iff...
    + apply Nat.ltb_lt in Hcase.
      apply not_In_nat_bool_shift; lia.
    + rewrite shift_In_nat_bool_ge; [ | apply Nat.ltb_nlt in Hcase; apply Nat.leb_le; lia ].
      apply negb_true_iff...
    + apply Nat.ltb_ge in Hcase.
      replace (i + a) with (k + (i + (a - k))) by lia.
      rewrite shift_In_nat_bool_ge; [ | apply Nat.leb_le; lia ].
      apply all_lt_In_nat_bool_false.
      now apply all_lt_leq with i; [ | lia ].
Qed.

Notation "f1 +++ f2" := (f1 ++ shift f2 0 (length f1)) (at level 61).

(** ** incr_all *)

Notation incr_all := (fun l i => shift l 0 i).

Lemma incr_all_S : forall l, incr_all l 1 = map S l.
Proof.
intros l; apply map_ext; intros x.
assert (x <? 0 = false) as Hz by (apply Nat.ltb_ge; lia); rewrite Hz; lia.
Qed.

Lemma nth_incr_all : forall l n n0 k,
  nth k (incr_all l n) (n + n0) = n + (nth k l n0).
Proof. intros; apply nth_shift_ge; lia. Qed.

Lemma In_nat_bool_incr_all : forall l k n,
  In_nat_bool (n + k) (incr_all l n) = In_nat_bool k l.
Proof. intros; apply shift_In_nat_bool_ge, Nat.leb_le; lia. Qed.

Lemma all_distinct_app : forall la lb k, all_lt la k = true ->
  all_distinct la = true -> all_distinct lb = true ->
  all_distinct (la ++ incr_all lb k) = true.
Proof with try reflexivity; try assumption.
  induction la; intros lb k Hal Hada Hadb.
  - simpl; rewrite all_distinct_shift...
  - simpl; simpl in Hada.
    apply andb_true_iff in Hada as (nHin & Hada).
    simpl in Hal.
    apply andb_true_iff in Hal as (Hlt & Hal).
    apply andb_true_intro; split.
    + apply negb_true_iff.
      rewrite In_nat_bool_app.
      apply orb_false_intro.
      * apply negb_true_iff...
      * apply Nat.ltb_lt in Hlt.
        apply not_In_nat_bool_shift; lia.
    + apply IHla...
Qed.


(** ** downshift *)

Notation down_nat := (fun n m => if n <? m then n else pred n).

Fixpoint downshift l k :=
  match l with
  | nil => nil
  | n :: l => if n =? k then downshift l k
              else down_nat n k :: downshift l k
  end.

Lemma downshift_eq : forall l k, downshift (k :: l) k = downshift l k.
Proof.
  intros l k; simpl.
  replace (k =? k) with true; [ reflexivity | ].
  symmetry; apply Nat.eqb_eq; reflexivity.
Qed.

Lemma downshift_gt : forall l k n, k <? n = true ->
  downshift (n :: l) k = (pred n) :: (downshift l k).
Proof.
  intros l k n Hlt.
  simpl.
  apply Nat.ltb_lt in Hlt.
  replace (n =? k) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (n <? k) with false by (symmetry; apply Nat.ltb_nlt; lia).
  reflexivity.
Qed.

Lemma downshift_In_nat_bool_lt : forall l n k, n <? k = true ->
  In_nat_bool n (downshift l k) = In_nat_bool n l.
Proof with try reflexivity; try assumption.
  induction l; intros n k Hlt...
  destruct (Compare_dec.lt_eq_lt_dec a k) as [[H1 | H2] | H3].
  - assert (a =? k = false) as Heq by (apply Nat.eqb_neq; lia).
    simpl; rewrite Heq.
    apply Nat.ltb_lt in H1.
    simpl; rewrite H1.
    rewrite (IHl n k Hlt)...
  - subst.
    rewrite (downshift_eq l k).
    assert (k <> n) as Hneq by (apply Nat.ltb_lt in Hlt; lia).
    rewrite (In_nat_bool_neq _ _ _ Hneq).
    apply IHl...
  - apply Nat.ltb_lt in H3 as Hlt2.
    rewrite (downshift_gt _ _ _ Hlt2).
    simpl; rewrite IHl...
    apply Nat.ltb_lt in Hlt.
    replace (n =? a) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (n =? pred a) with false by (symmetry; apply Nat.eqb_neq; lia)...
Qed.

Lemma downshift_In_nat_bool_gt : forall l n k,  k <? n = true ->
  In_nat_bool (pred n) (downshift l k) = In_nat_bool n l.
Proof with try reflexivity; try assumption.
  intros l; induction l; intros n k Hlt...
  destruct (Compare_dec.lt_eq_lt_dec a k) as [[H1 | H2] | H3].
  - assert (a =? k = false) as Hneq by (apply Nat.eqb_neq; lia).
    simpl; rewrite Hneq.
    apply Nat.ltb_lt in H1 as Hlt2.
    rewrite Hlt2.
    simpl; rewrite (IHl n k Hlt).
    apply Nat.ltb_lt in Hlt.
    replace (n =? a) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (pred n =? a) with false by (symmetry; apply Nat.eqb_neq; lia)...
  - subst.
    rewrite (downshift_eq l k).
    assert (k <> n) as Hneq by (apply Nat.ltb_lt in Hlt; lia).
    rewrite (In_nat_bool_neq _ _ _ Hneq).
    apply IHl...
  - apply Nat.ltb_lt in H3 as Hlt2.
    apply Nat.ltb_lt in Hlt.
    rewrite (downshift_gt _ _ _ Hlt2).
    destruct n; destruct a; try (exfalso; lia); simpl.
    apply Nat.ltb_lt in Hlt.
    rewrite<- (IHl (S n) k Hlt)...
Qed.

Lemma downshift_In_nat_bool_eq : forall l k,
  In_nat_bool k (downshift l k) = In_nat_bool (S k) l.
Proof.
intros l k.
etransitivity; [ | apply downshift_In_nat_bool_gt with (k := k) ].
- reflexivity.
- apply Nat.ltb_lt; lia.
Qed.

Lemma downshift_length : forall l n, In_nat_bool n l = false ->
  length (downshift l n) = length l.
Proof with try reflexivity; try assumption.
  intros l n nHin; induction l...
  simpl in nHin.
  apply orb_false_iff in nHin as (nHeq & nHin).
  rewrite Nat.eqb_sym in nHeq.
  simpl; rewrite nHeq.
  simpl; rewrite IHl...
Qed.

Lemma nth_downshift_ge : forall l n k0 k,
  In_nat_bool n l = false ->
  n <= nth k l k0 ->
  nth k (downshift l n) (pred k0) = pred (nth k l k0).
Proof.
intros l n k0 k nHin.
revert k; induction l; intros k Hge.
- simpl; destruct k; reflexivity.
- simpl in nHin; apply orb_false_iff in nHin as [nHin1 nHin2].
  rewrite Nat.eqb_sym in nHin1.
  simpl downshift; rewrite nHin1.
  destruct k; simpl; simpl in Hge.
  + now replace (a <? n) with false by (symmetry; apply Nat.ltb_nlt; intros H; lia).
  + now apply IHl.
Qed.

Lemma nth_downshift_lt : forall l n k0 k,
  In_nat_bool n l = false ->
  nth k l k0 < n ->
  nth k (downshift l n) k0 = nth k l k0.
Proof with try reflexivity; try assumption.
  intros l n k0 k nHin; revert k.
  induction l; intros k Hlt.
  - reflexivity.
  - simpl in nHin; apply orb_false_iff in nHin as [nHin1 nHin2].
    rewrite Nat.eqb_sym in nHin1.
    simpl downshift; rewrite nHin1.
    destruct k; simpl; simpl in Hlt.
    + apply Nat.ltb_lt in Hlt; rewrite Hlt; reflexivity.
    + now apply IHl.
Qed.

Lemma le_nth_downshift : forall l n k0 k,
  In_nat_bool n l = false ->
  nth k (downshift l n) k0 <= nth k l k0.
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin...
  destruct (orb_false_elim _ _ nHin) as (_ & nHin').
  simpl downshift.
  case_eq (a =? n); intros Heq.
  - simpl in nHin; rewrite Nat.eqb_sym in Heq; rewrite Heq in nHin; inversion nHin.
  - case (a <? n); destruct k; simpl; f_equal; (try now apply IHl); lia.
Qed.

Lemma nth_ge_downshift : forall l n k0 k,
  In_nat_bool n l = false ->
  n <= nth k (downshift l n) k0 ->
  nth k (downshift l n) (pred k0) = pred (nth k l k0).
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin Hgt.
  - simpl; destruct k; reflexivity.
  - simpl downshift in Hgt; simpl downshift.
    simpl in nHin; apply orb_false_iff in nHin as [nHin1 nHin2].
    rewrite Nat.eqb_sym in nHin1.
    rewrite nHin1; rewrite nHin1 in Hgt.
    destruct k; simpl.
    + case_eq (a <? n); intros Hlt; rewrite Hlt in Hgt...
      exfalso.
      apply Nat.ltb_lt in Hlt.
      simpl in Hgt; lia.
    + now apply IHl.
Qed.

Lemma nth_lt_downshift : forall l n k0 k,
  In_nat_bool n l = false ->
  nth k (downshift l n) k0 < n ->
  nth k (downshift l n) k0 = nth k l k0.
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin Hlt...
  simpl downshift; simpl downshift in Hlt.
  simpl in nHin; apply orb_false_iff in nHin as [nHin1 nHin2].
  rewrite Nat.eqb_sym in nHin1.
  rewrite nHin1; rewrite nHin1 in Hlt.
  destruct k; simpl.
  - case_eq (a <? n); intros Hlt2; rewrite Hlt2 in Hlt...
    exfalso.
    apply Nat.ltb_ge in Hlt2.
    apply Nat.eqb_neq in nHin1.
    simpl in Hlt; lia.
  - now apply IHl.
Qed.

Lemma all_lt_downshift : forall l n k, k <? S n = true ->
  all_lt (downshift l k) n = all_lt l (S n).
Proof.
intros l n k Heq; induction l; [ reflexivity | ].
simpl downshift.
apply Nat.ltb_lt in Heq.
case_eq (beq_nat a k); intros Heq2.
- rewrite IHl.
  simpl.
  replace (a <? S n) with true
    by (symmetry; apply Nat.eqb_eq in Heq2; apply Nat.ltb_lt; lia).
  reflexivity.
- simpl; f_equal; [ | assumption ].
  apply Nat.eqb_neq in Heq2.
  case_eq (a <? k); intros Heq3.
  + apply Nat.ltb_lt in Heq3.
    assert (a <? n = true) as Hn by (apply Nat.ltb_lt; lia).
    rewrite Hn; symmetry; apply Nat.ltb_lt; lia.
  + apply Nat.ltb_ge in Heq3.
    destruct a; [ exfalso; lia | reflexivity ].
Qed.

Lemma downshift_keep_all_distinct : forall l k,
  all_distinct l = true -> all_distinct (downshift l k) = true.
Proof with try reflexivity; try assumption.
  intros l k; induction l; intros Hal; simpl in Hal...
  destruct (Compare_dec.lt_eq_lt_dec a k) as [ [H1 | H2] | H3 ].
  - assert (a =? k = false) as Hneq by (apply Nat.eqb_neq; lia).
    simpl downshift; rewrite Hneq.
    apply Nat.ltb_lt in H1.
    simpl; rewrite H1.
    apply andb_prop in Hal as (nHin & Hal).
    apply andb_true_intro; split.
    + rewrite downshift_In_nat_bool_lt...
    + apply IHl...
  - subst.
    rewrite downshift_eq.
    apply andb_prop in Hal as (nHin & Hal).
    apply IHl...
  - apply andb_prop in Hal as (nHin & Hal).
    rewrite downshift_gt by (apply Nat.ltb_lt; assumption).
    simpl; apply andb_true_intro; split.
    + rewrite downshift_In_nat_bool_gt by (apply Nat.ltb_lt; apply H3)...
    + apply IHl...
Qed.

Lemma downshift_app : forall l1 l2 n,
  downshift (l1 ++ l2) n = downshift l1 n ++ downshift l2 n.
Proof with try reflexivity; try assumption.
  induction l1; intros l2 n...
  simpl.
  rewrite (IHl1 l2 n).
  case (a =? n)...
Qed.

Lemma downshift_if_all_lt : forall l n,
  all_lt l n = true -> downshift l n = l.
Proof with try reflexivity; try assumption.
  induction l; intros n Hal...
  simpl in Hal; apply andb_prop in Hal as (Hlt & Hal).
  apply Nat.ltb_lt in Hlt as Hlt2.
  simpl.
  replace (beq_nat a n) with false by (symmetry; apply Nat.eqb_neq; lia).
  rewrite Hlt.
  rewrite IHl...
Qed.

Lemma downshift_incr_all : forall l n,
  downshift (incr_all l (S n)) n = incr_all l n.
Proof with try reflexivity; try assumption.
induction l...
intro n; simpl shift.
rewrite downshift_gt by (apply Nat.ltb_lt; lia).
now rewrite IHl.
Qed.

Lemma downshift_shift : forall l n,
  downshift (shift l n 1) n = l.
Proof with try reflexivity; try assumption.
  induction l; intros n...
  simpl.
  replace (beq_nat (if a <? n then a else S a) n) with false; case_eq (a <? n); intros Hlt.
  - simpl.
    rewrite Hlt.
    rewrite IHl...
  - apply Nat.ltb_nlt in Hlt.
    replace (S a <? n) with false by (symmetry; apply Nat.ltb_nlt; lia).
    now rewrite IHl.
  - apply Nat.ltb_lt in Hlt; symmetry; apply Nat.eqb_neq; lia.
  - apply Nat.ltb_ge in Hlt; symmetry; apply Nat.eqb_neq; lia.
Qed.

Lemma shift_downshift : forall l n, In_nat_bool n l = false ->
  shift (downshift l n) n 1 = l.
Proof with try reflexivity; try assumption.
  induction l; intros n nHin...
  simpl in nHin; apply orb_false_iff in nHin as (nHeq & nHin).
  simpl; rewrite Nat.eqb_sym in nHeq; rewrite nHeq.
  case_eq (a <? n); intros Hlt.
  - simpl; rewrite Hlt, IHl...
  - apply Nat.eqb_neq in nHeq.
    apply Nat.ltb_ge in Hlt.
    simpl; rewrite IHl...
    f_equal; replace (pred a <? n) with false; [ lia | ].
    symmetry; apply Nat.ltb_ge; lia.
Qed.

Lemma downshift_nth : forall l1 l2 a0 k1 k2,
  k1 < length l1 ->
  In_nat_bool k2 l1 = false ->
  downshift ((nth k1 l1 a0) :: l2) k2 = (nth k1 (downshift l1 k2) a0 :: (downshift l2 k2)).
Proof.
  induction l1; intros l2 a0 k1 k2 Hlen nHin; try now inversion Hlen.
  simpl in nHin; apply orb_false_iff in nHin as [nHin1 nHin2].
  rewrite Nat.eqb_sym in nHin1.
  destruct k1.
  - change (nth 0 (a :: l1) a0) with a.
    simpl downshift.
    rewrite nHin1.
    case_eq (a <? k2); intros Hlt; reflexivity.
  - change (nth (S k1) (a :: l1) a0) with (nth k1 l1 a0).
    replace (nth (S k1) (downshift (a :: l1) k2) a0) with (nth k1 (downshift l1 k2) a0)
      by (now simpl downshift; rewrite nHin1).
    now simpl in Hlen; apply IHl1; try lia.
Qed.

Lemma downshift_inj : forall k l1 l2,
  In_nat_bool k l1 = false -> In_nat_bool k l2 = false ->
  downshift l1 k = downshift l2 k -> l1 = l2.
Proof.
  intros k; induction l1; intros l2 nHin1 nHin2 Heq.
  - destruct l2; [reflexivity | ].
    simpl in Heq; simpl in nHin2; apply orb_false_iff in nHin2 as [nHeq _].
    rewrite Nat.eqb_sym in nHeq; rewrite nHeq in Heq; inversion Heq.
  - destruct l2.
    + simpl in Heq; simpl in nHin1; apply orb_false_iff in nHin1 as [nHeq _].
      rewrite Nat.eqb_sym in nHeq; rewrite nHeq in Heq; inversion Heq.
    + simpl in *.
      apply orb_false_iff in nHin1 as [nHeq1 nHin1].
      apply orb_false_iff in nHin2 as [nHeq2 nHin2].
      rewrite Nat.eqb_sym in nHeq1, nHeq2; rewrite nHeq1 in Heq; rewrite nHeq2 in Heq.
      inversion Heq.
      rewrite (IHl1 l2 nHin1 nHin2 H1).
      replace a with n; [reflexivity | ].
      apply Nat.eqb_neq in nHeq1;  apply Nat.eqb_neq in nHeq2.
      revert H0.
      case_eq (a <? k); intro Hc1; case_eq (n <? k); intro Hc2;
        [ apply Nat.ltb_lt in Hc1; apply Nat.ltb_lt in Hc2
        | apply Nat.ltb_lt in Hc1; apply Nat.ltb_nlt in Hc2
        | apply Nat.ltb_nlt in Hc1; apply Nat.ltb_lt in Hc2
        | apply Nat.ltb_nlt in Hc1; apply Nat.ltb_nlt in Hc2];
        try lia.
Qed.

(* UIP, eq_dec, ...*)
Lemma UIP_nat : forall (n1 n2 : nat) (p1 p2 : n1 = n2), p1 = p2.
Proof. intros; apply Eqdep_dec.UIP_dec, Nat.eq_dec. Qed.

Lemma list_nat_eq_dec : forall (l1 l2 : list nat), {l1 = l2} + {l1 <> l2}.
Proof. intros; apply list_eq_dec, Nat.eq_dec. Qed.

Lemma UIP_list_nat : forall (l1 l2 : list nat) (p1 p2 : l1 = l2), p1 = p2.
Proof. intros; apply Eqdep_dec.UIP_dec, list_nat_eq_dec. Qed.

Fixpoint list_nat_eqb (l1 l2 : list nat) :=
  match l1, l2 with
  | nil, nil => true
  | n1 :: l1, n2 :: l2 => (n1 =? n2) && list_nat_eqb l1 l2
  | _, _ => false
  end.

Lemma list_nat_eqb_eq : forall l1 l2, list_nat_eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1; intros l2; split; destruct l2; intros Heq; try now inversion Heq.
  - simpl in Heq; apply andb_prop in Heq as [Heqn Heq].
    apply Nat.eqb_eq in Heqn.
    specialize (IHl1 l2) as [IHl1 _]; rewrite IHl1; now subst...
  - inversion Heq; subst.
    specialize (IHl1 l2) as [_ IHl1]; simpl; rewrite Nat.eqb_refl; now rewrite IHl1.
Qed.

Lemma list_nat_eqb_neq : forall l1 l2, list_nat_eqb l1 l2 = false <-> l1 <> l2.
Proof.
  intros l1 l2.
  case_eq (list_nat_eqb l1 l2); intros H; split.
  - intros H'; inversion H'.
  - intros Hneq; exfalso; apply Hneq; now apply list_nat_eqb_eq.
  - intros _ Heq; rewrite (proj2 (list_nat_eqb_eq _ _) Heq) in H; inversion H.
  - trivial.
Qed.

