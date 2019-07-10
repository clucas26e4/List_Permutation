Require Import Lia.
Require Import PeanoNat.
Require Import EqNat.
Require Import Injective.

Require Import Bool_more.
Require Import List_more.
Require Import List_manip.
Require Import Permutation_more.

Ltac splitb := apply andb_true_intro; split.

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

(** ** incr_all *)

Definition incr_all l k := map (fun x => k + x) l.

Lemma incr_all_max : forall l k i,
    l <> nil ->
    fold_left max (incr_all l k) i = k + (fold_left max l (i - k)).
Proof with try assumption; try reflexivity.
  induction l; intros k i Hnnil.
  - exfalso.
    apply Hnnil...
  - simpl.
    destruct l.
    + simpl.
      lia.
    + rewrite IHl.
      2:{ intros H; inversion H. }
      replace (max i (k + a) - k) with (max (i - k) a) by lia...
Qed.
      
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

Lemma incr_all_length : forall l n,
    length (incr_all l n) = length l.
Proof with try reflexivity.
  intros l n.
  unfold incr_all; apply map_length.
Qed.

Lemma incr_all_incr_all : forall l n m,
    incr_all (incr_all l n) m = incr_all (incr_all l m) n.
Proof with try reflexivity; try assumption.
  induction l; intros n m...
  simpl.
  rewrite IHl.
  replace (m + (n + a)) with (n + (m + a))...
  lia.
Qed.

Lemma incr_all_0 : forall l,
    incr_all l 0 = l.
Proof with try reflexivity; try assumption.
  induction l...
  simpl; rewrite IHl...
Qed.

Lemma incr_all_plus : forall l n m,
    incr_all l (n + m) = incr_all (incr_all l n) m.
Proof with try reflexivity; try assumption.
  induction l; intros n m...
  simpl.
  rewrite Nat.add_assoc.
  rewrite IHl.
  rewrite (Nat.add_comm n m)...
Qed.

Lemma incr_all_app : forall l1 l2 n,
    incr_all (l1 ++ l2) n = incr_all l1 n ++ incr_all l2 n.
Proof with try reflexivity; try assumption.
  induction l1; intros l2 n...
  simpl.
  rewrite IHl1...
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

(** ** In_nat_bool *)

Fixpoint In_nat_bool (n : nat) (l : list nat) :=
  match l with
  | nil => false
  | k :: l => (beq_nat n k) || (In_nat_bool n l)
  end.

Lemma In_nat_bool_false_tail : forall l n k,
    In_nat_bool n (k :: l) = false ->
    In_nat_bool n l = false.
Proof with try reflexivity; try assumption.
  intros l n k nHin.
  unfold In_nat_bool in nHin.
  change ((fix In_nat_bool (n : nat) (l : list nat) {struct l} : bool :=
               match l with
               | nil => false
               | k :: l0 => (n =? k) || In_nat_bool n l0
               end) n l) with (In_nat_bool n l) in nHin.
  case_eq (In_nat_bool n l); intro Heq...
  revert nHin; case (n =? k); intro nHin; rewrite Heq in nHin; inversion nHin.
Qed. 

Lemma neg_nth_eq : forall l n k0 k,
    In_nat_bool n l = false ->
    k < length l ->
    nth k l k0 <> n.
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin Hlt Heq.
  - inversion Hlt.
  - destruct k.
    + simpl in Heq.
      unfold In_nat_bool in nHin.
      replace (n =? a) with true in nHin ; [inversion nHin | ].
      symmetry; apply Nat.eqb_eq; symmetry...
    + simpl in Heq.
      simpl in Hlt; apply Lt.lt_S_n in Hlt.
      refine (IHl n k0 _ _ Hlt _)...
      apply In_nat_bool_false_tail with a...
Qed.

Lemma cond_negb_In_nat_bool : forall l n,
    (forall k k0,
        k < length l ->
        nth k l k0 <> n) <->
    In_nat_bool n l = false.
Proof with try reflexivity; try assumption.
  intros l n; split; revert n.
  - induction l; intros n H...
    unfold In_nat_bool.
    case_eq (n =? a); intro Heq.
    + exfalso.
      refine (H 0 0 _ _)...
      * simpl; lia.
      * apply Nat.eqb_eq in Heq.
        symmetry...
    + simpl.
      change ((fix In_nat_bool (n0 : nat) (l0 : list nat) {struct l0} : bool :=
                 match l0 with
                 | nil => false
                 | k :: l1 => (n0 =? k) || In_nat_bool n0 l1
                 end) n l) with (In_nat_bool n l).
      refine (IHl n _).
      intros k k0 Hlt Heq'.
      refine (H (S k) k0 _ _)...
      simpl; apply Lt.lt_n_S...
  - induction l; intros n nHin k k0 Hlt Heq.
    + inversion Hlt.
    + destruct k.
      * simpl in Heq.
        unfold In_nat_bool in nHin.
        replace (n =? a) with true in nHin ; [inversion nHin | ].
        symmetry; apply Nat.eqb_eq; symmetry in Heq...
      * simpl in Heq , Hlt.
        apply Lt.lt_S_n in Hlt.
        unfold In_nat_bool in nHin.
        change ((fix In_nat_bool (n : nat) (l : list nat) {struct l} : bool :=
               match l with
               | nil => false
               | k :: l0 => (n =? k) || In_nat_bool n l0
               end) n l) with (In_nat_bool n l) in nHin.
        revert nHin; case (n =? a); intro nHin; try now inversion nHin.
        refine (IHl _ nHin _ _ Hlt Heq).        
Qed.

Lemma cond_In_nat_bool : forall l n,
    {'(k0 , k) : _ & prod (k < length l) (nth k l k0 = n) } ->
    In_nat_bool n l = true.
Proof with try assumption; try reflexivity.
  intros l n x.
  destruct x as ((k0 & k) & (Hlt & Heq)).
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

Lemma In_nat_bool_incr_all : forall l k n,
    In_nat_bool k l = In_nat_bool (n + k) (incr_all l n).
Proof with try reflexivity; try assumption.
  induction l; intros k n...
  assert ((k =? a) = (n + k =? n + a)).
  { case_eq (k =? a); intro Heq.
    - apply Nat.eqb_eq in Heq; subst.
      symmetry; apply Nat.eqb_eq...
    - symmetry.
      apply Nat.eqb_neq.
      intro Heq'.
      apply Plus.plus_reg_l in Heq'; subst.
      apply Nat.eqb_neq in Heq.
      apply Heq... }
  unfold In_nat_bool.
  rewrite H.
  simpl.
  change ((fix In_nat_bool (n0 : nat) (l0 : list nat) {struct l0} : bool :=
        match l0 with
        | nil => false
        | k0 :: l1 => (n0 =? k0) || In_nat_bool n0 l1
        end) k l) with (In_nat_bool k l).
  rewrite (IHl k n)...
Qed.

Lemma negb_In_incr_all : forall l k n,
    k < n ->
    In_nat_bool k (incr_all l n) = false.
Proof with try reflexivity; try assumption.
  induction l; intros k n Hlt...
  simpl.
  assert (k =? n + a = false).
  { apply Nat.eqb_neq.
    intros Heq.
    clear - Hlt Heq.
    revert k Hlt Heq.
    induction n; intros k Hlt Heq.
    - inversion Hlt.
    -  destruct k.
       + inversion Heq.
       + apply Lt.lt_S_n in Hlt.
         inversion Heq.
         apply IHn with k... }
  rewrite H.
  apply IHl...
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
    replace ((b =? a0) || ((b =? a) || In_nat_bool b (l1 ++ l2))) with (((b =? a0) || In_nat_bool b (l1 ++ l2)) || (b =? a)).
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

Lemma In_nat_bool_Perm: forall l1 l2 a,
    Permutation l1 l2 ->
    In_nat_bool a l1 = In_nat_bool a l2.
Proof with try reflexivity; try assumption.
  intros l1 l2 a Hp.
  induction Hp...
  - simpl; rewrite IHHp...
  - simpl.
    case (a =? y) ; case (a =? x)...
  - transitivity (In_nat_bool a l')...
Qed.
                                
(** ** all_lt *)

Fixpoint all_lt (l : list nat) (n : nat) :=
  match l with
  | nil => true
  | k :: l => (k <? n) && (all_lt l n)
  end.

Lemma all_lt_leq : forall l k n,
    all_lt l k = true ->
    k <= n ->
    all_lt l n = true.
Proof with try reflexivity; try assumption.
  induction l; intros k n Hal Hleq...
  destruct (andb_prop _ _ Hal).
  splitb.
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
      unfold all_lt.
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
  - unfold all_lt in nHalt.
    case_eq (a <? n); intros Hlt.
    + rewrite Hlt in nHalt.
      simpl in nHalt.
      destruct (IHl n nHalt k0) as (k & (Hlen & Hgeq)).
      split with (S k).
      split...
      simpl.
      apply Lt.lt_n_S...
    + split with 0.
      split.
      * simpl; lia.
      * apply Nat.ltb_nlt in Hlt.
        simpl; lia.
Qed.

Lemma all_lt_middle_true : forall l1 l2 a k,
    all_lt (l1 ++ a :: l2) k = true ->
    all_lt (l1 ++ l2) k = true.
Proof with try reflexivity; try assumption.
  induction l1; intros l2 b k H.
  - apply andb_prop in H as (_ & H)...
  - apply andb_prop in H as (H1 & H2).
    simpl.
    rewrite H1.
    refine (IHl1 _ _ _ H2).
Qed.

Lemma cond_all_lt : forall l n,
    (forall k0 k,
        k < length l ->
        nth k l k0 < n) ->
    all_lt l n = true.
Proof with try reflexivity; try assumption.
  intros l n.
  induction l; intros H...
  splitb.
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
    simpl in Hlt.
    lia.
Qed.

Lemma all_lt_incr_all : forall l n1 n2,
    all_lt l n1 = all_lt (incr_all l n2) (n2 + n1).
Proof with try reflexivity; try assumption.
  induction l; intros n1 n2...
  simpl.
  rewrite (IHl n1 n2).
  assert (a <? n1 = (n2 + a <? n2 + n1)).
  { case_eq (a <? n1); intros Hleq; symmetry.
    - apply Nat.ltb_lt.
      apply Nat.ltb_lt in Hleq.
      apply Plus.plus_lt_compat_l...
    - apply Nat.ltb_nlt in Hleq.
      apply Nat.ltb_nlt.
      intro Hlt.
      apply Hleq.
      apply Plus.plus_lt_reg_l with n2... }
  rewrite H...
Qed.

Lemma all_lt_Id : forall n, all_lt (Id n) n = true.
Proof with try reflexivity; try assumption.
  induction n...
  simpl; rewrite<- all_lt_incr_all...
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
  apply Nat.ltb_lt in Hlt.
  lia.
Qed.
  
(** ** all_distinct *)

Fixpoint all_distinct (l : list nat) :=
  match l with
  | nil => true
  | n :: l => (negb (In_nat_bool n l)) && (all_distinct l)
  end.

Lemma all_distinct_incr_all : forall l n,
    all_distinct l = all_distinct (incr_all l n).
Proof with try reflexivity; try assumption.
  induction l; intros n...
  simpl.
  rewrite (In_nat_bool_incr_all l a n).
  rewrite (IHl n)...
Qed.

Lemma all_distinct_Id : forall n,
    all_distinct (Id n) = true.
Proof with try reflexivity; try assumption.
  induction n...
  splitb.
  + apply negb_true_iff.
    apply negb_In_incr_all.
    apply Nat.lt_0_1.
  + rewrite<- all_distinct_incr_all...
Qed.

Lemma cond_all_distinct : forall l,
    (forall n1 n2 k,
        n1 < length l ->
        n2 < length l ->
        (nth n1 l k) = (nth n2 l k) ->
        n1 = n2) ->
    all_distinct l = true.
Proof with try assumption; try reflexivity.
  induction l; intros H...
  splitb.
  + apply negb_true_iff.
    apply cond_negb_In_nat_bool.
    intros k k0 Hlt Heq.
    refine (Nat.neq_succ_0 k _).
    refine (H (S k) 0 k0 _ _ _)...
    * simpl; lia.
    * simpl; lia.
  + change ((fix all_distinct (l0 : list nat) : bool :=
               match l0 with
               | nil => true
               | n :: l1 => negb (In_nat_bool n l1) && all_distinct l1
               end) l) with (all_distinct l).
    refine (IHl _).
    intros n1 n2 k Hlt1 Hlt2 Heq.
    apply Nat.succ_inj.
    refine (H (S n1) (S n2) k _ _ _); try now (simpl; lia)...
Qed.

Lemma cond_all_distinct_inv : forall l,
    all_distinct l = true -> (forall n1 n2 k,
                                  n1 < length l ->
                                  n2 < length l ->
                                  (nth n1 l k) = (nth n2 l k) ->
                                  n1 = n2).
Proof with try assumption; try reflexivity.
  induction l; intros Hal n1 n2 k Hlt1 Hlt2 Heq.
  + destruct n1; inversion Hlt1.
  + destruct n1; destruct n2...
    * simpl in Heq.
      simpl in Hlt2; apply Lt.lt_S_n in Hlt2.
      exfalso.
      refine (neg_nth_eq l a k n2 _ _ _)...
      -- apply andb_prop in Hal as (H1 & _).
         apply negb_true_iff in H1...
      -- symmetry...
    * simpl in Heq.
      simpl in Hlt1; apply Lt.lt_S_n in Hlt1.
      exfalso.
      refine (neg_nth_eq l a k n1 _ _ _)...
      apply andb_prop in Hal as (H1 & _).
      apply negb_true_iff in H1...
    * simpl in *.
      apply Lt.lt_S_n in Hlt1.
      apply Lt.lt_S_n in Hlt2.
      apply eq_S.
      apply andb_prop in Hal as (_ & H2).
      refine (IHl _ _ _ k _ _ _)...
Qed.

Lemma all_distinct_no_head : forall l n,
    all_distinct (n :: l) = true ->
    forall k k0,
      k < length l ->
      nth k l k0 <> n.
Proof with try reflexivity; try assumption.
  intros l n Hal k k0 Hlt.
  apply andb_prop in Hal as (nHin & Hal).
  change ((fix all_distinct (l : list nat) : bool :=
           match l with
           | nil => true
           | n :: l0 => negb (In_nat_bool n l0) && all_distinct l0
           end) l) with (all_distinct l) in Hal.
  refine (neg_nth_eq l n k0 k _ Hlt).
  apply negb_true_iff...
Qed.

Lemma cond_all_distinct_false : forall l k0 k1 k2,
    k1 < length l ->
    k2 < length l ->
    k1 <> k2 ->
    nth k1 l k0 = nth k2 l k0 ->
    all_distinct l = false.
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
    split.
    + simpl in Hlt2; lia.
    + simpl in Heq; rewrite Heq...
  - simpl.
    replace (negb (In_nat_bool a l)) with false...
    symmetry.
    apply negb_false_iff.
    apply cond_In_nat_bool.
    split with (k0 , k1).
    split.
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
    {' (k1 , k2) : _ & prod (k1 < length l) (prod (k2 < length l) (prod (k1 <> k2) (nth k1 l k0 = nth k2 l k0)))}.
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

Lemma all_distinct_left : forall la lb k,
    all_distinct (la ++ k :: lb) = true ->
    In_nat_bool k la = false.
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
    all_distinct (la ++ k :: lb) = true ->
    In_nat_bool k lb = false.
Proof with try reflexivity; try assumption.
  induction la; intros lb k Had.
  - apply andb_prop in Had as (nHin & Had).
    apply negb_true_iff in nHin...
  - apply andb_prop in Had as (_ & Had).
    apply IHla...    
Qed.

Lemma all_distinct_app : forall la lb k,
    all_lt la k = true ->
    all_distinct la = true ->
    all_distinct lb = true ->
    all_distinct (la ++ incr_all lb k) = true.
Proof with try reflexivity; try assumption.
  induction la; intros lb k Hal Hada Hadb.
  - simpl; rewrite<- all_distinct_incr_all...
  - simpl.
    simpl in Hada.
    apply andb_true_iff in Hada as (nHin & Hada).
    simpl in Hal.
    apply andb_true_iff in Hal as (Hlt & Hal).
    apply andb_true_intro.
    split.
    + apply negb_true_iff.
      rewrite In_nat_bool_app.
      apply orb_false_intro.
      * apply negb_true_iff...
      * apply negb_In_incr_all.
        apply Nat.ltb_lt...
    + apply IHla...
Qed.

Lemma all_distinct_Perm : forall l l',
    Permutation l l' ->
    all_distinct l = all_distinct l'.
Proof with try assumption; try reflexivity.
  intros l l' Hp.
  induction Hp...
  - unfold all_distinct; fold all_distinct.
    rewrite IHHp.
    rewrite In_nat_bool_Perm with _ l' _...
  - simpl.
    rewrite 2 negb_orb.
    case_eq (y =? x); intro H.
    + replace (x =? y) with true...
      rewrite Nat.eqb_sym.
      rewrite H...
    + replace (x =? y) with false.
      2:{ rewrite Nat.eqb_sym.
          rewrite H... }
      case (In_nat_bool y l); case (In_nat_bool x l)...
  - transitivity (all_distinct l')...
Qed.

(** ** shift *)
Fixpoint shift l k :=
  match l with
  | nil => nil
  | n :: l => if n <? k then (n :: shift l k) else ((S n) :: shift l k)
  end.

Lemma shift_ge : forall l k n,
    k <=? n = true ->
    shift (n :: l) k = (S n) :: (shift l k).
Proof with try reflexivity; try assumption.
  intros l k n Hge.
  simpl.
  apply Nat.leb_le in Hge.
  replace (n <? k) with false...
  symmetry.
  apply Nat.ltb_nlt.
  lia.
Qed.
  
Lemma shift_In_nat_bool_lt : forall l n k,
    n <? k = true ->
    In_nat_bool n (shift l k) = In_nat_bool n l.
Proof with try reflexivity; try assumption.
  intros l; induction l; intros n k Hlt...
  simpl.
  case_eq (a <? k); intros Hlt'.
  - simpl.
    case (n =? a)...
    rewrite IHl...
  - simpl.
    rewrite IHl...
    apply Nat.ltb_lt in Hlt.
    apply Nat.ltb_nlt in Hlt'.
    replace (n =? a) with false.
    2:{ symmetry.
        apply Nat.eqb_neq.
        lia. }
    replace (n =? S a) with false...
    symmetry.
    apply Nat.eqb_neq.
    lia.
Qed.
  
Lemma shift_In_nat_bool_ge : forall l n k,
    k <=? n = true ->
    In_nat_bool (S n) (shift l k) = In_nat_bool n l.
Proof with try reflexivity; try assumption.
  intros l; induction l; intros n k Hge...
  simpl.
  case_eq (a <? k); intros Hlt.
  - simpl.
    change (match a with
            | 0 => false
            | S m' => n =? m'
            end) with (S n =? a).
    rewrite IHl...
    apply Nat.ltb_lt in Hlt.
    apply Nat.leb_le in Hge.
    replace (S n =? a) with false.
    2:{ symmetry.
        apply Nat.eqb_neq.
        lia. }
    replace (n =? a) with false...
    symmetry.
    apply Nat.eqb_neq.
    lia.
  - simpl.
    rewrite IHl...
Qed.

Lemma shift_In_nat_bool_eq : forall l k,
    In_nat_bool (S k) (shift l k) = In_nat_bool k l.
Proof with try reflexivity; try assumption.
  induction l; intro k...
  simpl.
  case_eq (a <? k); intros Hlt.
  - simpl.
    change ( match a with
             | 0 => false
             | S m' => k =? m'
             end) with (S k =? a).
    rewrite IHl.
    apply Nat.ltb_lt in Hlt.
    replace (S k =? a) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (k =? a) with false by (symmetry; apply Nat.eqb_neq; lia)...
  - simpl; rewrite IHl...
Qed.  

Lemma shift_length : forall l n,
    length (shift l n) = length l.
Proof with try reflexivity; try assumption.
  intros l n; induction l...
  simpl; case (a <? n); simpl; rewrite IHl...
Qed.

Lemma nth_shift_ge : forall l n k0 k,
    In_nat_bool n l = false ->
    k < length l ->
    n <= nth k l k0 ->
    nth k (shift l n) k0 = S (nth k l k0).
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin Hlen Hge.
  - inversion Hlen.
  - destruct k.
    + simpl.
      case_eq (a <? n); intros Hlt...
      apply Nat.ltb_lt in Hlt.
      simpl in Hge.
      exfalso.
      lia.
    + simpl.
      case_eq (a <? n); intros Hlt.
      * apply orb_false_elim in nHin as (_ & nHin).
        apply Lt.lt_S_n in Hlen.
        refine (IHl _ _ _ nHin Hlen Hge).
      * case_eq (a =? n); intros Heq.
        -- simpl in nHin.
           replace (n =? a) with true in nHin; try now inversion nHin.
           symmetry.
           rewrite Nat.eqb_sym...
        -- apply orb_false_elim in nHin as (_ & nHin).
           apply Lt.lt_S_n in Hlen.
           refine (IHl _ _ _ nHin Hlen Hge).
Qed.  

Lemma nth_shift_lt : forall l n k0 k,
    In_nat_bool n l = false ->
    k < length l ->
    nth k l k0 < n ->
    nth k (shift l n) k0 = (nth k l k0).
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin Hlen Hlt.
  - inversion Hlen.
  - destruct k.
    + simpl.
      case_eq (a <? n); intros Hlt'...
      simpl in Hlt.
      apply Nat.ltb_nlt in Hlt'.
      exfalso; lia.
    + simpl.
      case_eq (a <? n); intros Hlt'.
      * apply orb_false_elim in nHin as (_ & nHin).
        apply Lt.lt_S_n in Hlen.
        refine (IHl _ _ _ nHin Hlen Hlt).
      * case_eq (a =? n); intros Heq.
        -- simpl in nHin.
           replace (n =? a) with true in nHin; try now inversion nHin.
           symmetry.
           rewrite Nat.eqb_sym...
        -- apply orb_false_elim in nHin as (_ & nHin).
           apply Lt.lt_S_n in Hlen.
           refine (IHl _ _ _ nHin Hlen Hlt).
Qed.

Lemma le_nth_shift : forall l n k0 k,
    nth k l k0 <= nth k (shift l n) k0.
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k...
  destruct k ; simpl.
  - case (a <? n); simpl; lia.
  - case (a <? n); simpl; apply IHl.  
Qed.

Lemma nth_ge_shift : forall l n k0 k,
    k < length l ->
    n <= nth k (shift l n) k0 ->
    nth k (shift l n) k0 = S (nth k l k0).
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k Hlen Hgt.
  - inversion Hlen.
  - simpl in Hgt.
    simpl.
    destruct k.
    + case_eq (a <? n); intros Hlt; rewrite Hlt in Hgt...
      apply Nat.ltb_lt in Hlt.
      simpl in Hgt.
      lia.
    + case_eq (a <? n); intros Hlt; rewrite Hlt in Hgt; apply Lt.lt_S_n in Hlen; refine (IHl _ _ _ Hlen Hgt).
Qed.  

Lemma nth_lt_shift : forall l n k0 k,
    k < length l ->
    nth k (shift l n) k0 < n ->
    nth k (shift l n) k0 = (nth k l k0).
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k Hlen Hlt.
  - inversion Hlen.
  - simpl.
    simpl in Hlt.
    destruct k.
    + case_eq (a <? n); intros Hlt'; rewrite Hlt' in Hlt...
      simpl in Hlt.
      apply Nat.ltb_nlt in Hlt'.
      lia.
    + case_eq (a <? n); intros Hlt'; rewrite Hlt' in Hlt; apply Lt.lt_S_n in Hlen; refine (IHl _ _ _ Hlen Hlt).
Qed.

Lemma shift_all_lt : forall l n k,
    k <=? n = true ->
    all_lt l n = all_lt (shift l k) (S n).
Proof with try reflexivity; try assumption.
  intros l n k Hleq; induction l...
  simpl.
  case_eq (a <? k); intros Hlt; simpl; rewrite IHl...
  apply Nat.leb_le in Hleq.
  apply Nat.ltb_lt in Hlt.
  replace (a <? n) with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (a <? S n) with true by (symmetry; apply Nat.ltb_lt; lia)...
Qed.

Lemma shift_keep_all_distinct : forall l k,
    all_distinct l = true ->
    all_distinct (shift l k) = true.
Proof with try reflexivity; try assumption.
  induction l; intros k Hal...
  simpl in Hal |- *.
  case_eq (a <? k); intros Hlt; simpl; splitb.
  - apply andb_prop in Hal as (nHin & _).
    rewrite shift_In_nat_bool_lt...
  - apply andb_prop in Hal as (_ & Hal).
    apply IHl...
  - apply andb_prop in Hal as (nHin & _).
    rewrite shift_In_nat_bool_ge...
    apply Nat.leb_le.
    apply Nat.ltb_nlt in Hlt.
    lia.
  - apply andb_prop in Hal as (_ & Hal).
    apply IHl...
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

Lemma shift_incr_all : forall l n,
    shift (incr_all l (S n)) n = incr_all l (S (S n)).
Proof with try reflexivity; try assumption.
  induction l...
  simpl.
  intro n.
  replace (S (n + a) <? n ) with false.
  2:{ symmetry.
      apply Nat.ltb_nlt.
      lia. }
  rewrite (IHl n).
  destruct n...
Qed.

Lemma shift_app : forall l1 l2 n,
    shift (l1 ++ l2) n = shift l1 n ++ shift l2 n.
Proof with try reflexivity; try assumption.
  induction l1; intros l2 n...
  simpl.
  rewrite (IHl1 l2 n).
  case (a <? n)...
Qed.

Lemma shift_if_all_lt : forall l n,
    all_lt l n = true ->
    shift l n = l.
Proof with try reflexivity; try assumption.
  induction l; intros n Hal...
  apply andb_prop in Hal as (Hlt & Hal).
  simpl.
  rewrite Hlt.
  rewrite IHl...
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
  
(** ** downshift *)
Fixpoint downshift l k :=
  match l with
  | nil => nil
  | n :: l => if n <? k then (n :: downshift l k) else (if n =? k then downshift l k else (pred n) :: downshift l k)
  end.

Definition down_nat n m := if n <? m then n else pred n.

Lemma downshift_eq : forall l k, downshift (k :: l) k = downshift l k.
Proof with try reflexivity; try assumption.
  intro l; intros k.
  simpl.
  replace (k <? k) with false.
  2:{ symmetry.
      apply Nat.ltb_nlt.
      lia. }
  replace (k =? k) with true...
  symmetry.
  apply Nat.eqb_eq...
Qed.

Lemma downshift_gt : forall l k n,
    k <? n = true ->
    downshift (n :: l) k = (pred n) :: (downshift l k).
Proof with try reflexivity; try assumption.
  intros l k n Hlt.
  simpl.
      apply Nat.ltb_lt in Hlt.
  replace (n <? k) with false.
  2:{ symmetry.
      apply Nat.ltb_nlt.
      lia. }
  replace (n =? k) with false...
  symmetry.
  apply Nat.eqb_neq.
  lia.
Qed.
  
Lemma downshift_In_nat_bool_lt : forall l n k,
    n <? k = true ->
    In_nat_bool n (downshift l k) = In_nat_bool n l.
Proof with try reflexivity; try assumption.
  intros l; induction l; intros n k Hlt...
  destruct (Compare_dec.lt_eq_lt_dec a k) as [[H1 | H2] | H3].
  - apply Nat.ltb_lt in H1.
    simpl; rewrite H1.
    simpl; rewrite (IHl n k Hlt)...
  - subst.
    rewrite (downshift_eq l k).
    assert (k <> n).
    { apply Nat.ltb_lt in Hlt.
      lia. }
    rewrite (In_nat_bool_neq _ _ _ H).
    apply IHl...
  - apply Nat.ltb_lt in H3.
    rewrite (downshift_gt _ _ _ H3).
    destruct a.
    + exfalso.
      apply Nat.ltb_lt in H3.
      lia.
    + simpl.
      replace (n =? a) with false.
      2:{ symmetry.
          apply Nat.eqb_neq.
          apply Nat.ltb_lt in Hlt.
          apply Nat.ltb_lt in H3.
          lia. }
      replace (n =? S a) with false.
      2:{ symmetry.
          apply Nat.eqb_neq.
          apply Nat.ltb_lt in Hlt.
          apply Nat.ltb_lt in H3.
          lia. }
      apply IHl...      
Qed.
  
Lemma downshift_In_nat_bool_gt : forall l n k,
    k <? n = true ->
    In_nat_bool (pred n) (downshift l k) = In_nat_bool n l.
Proof with try reflexivity; try assumption.
  intros l; induction l; intros n k Hlt...
  destruct (Compare_dec.lt_eq_lt_dec a k) as [[H1 | H2] | H3].
  - apply Nat.ltb_lt in H1.
    simpl; rewrite H1.
    simpl; rewrite (IHl n k Hlt).
    apply Nat.ltb_lt in Hlt.
    apply Nat.ltb_lt in H1.
    replace (pred n =? a) with false.
    2:{ symmetry.
        apply Nat.eqb_neq.
        lia. }
    replace (n =? a) with false...
    symmetry.
    apply Nat.eqb_neq...
    lia.
  - subst.
    rewrite (downshift_eq l k).
    assert (k <> n).
    { apply Nat.ltb_lt in Hlt.
      lia. }
    rewrite (In_nat_bool_neq _ _ _ H).
    apply IHl...
  - apply Nat.ltb_lt in H3.
    apply Nat.ltb_lt in Hlt.
    rewrite (downshift_gt _ _ _ H3).
    apply Nat.ltb_lt in H3.
    destruct n; destruct a; try (exfalso; lia).
    simpl.
    apply Nat.ltb_lt in Hlt.
    rewrite<- (IHl (S n) k Hlt)...
Qed.

Lemma downshift_In_nat_bool_eq : forall l k,
    In_nat_bool k (downshift l k) = In_nat_bool (S k) l.
Proof with try reflexivity; try assumption.
  induction l; intro k...
  destruct (Compare_dec.lt_eq_lt_dec a k) as [[H1 | H2] | H3].
  - simpl.
    apply Nat.ltb_lt in H1.
    rewrite H1.
    change (match a with
            | 0 => false
            | S m' => k =? m'
            end) with (S k =? a).
    apply Nat.ltb_lt in H1.
    replace (S k =? a) with false.
    2:{ symmetry.
        apply Nat.eqb_neq.
        lia. }
    simpl.
    replace (k =? a) with false.
    2:{ symmetry.
        apply Nat.eqb_neq.
        lia. }
    refine (IHl k).
  - subst.
    rewrite downshift_eq.
    simpl.
    change ( match k with
              | 0 => false
              | S m' => k =? m'
             end) with (S k =? k).
    replace (S k =? k) with false.
    2:{ symmetry.
        apply Nat.eqb_neq.
        lia. }
    refine (IHl _).
  - simpl.
    change ( match a with
              | 0 => false
              | S m' => k =? m'
             end) with (S k =? a).
    replace (a <? k) with false.
    2:{ symmetry.
        apply Nat.ltb_nlt.
        lia. }
    replace (a =? k) with false.
    2:{ symmetry.
        apply Nat.eqb_neq.
        lia. }
    destruct a ; [exfalso; lia |].
    case_eq (k =? a); intro Heq.
    + apply Nat.eqb_eq in Heq.
      subst.
      simpl.
      replace (a =? a) with true...
      symmetry; apply Nat.eqb_eq...
    + simpl.
      rewrite Heq.
      refine (IHl k).
Qed.  

Lemma downshift_length : forall l n,
    In_nat_bool n l = false ->
    length (downshift l n) = length l.
Proof with try reflexivity; try assumption.
  intros l n nHin; induction l...
  simpl in nHin.
  apply orb_false_iff in nHin as (nHeq & nHin).
  rewrite Nat.eqb_sym in nHeq.
  simpl.
  case (a <? n); simpl; try rewrite (IHl nHin)...
  rewrite nHeq; simpl; rewrite IHl...
Qed.

Lemma nth_downshift_gt : forall l n k0 k,
    In_nat_bool n l = false ->
    k < length l ->
    n < nth k l k0 ->
    nth k (downshift l n) k0 = pred (nth k l k0).
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin Hlen Hgt.
  - inversion Hlen.
  - destruct k.
    + simpl.
      case_eq (a <? n); intros Hlt.
      * apply Nat.ltb_lt in Hlt.
        simpl in Hgt.
        exfalso.
        lia.
      * case_eq (a =? n); intros Heq...
        apply Nat.eqb_eq in Heq.
        simpl in Hgt.
        lia.
    + simpl.
      case_eq (a <? n); intros Hlt.
      * apply orb_false_elim in nHin as (_ & nHin).
        apply Lt.lt_S_n in Hlen.
        refine (IHl _ _ _ nHin Hlen Hgt).
      * case_eq (a =? n); intros Heq.
        -- simpl in nHin.
           replace (n =? a) with true in nHin; try now inversion nHin.
           symmetry.
           rewrite Nat.eqb_sym...
        -- apply orb_false_elim in nHin as (_ & nHin).
           apply Lt.lt_S_n in Hlen.
           refine (IHl _ _ _ nHin Hlen Hgt).
Qed.  

Lemma nth_downshift_lt : forall l n k0 k,
    In_nat_bool n l = false ->
    k < length l ->
    nth k l k0 < n ->
    nth k (downshift l n) k0 = (nth k l k0).
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin Hlen Hlt.
  - inversion Hlen.
  - destruct k.
    + simpl.
      case_eq (a <? n); intros Hlt'...
      case_eq (a =? n); intros Heq.
      * apply Nat.eqb_eq in Heq.
        simpl in Hlt.
        lia.
      * apply Nat.eqb_neq in Heq.
        apply Nat.ltb_nlt in Hlt'.
        simpl in Hlt.
        lia.
    + simpl.
      case_eq (a <? n); intros Hlt'.
      * apply orb_false_elim in nHin as (_ & nHin).
        apply Lt.lt_S_n in Hlen.
        refine (IHl _ _ _ nHin Hlen Hlt).
      * case_eq (a =? n); intros Heq.
        -- simpl in nHin.
           replace (n =? a) with true in nHin; try now inversion nHin.
           symmetry.
           rewrite Nat.eqb_sym...
        -- apply orb_false_elim in nHin as (_ & nHin).
           apply Lt.lt_S_n in Hlen.
           refine (IHl _ _ _ nHin Hlen Hlt).
Qed.

Lemma le_nth_downshift : forall l n k0 k,
    In_nat_bool n l = false ->
    nth k (downshift l n) k0 <= nth k l k0.
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin...
  destruct (orb_false_elim _ _ nHin) as (_ & nHin').
  simpl.
  case (a <? n) ; [ | case_eq (a =? n); intros Heq; [simpl in nHin; rewrite Nat.eqb_sym in Heq; rewrite Heq in nHin; inversion nHin | ]]; destruct k; try apply IHl...
  - apply Nat.le_pred_l.
Qed.

Lemma nth_ge_downshift : forall l n k0 k,
    In_nat_bool n l = false ->
    k < length l ->
    n <= nth k (downshift l n) k0 ->
    nth k (downshift l n) k0 = pred (nth k l k0).
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin Hlen Hgt.
  - inversion Hlen.
  - simpl in Hgt.
    simpl.
    destruct k.
    + case_eq (a <? n); intros Hlt; rewrite Hlt in Hgt.
      * apply Nat.ltb_lt in Hlt.
        simpl in Hgt.
        lia.
      * case_eq (a =? n); intros Heq; rewrite Heq in Hgt...
        unfold In_nat_bool in nHin.
        rewrite Nat.eqb_sym in Heq.
        rewrite Heq in nHin.
        inversion nHin.
    + case_eq (a <? n); intros Hlt; rewrite Hlt in Hgt.
      * apply orb_false_elim in nHin as (_ & nHin).
        apply Lt.lt_S_n in Hlen.
        refine (IHl _ _ _ nHin Hlen Hgt).
      * case_eq (a =? n); intros Heq; rewrite Heq in Hgt.
        -- simpl in nHin.
           rewrite Nat.eqb_sym in nHin.
           rewrite Heq in nHin.
           inversion nHin.
        -- apply orb_false_elim in nHin as (_ & nHin).
           apply Lt.lt_S_n in Hlen.
           refine (IHl _ _ _ nHin Hlen Hgt).
Qed.  

Lemma nth_lt_downshift : forall l n k0 k,
    In_nat_bool n l = false ->
    k < length l ->
    nth k (downshift l n) k0 < n ->
    nth k (downshift l n) k0 = (nth k l k0).
Proof with try reflexivity; try assumption.
  induction l; intros n k0 k nHin Hlen Hlt.
  - inversion Hlen.
  - simpl.
    simpl in Hlt.
    destruct k.
    + case_eq (a <? n); intros Hlt'; rewrite Hlt' in Hlt...
      case_eq (a =? n); intros Heq; rewrite Heq in Hlt.
      * simpl in nHin.
        rewrite Nat.eqb_sym in nHin.
        rewrite Heq in nHin.
        inversion nHin.
      * apply Nat.eqb_neq in Heq.
        apply Nat.ltb_nlt in Hlt'.
        simpl in Hlt.
        lia.
    + case_eq (a <? n); intros Hlt'; rewrite Hlt' in Hlt.
      * apply orb_false_elim in nHin as (_ & nHin).
        apply Lt.lt_S_n in Hlen.
        refine (IHl _ _ _ nHin Hlen Hlt).
      * case_eq (a =? n); intros Heq; rewrite Heq in Hlt.
        -- simpl in nHin.
           replace (n =? a) with true in nHin; try now inversion nHin.
           symmetry.
           rewrite Nat.eqb_sym...
        -- apply orb_false_elim in nHin as (_ & nHin).
           apply Lt.lt_S_n in Hlen.
           refine (IHl _ _ _ nHin Hlen Hlt).
Qed.

Lemma downshift_all_lt : forall l n k,
    k <=? n = true ->
    all_lt l (S n) = all_lt (downshift l k) n.
Proof with try reflexivity; try assumption.
  intros l n k Hleq; induction l...
  destruct (Compare_dec.lt_eq_lt_dec a k) as [[H1 | H2] | H3].
  - apply Nat.ltb_lt in H1.
    simpl; rewrite H1.
    simpl.
    apply Nat.ltb_lt in H1.
    apply Nat.leb_le in Hleq.
    replace (a <? S n) with true.
    2:{ symmetry.
        apply Nat.ltb_lt.
        lia. }
    replace (a <? n) with true...
    symmetry.
    apply Nat.ltb_lt.
    lia.
  - subst.
    rewrite downshift_eq.
    simpl.
    rewrite IHl.
    replace (k <? S n) with true...
  - apply Nat.ltb_lt in H3.
    rewrite downshift_gt...
    destruct a; simpl.
    + apply Nat.ltb_lt in H3; lia.
    + change (S a <? S n) with (a <? n).
      rewrite IHl...
Qed.

Lemma downshift_keep_all_distinct : forall l k,
    all_distinct l = true ->
    all_distinct (downshift l k) = true.
Proof with try reflexivity; try assumption.
  induction l; intros k Hal...
  destruct (Compare_dec.lt_eq_lt_dec a k) as [[H1 | H2] | H3].
  - apply Nat.ltb_lt in H1.
    simpl; rewrite H1.
    apply andb_prop in Hal as (nHin & Hal).
    splitb.
    + rewrite downshift_In_nat_bool_lt...
    + refine (IHl k Hal).
  - subst.
    rewrite downshift_eq.
    apply andb_prop in Hal as (nHin & Hal).
    refine (IHl k Hal).
  - apply andb_prop in Hal as (nHin & Hal).
    specialize (IHl k Hal).
    clear Hal.
    rewrite downshift_gt.
    2:{ apply Nat.ltb_lt... }
    splitb...
    rewrite downshift_In_nat_bool_gt by (apply Nat.ltb_lt; apply H3)...
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

Lemma downshift_incr_all : forall l n,
    downshift (incr_all l (S n)) n = incr_all l n.
Proof with try reflexivity; try assumption.
  induction l...
  simpl.
  intro n.
  replace (S (n + a) <? n ) with false.
  2:{ symmetry.
      apply Nat.ltb_nlt.
      lia. }
  rewrite (IHl n).
  destruct n...
  replace (S n + a =? n) with false...
  symmetry.
  apply Nat.eqb_neq.
  lia.  
Qed.

Lemma downshift_app : forall l1 l2 n,
    downshift (l1 ++ l2) n = downshift l1 n ++ downshift l2 n.
Proof with try reflexivity; try assumption.
  induction l1; intros l2 n...
  simpl.
  rewrite (IHl1 l2 n).
  case (a <? n)...
  case (a =? n)...
Qed.

Lemma downshift_if_all_lt : forall l n,
    all_lt l n = true ->
    downshift l n = l.
Proof with try reflexivity; try assumption.
  induction l; intros n Hal...
  apply andb_prop in Hal as (Hlt & Hal).
  simpl.
  rewrite Hlt.
  rewrite IHl...
Qed.

Lemma downshift_shift : forall l n,
    downshift (shift l n) n = l.
Proof with try reflexivity; try assumption.
  induction l; intros n...
  simpl.
  case_eq (a <? n); intros Hlt.
  - simpl.
    rewrite Hlt.
    rewrite IHl...
  - simpl.
    apply Nat.ltb_nlt in Hlt.
    replace (S a <? n) with false by (symmetry; apply Nat.ltb_nlt; lia).
    change (match n with
            | 0 => false
            | S m' => a =? m'
            end) with (S a =? n).
    case_eq (S a =? n); intros Heq; [ | rewrite IHl]...
    apply Nat.eqb_eq in Heq.
    lia.
Qed.

Lemma shift_downshift : forall l n,
    In_nat_bool n l = false ->
    shift (downshift l n) n = l.
Proof with try reflexivity; try assumption.
  induction l; intros n nHin...
  simpl in nHin; apply orb_false_iff in nHin as (nHeq & nHin).
  simpl.
  case_eq (a <? n); intros Hlt.
  - simpl; rewrite Hlt.
    rewrite IHl...
  - rewrite Nat.eqb_sym in nHeq.
    rewrite nHeq.
    destruct a; try now (destruct n; inversion nHeq).
    simpl.
    rewrite IHl...
    replace (a <? n) with false...
    symmetry.
    apply Nat.ltb_nlt.
    apply Nat.ltb_nlt in Hlt.
    apply Nat.eqb_neq in nHeq.
    lia.
Qed.

Lemma incr_all_downshift_0 : forall l,
    In_nat_bool 0 l = false ->
    incr_all (downshift l 0) 1 = l.
Proof with try reflexivity; try assumption.
  induction l; intros nHin...
  destruct a.
  { inversion nHin. }
  rewrite downshift_gt...
  simpl.
  rewrite IHl...
Qed.

Lemma downshift_nth : forall l1 l2 a0 k1 k2,
    k1 < length l1 ->
    In_nat_bool k2 l1 = false ->
    downshift ((nth k1 l1 a0) :: l2) k2 = (nth k1 (downshift l1 k2) a0 :: (downshift l2 k2)).
Proof with try reflexivity; try assumption.
  induction l1; intros l2 a0 k1 k2 Hlen nHin; try now inversion Hlen.
  destruct k1.
  - change (nth 0 (a :: l1) a0) with a.
    case_eq (a <? k2); intros Hlt.
    + simpl.
      rewrite Hlt...
    + assert (k2 <? a = true) as Hgt.
      { apply Nat.ltb_lt.
        apply Nat.ltb_nlt in Hlt.
        apply orb_false_iff in nHin as (nHeq & _).
        apply Nat.eqb_neq in nHeq.
        lia. }
      rewrite 2 downshift_gt...
  - change (nth (S k1) (a :: l1) a0) with (nth k1 l1 a0).
    replace (nth (S k1) (downshift (a :: l1) k2) a0) with (nth k1 (downshift l1 k2) a0).
    { simpl in Hlen.
      apply Lt.lt_S_n in Hlen.
      apply orb_false_iff in nHin as (_ & nHin).
      apply IHl1... }
    case_eq (a <? k2); intros Hlt.
    + simpl.
      rewrite Hlt...
    + assert (k2 <? a = true) as Hgt.
      { apply Nat.ltb_lt.
        apply Nat.ltb_nlt in Hlt.
        apply orb_false_iff in nHin as (nHeq & _).
        apply Nat.eqb_neq in nHeq.
        lia. }
      rewrite downshift_gt...
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

(** ** Basic manipulation *)

Lemma map_incr_all {A} : forall (f : nat -> A) l k,
    map f (incr_all l k) = map (fun x => f (k + x)) l.
Proof with try reflexivity; try assumption.
  intros f.
  induction l; intros k...
  simpl.
  rewrite IHl...
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
  splitb.
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

(** ** append function *)
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

Lemma append_fun_all_lt : forall l1 l2 n1 n2,
    all_lt l1 n1 = true ->
    all_lt l2 n2 = true ->
    all_lt (l1 ++ (incr_all l2 n1)) (n1 + n2) = true.
Proof with try reflexivity; try assumption.
  intros l1 l2 n1 n2 Hal1 Hal2.
  rewrite all_lt_app.
  apply andb_true_iff.
  split.
  - apply all_lt_leq with n1...
    lia...
  - rewrite<- all_lt_incr_all...
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

Lemma nth_incr_all : forall l n n0 k,
    nth k (incr_all l n) (n + n0) = n + (nth k l n0).
Proof with try reflexivity.
  induction l; destruct k...
  simpl.
  apply IHl.
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

Lemma incr_all_inj : forall l1 l2 n,
    incr_all l1 n = incr_all l2 n ->
    l1 = l2.
Proof with try reflexivity.
  induction l1; intros l2 n Heq.
  - destruct l2; try now inversion Heq...
  - destruct l2; try now inversion Heq.
    simpl in Heq.
    inversion Heq.
    apply Plus.plus_reg_l in H0.
    apply IHl1 in H1.
    subst...
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

Lemma all_distinct_map : forall f p,
    all_distinct p = true ->
    injective f ->
    all_distinct (map f p) = true.
Proof with try assumption; try reflexivity.
  intros f p Had inj.
  revert Had; induction p; intros Had...
  apply andb_prop in Had as (nHin & Had).
  simpl.
  splitb; [ | apply IHp]...
  apply negb_true_iff.
  apply cond_negb_In_nat_bool.
  intros k k0 Hlen.
  intros Heq.
  rewrite (nth_indep _ _ (f 0)) in Heq...
  rewrite map_nth in Heq.
  apply negb_true_iff in nHin.
  apply neg_nth_eq with _ _ 0 k in nHin; [ | rewrite map_length in Hlen]...
  apply nHin.
  apply inj...
Qed.
                                
Lemma all_lt_max : forall f k a, fold_left max f a < k -> all_lt f k = true.
Proof with try assumption; try reflexivity.
  intro f.
  induction f; intros k b Hlt...
  simpl.
  splitb.
  - apply Nat.ltb_lt.
    apply Nat.le_lt_trans with (fold_left max (a :: f) b)...
    simpl.
    transitivity (max b a).
    + apply Nat.le_max_r.
    + apply fold_left_max_r.
  - apply IHf with (max b a)...
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
    
Lemma transpo_max : forall m n k, fold_left max (transpo m n) k = max m k.
Proof with try reflexivity; try assumption.
  intros m n k.
  unfold transpo.
  case_eq (n <? m); intros Hcase.
  - rewrite fold_left_max_app.
    change (fold_left max (S n :: n :: incr_all (Id (S m - (2 + n))) (2 + n)) k) with (fold_left max (incr_all (Id (S m - (2 + n))) (2 + n)) (max (max k (S n)) n)).
    apply Nat.ltb_lt in Hcase.
    remember (S m - (2 + n)); destruct n; destruct n0.
    + simpl; lia.
    + rewrite incr_all_max ; [ | intros H; inversion H]; rewrite Id_max; simpl.
      simpl in Heqn0.
      rewrite Nat.max_comm.
      lia.
    + rewrite Id_max.
      simpl.
      lia.
    + rewrite incr_all_max ; [ | intros H; inversion H]; rewrite 2 Id_max; simpl.
      lia.
  - apply Id_max.
Qed.

Lemma all_lt_transpo : forall m n, all_lt (transpo m n) (S m) = true.
Proof with try reflexivity; try assumption.
  intros m n.
  unfold transpo.
  case_eq (n <? m); intros Hcase.
  - apply Nat.ltb_lt in Hcase.
    rewrite all_lt_app.
    splitb.
    + apply all_lt_leq with n; [ | lia].
      apply all_lt_Id.
    + simpl.
      splitb; [ | splitb].
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
    + simpl; splitb; [ | splitb].
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

Lemma app_compo_transpo : forall m l1 l2, compo_transpo m (l1 ++ l2) = app_nat_fun (compo_transpo m l1) (compo_transpo m l2).
Proof with try reflexivity.
  intros m; induction l1; intros l2.
  - simpl.
    change (0 :: incr_all (Id m) 1) with (Id (S m)).
    replace (S m) with (length (compo_transpo m l2)) by apply compo_transpo_length.
    rewrite app_Id...
  - simpl.
    rewrite asso_app_nat_fun.
    rewrite<- IHl1...
Qed.

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
  - rewrite incr_all_length; rewrite Id_length...
  - rewrite incr_all_length; rewrite Id_length...
Qed.

Lemma all_lt_nc_transpo : forall m i j,
    all_lt (nc_transpo m i j) (S m) = true.
Proof with try reflexivity; try assumption.
  intros m i j.
  unfold nc_transpo.
  case_eq (i <? j); intros Hcase1; [case_eq (j <=? m); intros Hcase2 | ]; unfold "&&".
  - apply Nat.ltb_lt in Hcase1; apply Nat.leb_le in Hcase2.
    rewrite all_lt_app.
    splitb.
    + apply all_lt_leq with i; [apply all_lt_Id | lia].
    + simpl.
      splitb; [apply Nat.ltb_lt; lia | ].
      rewrite all_lt_app.
      splitb.
      * rewrite (Minus.le_plus_minus (S i) (S m)); [ | lia].
        rewrite<- all_lt_incr_all.
        apply all_lt_leq with (j - S i); [apply all_lt_Id | lia].
      * simpl.
        splitb; [ apply Nat.ltb_lt; lia | ].
        rewrite (Minus.le_plus_minus (S j) (S m)); [ | lia].
        rewrite<- all_lt_incr_all.
        simpl.
        apply all_lt_Id.
  - apply all_lt_Id.
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
    rewrite incr_all_length; rewrite Id_length...
  - destruct a; simpl.
    rewrite app_nat_fun_length.
    + apply nc_transpo_length.
    + intros H; rewrite H in IHl; inversion IHl.
Qed.

Lemma nc_transpo_decrease :
  forall m i j, i <> j -> i < S j -> S j <= m -> nc_transpo m i (S j) = app_nat_fun (app_nat_fun (transpo m j) (nc_transpo m i j)) (transpo m j).
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
      - replace (Id i ++ j :: incr_all (Id (j - S i)) (S i) ++ i :: incr_all (Id (m - j)) (S j)) with
            ((Id i ++ j :: incr_all (Id (j - S i)) (S i)) ++ i :: incr_all (Id (m - j)) (S j)) by (rewrite<- ? app_assoc; reflexivity).
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
      apply Nat.lt_le_trans with (S i)...
      destruct i; [simpl; lia | ].
      rewrite Id_max.
      lia. }
  change (S j :: j :: incr_all (Id (m - S j)) (S (S j))) with ((S j :: nil) ++ (j :: nil) ++ (incr_all (Id (m - S j)) (S (S j)))).
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
        with
          (incr_all ((S j - length (Id i ++ j :: incr_all (Id (j - S i)) (S i))) :: nil) (length (Id i ++ j :: incr_all (Id (j - S i)) (S i)))).
      replace (Id i ++
                  j :: incr_all (Id (j - S i)) (S i) ++ i :: incr_all (Id (m - j)) (S j))
        with ((Id i ++
                  j :: incr_all (Id (j - S i)) (S i)) ++ i :: incr_all (Id (m - j)) (S j)) by (rewrite <- ? app_assoc; reflexivity).
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
                       (Id j ++ (S j :: nil) ++ (j :: nil) ++ incr_all (Id (m - S j)) (S (S j)))) with (j :: nil).
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
      replace (Id i ++
                  j :: incr_all (Id (j - S i)) (S i) ++ i :: incr_all (Id (m - j)) (S j)) with  ((Id i ++
                                                                                                     j :: incr_all (Id (j - S i)) (S i)) ++ i :: incr_all (Id (m - j)) (S j)) by (rewrite <- ? app_assoc; reflexivity).
      rewrite app_nat_fun_right... }
  replace (app_nat_fun (i :: nil)
                       (Id j ++ (S j :: nil) ++ (j :: nil) ++ incr_all (Id (m - S j)) (S (S j)))) with (i :: nil).
  2:{ rewrite app_nat_fun_left.
      - rewrite app_nat_fun_Id_r...
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
          rewrite Nat.add_0_r.
          rewrite<- incr_all_plus... }
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
                       (Id j ++ (S j :: nil) ++ (j :: nil) ++ incr_all (Id (m - S j)) (S (S j)))) with (incr_all (Id (m - S j)) (S (S j))).
  2:{ replace (Id j ++ (S j :: nil) ++ (j :: nil) ++ incr_all (Id (m - S j)) (S (S j)))
        with
          ((Id j ++ (S j :: j :: nil)) ++ incr_all (Id (m - S j)) (S (S j))) by (rewrite<- ? app_assoc; reflexivity).
      replace (S (S j)) with (length (Id j ++ S j :: j :: nil)) at 2.
      2:{ rewrite app_length; rewrite Id_length; simpl; lia. }
      rewrite app_nat_fun_right.
      2:{ rewrite incr_all_length; rewrite Id_length.
          apply all_lt_Id. }
      replace (m - S j) with (length (incr_all (Id (m - S j)) (S (S j)))) at 2.
      - rewrite app_Id...
      - rewrite incr_all_length; rewrite Id_length... }
  change (S j :: incr_all (Id (j - i)) (S i) ++ i :: incr_all (Id (m - S j)) (S (S j))) with ((S j :: incr_all (Id (j - i)) (S i)) ++ i :: incr_all (Id (m - S j)) (S (S j))).
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
  replace (incr_all (Id (j - i)) (S i)) with (app_nat_fun (incr_all (Id (j - S i)) (S i))
                                                          (Id j ++ S j :: j :: incr_all (Id (m - S j)) (S (S j))) ++ 
                                                          j :: nil)...
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
    2:{ rewrite incr_all_max; [ | intro H; inversion H].
        rewrite Id_max.
        simpl; lia. }
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
            replace (match i with | 0 => S i | S m' => S (max i m') end) with (S i).
            2:{ change (match i with | 0 => S i | S m' => S (max i m') end) with (max (S i) i).
                lia. }
            remember (m - S i).
            destruct n.
            - simpl.
              destruct i.
              + simpl.
                lia.
              + rewrite Id_max.
                lia.
            - rewrite incr_all_max.
              2:{ simpl.
                  intros H; inversion H. }
              destruct i; rewrite ? Id_max; simpl; lia. }
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
               rewrite transpo_max.
               lia. }
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
  change (j :: incr_all (Id (j - S i)) (S i) ++ i :: incr_all (Id (n - j)) (S j)) with ((j :: incr_all (Id (j - S i)) (S i)) ++ i :: incr_all (Id (n - j)) (S j)).
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
      replace (l0 ++ a :: l1 ++ b :: l2) with ((l0 ++ a :: l1) ++ b :: l2) by (rewrite<- ? app_assoc; reflexivity).
      rewrite app_nat_fun_right... }
  replace ( app_nat_fun (incr_all (Id (j - S i)) (S i)) (l0 ++ a :: l1 ++ b :: l2)) with l1.
  2:{ rewrite Hleni at 2.
      replace (l0 ++ a :: l1 ++ b :: l2) with ((l0 ++ a :: nil) ++ l1 ++ b :: l2) by (rewrite<- ? app_assoc; reflexivity).
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
  replace (l0 ++ a :: l1 ++ b :: l2) with ((l0 ++ a :: l1 ++ b :: nil) ++ l2) by (repeat (rewrite<- app_assoc; simpl); reflexivity).
  replace (n - j) with (length l2).
  2:{ rewrite app_length in Hlenj.
      repeat (rewrite app_length in Hlenn; simpl in Hlenn).
      simpl in Hlenj.
      lia. }
  rewrite app_nat_fun_right.
  - rewrite app_Id...
  - apply all_lt_Id.
Qed.