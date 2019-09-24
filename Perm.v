Require Import Lia.
Require Import PeanoNat.

Require Import Bool_more.
Require Import List_Type_more.
Require Import List_more2.
Require Import List_nat.
Require Import Fun_nat.
Require Import Transposition.
Require Import misc.

(* PERMUTATION DEFINITION *)

Definition is_perm (l : list nat) :=
  (all_lt l (length l)) && (all_distinct l).

(* Some facts about is_perm *)

Lemma tail_perm : forall l k,
  is_perm (k :: l) = true ->
  is_perm (downshift l k) = true.
Proof with try assumption.
intros l k Hp.
apply andb_true_iff in Hp as [Hp1 Hp2].
simpl in Hp1; apply andb_true_iff in Hp1 as [Hp1 Hp3].
apply Nat.ltb_lt in Hp1.
simpl in Hp2; apply andb_true_iff in Hp2 as [Hp2 Hp4].
apply negb_true_iff in Hp2.
apply andb_true_iff; split.
- rewrite downshift_length...
  rewrite <- downshift_all_lt by (apply Nat.leb_le; lia)...
- apply downshift_keep_all_distinct; assumption.
Qed.

Lemma perm_surj : forall p k0 k,
  is_perm p = true -> k < length p ->
  {i & prod (i < length p) (nth i p k0 = k)}.
Proof.
intro p; remember (length p); revert p Heqn.
induction n; intros p Heq k0 k Hperm Hlt.
- exfalso; lia.
- destruct p; inversion Heq; subst.
  assert (Hperm' := Hperm).
  apply andb_true_iff in Hperm' as [Hperm1 Hperm2]; simpl in Hperm2.
  apply andb_true_iff in Hperm2 as [Hperm2 _]; simpl in Hperm2.
  assert (In_nat_bool n0 p = false) as Hn0 by (apply (proj1 (negb_true_iff _) Hperm2)).
  apply tail_perm in Hperm.
  case_eq (n0 =? k); intros Heqk;
    [ | case_eq (n0 <? k); intros Hlt2; [ apply Nat.ltb_lt in Hlt2 | ] ].
  + apply Nat.eqb_eq in Heqk; subst.
    exists 0; split; [ lia | reflexivity ].
  + apply IHn with _ k0 (pred k) in Hperm; [ | | lia ].
    * destruct Hperm as [i [Hnth1 Hnth2]].
      exists (S i); split; [ lia | simpl ].
      rewrite nth_ge_downshift in Hnth2; [ | assumption | assumption | lia ].
      assert (In_nat_bool (nth i p k0) p = true)
        by (apply cond_In_nat_bool; now exists (k0,i)).
      destruct (nth i p k0); try lia.
      destruct k; [ reflexivity | exfalso ].
      simpl in Hnth2; subst.
      destruct n0; try lia.
      rewrite Hn0 in H; inversion H.
    * now rewrite downshift_length.
  + assert (k < n0) as Hlt3
      by (apply Nat.ltb_ge in Hlt2; apply Nat.eqb_neq in Heqk; lia).
    apply IHn with _ k0 k in Hperm.
    * destruct Hperm as [i [Hnth1 Hnth2]].
      exists (S i); split; [ lia | simpl ].
      now rewrite nth_lt_downshift in Hnth2; try lia. 
    * now rewrite downshift_length.
    * apply andb_true_iff in Hperm1 as [Hperm1 _]; simpl in Hperm1.
      apply Nat.ltb_lt in Hperm1; lia.
Qed.

Lemma decomp_perm : forall l k,
    k < length l ->
    is_perm l = true ->
    {' (la , lb) : _ & l = la ++ k :: lb & (prod (In_nat_bool k la = false) (In_nat_bool k lb = false))}.
Proof with try reflexivity; try assumption.
  intros l k Hlen Hperm.
  destruct (perm_surj l 0 k Hperm Hlen) as (i & Hleni & Heq).
  destruct (nth_split_Type i l 0 Hleni) as [(la,lb) Heql Heq_len].
  split with (la , lb); [ | split].
  - rewrite<- Heq...
  - apply andb_prop in Hperm as (_ & Had).
    rewrite Heql in Had.
    rewrite Heq in Had.
    apply all_distinct_left with lb...
  - apply andb_prop in Hperm as (_ & Had).
    rewrite Heql in Had.
    rewrite Heq in Had.
    apply all_distinct_right with la...
Qed.

Lemma downshift_perm_length : forall l k,
    k < length l -> 
    is_perm l = true ->
    length (downshift l k) = pred (length l).
Proof with try reflexivity; try assumption.
  intros l k Hlen Hperm.
  destruct (decomp_perm l k Hlen Hperm) as [(la & lb) Heq (nHinla & nHinlb)].
  rewrite Heq.
  rewrite downshift_app.
  rewrite 2 app_length.
  rewrite downshift_eq.
  simpl.
  rewrite Nat.add_succ_r.
  rewrite 2 downshift_length...
Qed.

Lemma downshift_perm : forall l k,
    is_perm l = true ->
    is_perm (downshift l k) = true.
Proof with try reflexivity; try assumption.
  intros l k Hperm.
  case_eq (k <? length l); intros Hlt.
  - apply Nat.ltb_lt in Hlt.
    unfold is_perm in *.
    destruct (andb_prop _ _ Hperm) as (Halt & Had).
    replace (all_distinct (downshift l k)) with true
      by (symmetry; apply downshift_keep_all_distinct; assumption).
    rewrite andb_true_r.
    rewrite downshift_perm_length...
    destruct l; try now inversion Hlt.
    simpl length in Halt.
    simpl length; simpl pred.
    rewrite downshift_all_lt with _ _ k in Halt...
    simpl in Hlt.
    apply Nat.leb_le; lia.
  - rewrite downshift_if_all_lt...
    apply Nat.ltb_nlt in Hlt.
    apply andb_prop in Hperm as (Hal & _).
    apply all_lt_leq with (length l); [ assumption | lia ].
Qed.

Lemma app_perm_keep_all_distinct : forall (l : list nat) p,
    length p = length l ->
    is_perm p = true ->
    all_distinct l = all_distinct (app_nat_fun p l).
Proof with try reflexivity; try assumption.
  destruct l...
  unfold app_nat_fun.
  intros p Hlen H1.
  assert (Hperm := H1).
  unfold is_perm in H1.
  simpl.
  simpl in Hlen.
  change (negb (In_nat_bool n l) && all_distinct l) with (all_distinct (n :: l)).
  apply andb_prop in H1 as (H1 & H2).
  case_eq (all_distinct (n :: l)); intros Hal; symmetry.
  - apply cond_all_distinct.
    intros n1 n2 k Hlt1 Hlt2 Heq.
    assert (H := cond_all_distinct_inv (n :: l)).
    specialize (H Hal) as H.
    clear Hal.
    assert (H0 := cond_all_distinct_inv p).
    specialize (H0 H2).
    unfold app_nat_fun_dflt in Hlt1, Hlt2; rewrite map_length in Hlt1 , Hlt2.
    apply H0 with n...
    apply H with n; try (simpl; rewrite<- Hlen)...
    + apply cond_all_lt_inv...
    + apply cond_all_lt_inv...
    + rewrite 2 nth_nth...
      rewrite 2 nth_indep with _ _ _ n k by (rewrite map_length; assumption)...
  - apply cond_all_distinct_false_inv with _ n in Hal as ((k1 & k2) & (Hlt1 & (Hlt2 & (nHeq & Heq)))).
    simpl in Hlt1 , Hlt2.
    rewrite<- Hlen in Hlt1, Hlt2.
    destruct (perm_surj _ n k1 Hperm Hlt1) as (i1 & (Hlti1 & Heqk1)).
    destruct (perm_surj _ n k2 Hperm Hlt2) as (i2 & (Hlti2 & Heqk2)).
    apply cond_all_distinct_false with n i1 i2.
    + unfold app_nat_fun_dflt; rewrite map_length...
    + unfold app_nat_fun_dflt; rewrite map_length...
    + intro H.
      apply nHeq.
      assert (H0 := cond_all_distinct_inv p).
      apply H0 with n...
      rewrite<- Heqk1.
      rewrite<- Heqk2.
      rewrite H...
    + unfold app_nat_fun_dflt; rewrite<- nth_nth with _ _ _ n _...
      rewrite<- nth_nth with _ _ _ n _ ...
      rewrite Heqk1.
      rewrite Heqk2...
Qed.

Lemma app_perm_keep_all_lt : forall (l : list nat) n p,
    length p = length l ->
    is_perm p = true ->
    all_lt l n = all_lt (app_nat_fun p l) n.
Proof with try reflexivity; try assumption.
  intros l n p Hlen Hperm.
  simpl in Hlen.
  case_eq (all_lt l n); intros Heq; symmetry.
  - destruct l...
    apply cond_all_lt.
    intros k0 k Hlt.
    unfold app_nat_fun.
    simpl.
    simpl in Hlt.
    unfold app_nat_fun_dflt in Hlt; rewrite map_length in Hlt.
    replace (nth k (map (fun x : nat => nth x (n0 :: l) n0) p) k0)
       with (nth k (map (fun x : nat => nth x (n0 :: l) n0) p) n0).
    2:{ apply nth_indep.
        rewrite map_length... }
    unfold app_nat_fun_dflt.
    rewrite nth_indep with _ _ _ _ n0; [ | rewrite map_length ]...
    rewrite<- nth_nth with _ _ _ n0 _...
    apply cond_all_lt_inv...
    apply cond_all_lt_inv...
    apply andb_prop in Hperm as (H & _)...
    rewrite<- Hlen...
  - destruct l; try now inversion Heq...
    simpl.
    change (fun x : nat => match x with
                              | 0 => n0
                              | S n1 => nth n1 l n0
                           end) with (fun x => nth x (n0 :: l) n0).
    destruct (cond_all_lt_false_inv _ _ Heq n0) as (k & (Hlen' & Hge)).
    rewrite<- Hlen in Hlen'.
    destruct (perm_surj _ n0 k Hperm Hlen') as (i & (Hlen'' & Heqi)).
    apply cond_all_lt_false with i n0.
    + unfold app_nat_fun_dflt; rewrite map_length...
    + unfold app_nat_fun_dflt; rewrite<- nth_nth with _ _ _ n0 _...
      rewrite Heqi...
Qed.

Lemma compo_perm_is_perm : forall l1 l2,
    is_perm l1 = true ->
    is_perm l2 = true ->
    length l1 = length l2 ->
    is_perm (app_nat_fun l1 l2) = true.
Proof with try reflexivity; try assumption.
  intros l1 l2 Hp1 Hp2 Hlen.
  splitb.
  - rewrite<- app_perm_keep_all_lt...
    simpl.
    apply andb_prop in Hp2 as (Hp2 & _).
    destruct l2...
    unfold app_nat_fun.
    unfold app_nat_fun_dflt; rewrite map_length.
    rewrite Hlen...
  - apply andb_prop in Hp2 as (Halt2 & Had2).
    rewrite<- app_perm_keep_all_distinct...
Qed.

Lemma Id_is_perm : forall n, is_perm (Id n) = true.
Proof.
  intros n.
  splitb.
  - rewrite seq_length.
    apply all_lt_seq; lia.
  - apply all_distinct_seq.
Qed.

Lemma cfun_is_perm : forall n m,
    is_perm (cfun n m) = true.
Proof with try reflexivity; try assumption.
  intros n m.
  unfold is_perm.
  unfold cfun.
  apply andb_true_iff.
  split.
  - rewrite app_length.
    rewrite 2 seq_length.
    replace (m + n) with (n + m) by lia.
    apply all_lt_cfun.
  - apply all_distinct_cfun.
Qed.

Lemma append_perm_is_perm : forall f1 f2,
    is_perm f1 = true ->
    is_perm f2 = true ->
    is_perm (f1 ++ (incr_all f2 (length f1))) = true.
Proof with try reflexivity; try assumption.
  intros f1 f2 Hp1 Hp2.
  apply andb_prop in Hp1 as (Hal1 & Had1).
  apply andb_prop in Hp2 as (Hal2 & Had2).
  splitb.
  - rewrite app_length.
    rewrite incr_all_length.
    apply append_fun_all_lt...
  - remember (length f1) as n.
    clear Heqn Hal2.
    revert n Hal1.
    induction f1; intros n Hal.
    + simpl; rewrite all_distinct_incr_all...
    + simpl in Had1, Hal |- *.
      splitb.
      * apply negb_true_iff.
        rewrite In_nat_bool_app.
        apply orb_false_iff.
        split.
        -- apply andb_prop in Had1 as (nHin & _).
           apply negb_true_iff in nHin...
        -- apply negb_In_incr_all.
           apply andb_prop in Hal as (Hlt & _).
           apply Nat.ltb_lt...
      * apply andb_prop in Hal as (_ & Hal).
        apply andb_prop in Had1 as (_ & Had1).
        apply IHf1...
Qed.

Lemma app_nat_fun_vs_cons {A} : forall l1 l2 (a : A) n p
                                       (Hlen : length (n :: p) = length l2)
                                       (Hperm : is_perm (n :: p) = true)
                                       (Heq : a :: l1 = app_nat_fun (n :: p) l2),
    {' (la , lb) : _ & l2 = la ++ a :: lb & length la = n }.
Proof with try reflexivity; try assumption.
  intros l1 l2 a n p Hlen Hperm Heq.
  destruct l2; try now inversion Heq.
  unfold app_nat_fun in Heq.
  inversion Heq.
  change (match n with
           | 0 => a0
           | S n => nth n l2 a0
           end) with (nth n (a0 :: l2) a0) in H0.
  change (match n with
           | 0 => a0
           | S n => nth n l2 a0
          end) with (nth n (a0 :: l2) a0).
  apply nth_split_Type.
  rewrite<- Hlen.
  apply andb_prop in Hperm as (Halt & _).
  apply andb_prop in Halt as (Hlt & _).
  apply Nat.ltb_lt in Hlt...
Qed.

Lemma perm_has_inv : forall p,
    is_perm p = true ->
    { p_inv & prod (app_nat_fun p_inv p = Id (length p))
             (prod (is_perm p_inv = true) (length p = length p_inv)) }.
Proof with try reflexivity; try assumption.
  intro p.
  remember (length p).
  revert p Heqn.
  induction n; intros p Heqn Hperm.
  { destruct p; try now inversion Heqn.
    split with nil.
    split; [ | split]... }
  assert (0 < length p) as H.
  { rewrite<- Heqn.
    lia. }
  destruct (perm_surj p 0 0 Hperm H) as (n0 & (Hlen & Heq)).
  assert (n = length (downshift p 0)).
  { destruct p; try now inversion H.
    simpl in Heqn.
    apply Nat.succ_inj in Heqn.
    rewrite Heqn.
    symmetry.
    apply downshift_perm_length... }
  specialize (IHn (downshift p 0) H0 (downshift_perm _ _ Hperm)) as (p_inv & (Heq' & (Hperm' & Heq_len))).
  apply andb_prop in Hperm' as (Hal & Had).
  split with (n0 :: (shift p_inv n0)).
  simpl.
  destruct p; try now inversion H.
  app_nat_fun_unfold p (shift p_inv n0) n1 n0.
  replace (nth n0 (n1 :: p) n1) with 0.
  2:{ symmetry.
      transitivity (nth n0 (n1 :: p) 0)...
      apply nth_indep... }
  split; [ | split].
  - replace (seq 1 n) with (app_nat_fun (shift p_inv n0) (n1 :: p)).
    { rewrite <- Heq.
      replace (nth n0 (n1 :: p) 0) with (nth n0 (n1 :: p) n1)...
      apply nth_indep... }
    replace (seq 1 n) with (map S (Id n)) by (apply seq_shift).
    rewrite <- Heq'.
    pattern 0 at 1.
    rewrite <- Heq.
    rewrite app_nat_fun_downshift_shift...
    + rewrite Heq.
      change (map S (downshift (app_nat_fun (shift p_inv n0) (n1 :: p)) 0))
        with (incr_all (downshift (app_nat_fun (shift p_inv n0) (n1 :: p)) 0)1).
      rewrite incr_all_downshift_0...
      rewrite <- Heq.
      apply In_nat_bool_shift_false...
      * rewrite<- downshift_perm_length with _ 0...
        rewrite<- H0.
        rewrite Heq_len...
      * apply andb_prop in Hperm as (_ & Had')...
    + apply andb_prop in Hperm as (_ & Had')...
    + rewrite<- downshift_perm_length with _ 0...
      rewrite<- H0.
      rewrite Heq_len...
  - unfold is_perm; simpl; splitb; splitb.
    + apply Nat.ltb_lt.
      rewrite shift_length.
      lia.
    + rewrite shift_length.
      rewrite<- shift_all_lt...
      apply Nat.leb_le.
      lia.
    + assert (forall l k,
                 In_nat_bool k (shift l k) = false) as not_In_nat_bool_shift.
      { clear.
        induction l; intros k...
        simpl.
        case_eq (a <? k); intros Hlt.
        - simpl.
          replace (k =? a) with false; [apply IHl | ].
          symmetry.
          apply Nat.eqb_neq.
          apply Nat.ltb_lt in Hlt.
          lia.
        - simpl.
          replace (k =? (S a)) with false; [apply IHl | ].
          symmetry.
          apply Nat.eqb_neq.
          apply Nat.ltb_nlt in Hlt.
          lia. }
      apply negb_true_iff.
      apply not_In_nat_bool_shift...
    + apply shift_keep_all_distinct...
  - rewrite shift_length.
    rewrite Heq_len...
Qed.

(* PERMUTATION BY BLOCK *)
Lemma concat_perm {A} : forall (p1 : list nat) (L1 L2 : list (list A)) lp,
    length p1 = length L1 ->
    length p1 = length lp ->
    length L1 = length L2 ->
    is_perm p1 = true ->
    (forall i,
        i < length p1 ->
        (is_perm (nth (nth i p1 0) lp nil) = true) *
        (length (nth (nth i p1 0) lp nil) = length (nth (nth i p1 0) L1 nil)) *
        (nth i L2 nil = app_nat_fun (nth (nth i p1 0) lp nil) (nth (nth i p1 0) L1 nil))) ->
    { p & prod (is_perm p = true) ((length p = length (concat L1)) * (app_nat_fun p (concat L1) = concat L2)) }.
Proof with try reflexivity; try assumption.
  intros p1 L1 L2.
  revert p1 L1.
  induction L2; intros p1 L1 lp Hlen1 Hlenp Hlen2 Hperm H.
  - split with nil.
    destruct L1; try now inversion Hlen2.
  - destruct p1 as [ | i p1]; try (destruct L1; inversion Hlen1; now inversion Hlen2).
    destruct (andb_prop _ _ Hperm) as (Hal & Had).
    simpl in Hal, Had.
    apply andb_prop in Hal as (Hlt & Hal); apply Nat.ltb_lt in Hlt.
    destruct (nth_split_Type i lp nil) as [(lpa,lpb) Heqlp Hlenlpa]; [length_lia | ]...
    destruct (nth_split_Type i L1 nil) as [(L1a,L1b) HeqL1 HlenL1a]; [length_lia | ]...
    specialize (IHL2 (downshift p1 i) (L1a ++ L1b) (lpa ++ lpb)).
    apply andb_prop in Had as (nHin & Had); apply negb_true_iff in nHin.
    destruct IHL2 as (p & (Hperm' & Hlen' & Heq')).
    + rewrite downshift_length...
      rewrite HeqL1 in Hlen1; length_lia.
    + rewrite downshift_length...
      rewrite Heqlp in Hlenp; length_lia.
    + rewrite HeqL1 in Hlen2; length_lia.
    + replace (downshift p1 i) with (downshift (i :: p1) i) by now rewrite downshift_eq.
      apply downshift_perm...
    + intros j Hltj.
      rewrite downshift_length in Hltj...
      case_eq (nth j p1 0 <? i); intros Hcase; [apply Nat.ltb_lt in Hcase | apply Nat.ltb_nlt in Hcase].
      * rewrite nth_downshift_lt...
        destruct (H (S j)) as ((Hpermj & Hlenj) & Heqj); [ length_lia | ].
        split; [ split |].
        -- rewrite Heqlp in Hpermj.
           rewrite app_nth1 by now rewrite Hlenlpa.
           rewrite<- (app_nth1 _ (nth i lp nil :: lpb)) by now rewrite Hlenlpa...
        -- rewrite Heqlp in Hlenj; rewrite HeqL1 in Hlenj.
           rewrite app_nth1 by now rewrite Hlenlpa.
           rewrite app_nth1 by now rewrite HlenL1a.
           rewrite<- (app_nth1 _ (nth i lp nil :: lpb)) by now rewrite Hlenlpa.
           rewrite<- (app_nth1 _ (nth i L1 nil :: L1b)) by now rewrite HlenL1a...
        -- change (nth j L2 nil) with (nth (S j) (a :: L2) nil).
           change (nth j p1 0) with (nth (S j) (i :: p1) 0).
           rewrite ? app_nth1; try lia.
           rewrite Heqj.
           rewrite Heqlp; rewrite HeqL1.
           rewrite 2 app_nth1...
           ++ rewrite HlenL1a...
           ++ rewrite Hlenlpa...
           ++ rewrite HlenL1a...
           ++ rewrite Hlenlpa...
      * assert (nth j p1 0 <> i) by now apply neg_nth_eq.
        rewrite nth_downshift_ge; try lia...
        destruct (H (S j)) as ((Hpermj & Hlenj) & Heqj); [ length_lia | ].
        split; [ split |].
        -- rewrite app_nth2 by (rewrite Hlenlpa ; lia).
           replace (nth (pred (nth j p1 0) - length lpa) lpb nil)
              with (nth (nth j p1 0 - length lpa) (nth i lp nil :: lpb) nil).
           2:{ replace (nth j p1 0 - length lpa) with (S (pred (nth j p1 0) - length lpa)) by lia... }
           rewrite<- (app_nth2 lpa); [| rewrite Hlenlpa; length_lia].
           change (nth j p1 0) with (nth (S j) (i :: p1) 0).
           rewrite Heqlp in Hpermj...
        -- rewrite Heqlp in Hlenj; rewrite HeqL1 in Hlenj.
           rewrite app_nth2; [ | rewrite Hlenlpa; length_lia].
           replace (nth (pred (nth j p1 0) - length lpa) lpb nil)
              with (nth (nth j p1 0 - length lpa) (nth i lp nil :: lpb) nil).
           2:{ replace (nth j p1 0 - length lpa) with (S (pred (nth j p1 0) - length lpa)) by lia... }
           rewrite app_nth2; [ | rewrite HlenL1a; length_lia].
           replace (nth (pred (nth j p1 0) - length L1a) L1b nil)
              with (nth (nth j p1 0 - length L1a) (nth i L1 nil :: L1b) nil).
           2:{ replace (nth j p1 0 - length L1a) with (S (pred (nth j p1 0) - length L1a)) by lia... }
           rewrite<- (app_nth2 lpa); [ | rewrite Hlenlpa; length_lia].
           rewrite<- (app_nth2 L1a); [ | rewrite HlenL1a; length_lia].
           change (nth j p1 0) with (nth (S j) (i :: p1) 0)...
        -- change (nth j L2 nil) with (nth (S j) (a :: L2) nil).
           rewrite 2 app_nth2 ; [ | lia | lia ].
           replace (nth (pred (nth j p1 0) - length lpa) lpb nil)
              with (nth (nth j p1 0 - length lpa) (nth i lp nil :: lpb) nil).
           2:{ replace (nth j p1 0 - length lpa) with (S (pred (nth j p1 0) - length lpa)) by lia... }
           replace (nth (pred (nth j p1 0) - length L1a) L1b nil)
              with (nth (nth j p1 0 - length L1a) (nth i L1 nil :: L1b) nil).
           2:{ replace (nth j p1 0 - length L1a) with (S (pred (nth j p1 0) - length L1a)) by lia... }
           rewrite<- app_nth2 by lia.
           rewrite<- app_nth2 by lia.
           rewrite HeqL1 in Heqj; rewrite Heqlp in Heqj...
    + split with (incr_all (nth i lp nil) (length (concat L1a))
                     ++ map (fun k => if k <? length (concat L1a)
                                      then k else k + length (nth i lp nil)) p); split ; [splitb | split].
      * rewrite all_lt_app.
        splitb.
        -- apply all_lt_leq with (length (incr_all (nth i lp nil) (length (concat L1a))) + length (concat L1a)).
           ++ rewrite incr_all_length.
              rewrite Nat.add_comm.
              rewrite<- all_lt_incr_all.
              destruct (H 0) as ((Hpermi & _) & _); [length_lia | ]...
              apply andb_prop in Hpermi as (Hali & _).
              change i with (nth 0 (i :: p1) 0)...
           ++ rewrite app_length.
              rewrite map_length.
              rewrite Hlen'.
              rewrite concat_app; length_lia.
        -- rewrite app_length; rewrite map_length.
           rewrite incr_all_length.
           apply andb_prop in Hperm'; destruct Hperm' as (Hal' & _).
           remember (length p).
           clear - Hal'.
           rewrite Nat.add_comm.
           induction p...
           simpl in Hal'; apply andb_prop in Hal' as (Hlt' & Hal').
           simpl; splitb.
           ** apply Nat.ltb_lt in Hlt'.
              case (a <? length (concat L1a)); apply Nat.ltb_lt; lia.
           ** apply IHp...
      * destruct (H 0) as ((Hpermi & _) & _); [length_lia | ].
        apply andb_prop in Hpermi as (Hali & Hadi).
        apply andb_prop in Hperm' as (Hal' & Had').
        simpl in Hali, Hadi.
        remember (nth i lp nil).
        remember (length (concat L1a)).
        remember (length p).
        remember (length l).
        assert (length l <= n1) as Hlenn1 by lia.
        clear - Hal' Had' Hlenn1 Hadi Hali.
        induction l.
        -- simpl.
           rewrite all_distinct_map...
           intros x y.
           case_eq (x <? n); case_eq (y <? n); intros H1 H2 H3...
           ++ apply Nat.ltb_nlt in H1; apply Nat.ltb_lt in H2; lia.
           ++ apply Nat.ltb_lt in H1; apply Nat.ltb_nlt in H2; lia.
           ++ apply Nat.ltb_nlt in H1; apply Nat.ltb_nlt in H2; lia.
        -- simpl; splitb.
           ++ apply negb_true_iff.
              rewrite In_nat_bool_app.
              apply orb_false_intro.
              ** rewrite<- In_nat_bool_incr_all.
                 apply andb_prop in Hadi as (nHin & _).
                 apply negb_true_iff...
              ** apply andb_prop in Hali as (Hlt & _).
                 apply Nat.ltb_lt in Hlt.
                 clear - Hlt.
                 induction p...
                 simpl.
                 apply orb_false_intro...
                 case_eq (a0 <? n); intro Hcase ; [ apply Nat.ltb_lt in Hcase | apply Nat.ltb_nlt in Hcase];
                   apply Nat.eqb_neq; lia.
           ++ apply andb_prop in Hali as (_ & Hali); apply andb_prop in Hadi as (_ & Hadi).
              apply IHl...
              length_lia.
      * rewrite ? app_length.
        rewrite incr_all_length.
        rewrite map_length.
        rewrite Hlen'.
        rewrite HeqL1.
        rewrite 2 concat_app.
        rewrite 2 app_length.
        simpl; rewrite app_length.
        destruct (H 0) as ((_ & Hleni) & _); [ length_lia | ].
        change (nth 0 (i :: p1) 0) with i in Hleni.
        rewrite Hleni.
        lia.
      * destruct (H 0) as ((Hpermi & Hleni) & Heqi'); [ length_lia | ].
        change (nth 0 (i :: p1) 0) with i in Hpermi, Hleni, Heqi'.
        apply andb_prop in Hpermi as (Hali & Hadi).
        rewrite app_nat_fun_app.
        rewrite HeqL1.
        replace (concat (L1a ++ nth i L1 nil :: L1b))
           with (concat L1a ++ (nth i L1 nil) ++ concat L1b) by now rewrite concat_app.
        rewrite app_nat_fun_right; [ | reflexivity | ].
        2:{ apply all_lt_leq with (length (nth i lp nil))...
            length_lia. }
        rewrite app_nat_fun_left.
        2:{ rewrite<- Hleni... }
        change (concat (a :: L2)) with (a ++ concat L2).
        change a with (nth 0 (a :: L2) nil).
        rewrite Heqi'.
        replace (concat L2) with (app_nat_fun
                                    (map
                                       (fun k : nat =>
                                          if k <? length (concat L1a) then k else k + length (nth i lp nil)) p)
                                    (concat L1a ++ nth i L1 nil ++ concat L1b))...
        rewrite<- Heq'.
        rewrite Hleni.
        rewrite concat_app.
        apply andb_prop in Hperm' as (Hal' & _).
        rewrite Hlen' in Hal'.
        rewrite concat_app in Hal'.
        rewrite app_length in Hal'.
        remember (concat L1a); remember (concat L1b); remember (nth i L1 nil).
        clear - Hal'.
        induction p.
        -- destruct l; destruct l1; destruct l0...
        -- destruct l ; [ destruct l1; [ destruct l0 |] |]; rewrite ? app_nil_l...
           ++ clear.
              change (length nil) with 0.
              replace (map (fun k => if k <? 0 then k else k + 0) (a :: p)) with (a :: p)...
              remember (a :: p); clear.
              induction l...
              simpl in *; rewrite Nat.add_0_r; rewrite<- IHl...
           ++ change (length nil) with 0.
              replace (map (fun k => if k <? 0 then k else k + (length (a0 :: l1))) (a :: p))
                 with (incr_all (a :: p) (length (a0 :: l1)))...
              2:{ remember (a :: p); clear; induction l...
                  simpl in *.
                  rewrite Nat.add_comm.
                  rewrite IHl.
                  rewrite Nat.add_succ_r... }
              rewrite app_nat_fun_right...
           ++ change ((a0 :: l) ++ l1 ++ l0) with (a0 :: l ++ l1 ++ l0).
              change ((a0 :: l) ++ l0) with (a0 :: l ++ l0).
              change (map (fun k => if k<? length (a0 :: l) then k else k + length l1) (a :: p))
                with ((if a <? length (a0 :: l) then a else a + length l1)
                        :: (map (fun k => if k <? length (a0 :: l) then k else k + length l1) p)).
              app_nat_fun_unfold (map (fun k => if k <? length (a0 :: l) then k else k + length l1) p)
                                 (l ++ l1 ++ l0) (if a <? length (a0 :: l) then a else a + length l1) a0.
              app_nat_fun_unfold p (l ++ l0) a a0.
              change (a0 :: l ++ l1 ++ l0) with ((a0 :: l) ++ l1 ++ l0).
              change (a0 :: l ++ l0) with ((a0 :: l) ++ l0).
              rewrite IHp.
              replace (nth a ((a0 :: l) ++ l0) a0)
                 with (nth (if a <? length (a0 :: l) then a else a + length l1) ((a0 :: l) ++ l1 ++ l0) a0)...
              clear.
              case_eq (a <? length (a0 :: l)); intro Hcase;
                [ apply Nat.ltb_lt in Hcase | apply Nat.ltb_nlt in Hcase].
              ** rewrite ? app_nth1...
              ** rewrite app_nth2 by length_lia.
                 rewrite app_nth2 by length_lia.
                 rewrite app_nth2 by length_lia.
                 replace (a + length l1 - length (a0 :: l) - length l1)
                    with (a - length (a0 :: l)) by length_lia...
              ** apply andb_prop in Hal' as (_ & Hal')...
Qed.

Lemma perm_block {A} : forall (p1 : list nat) (L1 L2 : list (list A)),
    length p1 = length L1 ->
    is_perm p1 = true ->
    app_nat_fun p1 L1 = L2 ->
    { p & prod (is_perm p = true) ((length p = length (concat L1)) * (app_nat_fun p (concat L1) = concat L2))}.
Proof with try reflexivity; try assumption.
  intros p1 L1 L2 Hlen Hperm Heq.
  apply concat_perm with p1 (map (fun x => Id (length x)) L1)...
  - rewrite map_length...
  - rewrite <- Heq.
    destruct p1; destruct L1; try now inversion Hlen.
    unfold app_nat_fun; unfold app_nat_fun_dflt; rewrite map_length.
    symmetry...
  - rewrite<- Heq.
    apply andb_prop in Hperm as (Hal & _).
    rewrite Hlen in Hal.
    clear - Hal.
    induction p1; intros i Hleni; try now inversion Hleni.
    destruct i.
    + simpl.
      apply andb_prop in Hal as (Hlt & _).
      clear - Hlt.
      apply Nat.ltb_lt in Hlt.
      revert a Hlt; induction L1; intros n Hlt.
      * destruct n; (split; [ split | ])...
      * destruct n; simpl.
        -- split; [ split | ].
           ++ apply Id_is_perm.
           ++ rewrite seq_length...
           ++ rewrite app_Id...
        -- replace (nth n L1 a) with (nth 0 (app_nat_fun (n :: p1) L1) nil); [ apply IHL1; length_lia | ].
           destruct L1.
           ++ length_lia.
           ++ app_nat_fun_unfold p1 L1 n l.
              change (nth 0 (nth n (l :: L1) l :: app_nat_fun p1 (l :: L1)) nil) with (nth n (l :: L1) l).
              apply nth_indep...
              length_lia.
    + simpl.
      destruct L1.
      { simpl.
        destruct (nth i p1 0) ; (split ; [ split | ])... }
      app_nat_fun_unfold p1 L1 a l.
      apply IHp1...
      * apply andb_prop in Hal as (_ & Hal)...
      * length_lia.
Qed.


(* TRANSPOSITION DECOMPOSITION *)
Lemma nc_transpo_S : forall i j k, nc_transpo (S i) (S j) (S k) = 0 :: incr_all (nc_transpo i j k) 1.
Proof with try assumption; try reflexivity.
  intros i j k.
  unfold nc_transpo.
  case_eq (S j <? S k); intros Hcase1.
  - case_eq (S k <=? S i); intros Hcase2.
    + replace (j <? k) with true.
      replace (k <=? i) with true.
      simpl.
      rewrite incr_all_app.
      simpl.
      rewrite incr_all_app.
      simpl.
      rewrite 3 incr_all_seq.
      repeat f_equal; lia.
    + replace (j <? k) with true.
      replace (k <=? i) with false...
      simpl; rewrite incr_all_seq...
  - replace (j <? k) with false...
    simpl; rewrite incr_all_seq...
Qed.

Lemma incr_all_compo_nc_transpo : forall n l,
    0 :: incr_all (compo_nc_transpo (S n - 1) l) 1
  = compo_nc_transpo (S (S n) - 1) (map (fun x => (S (fst x) , S (snd x))) l).
Proof with try reflexivity; try assumption.
  intros n l.
  simpl.
  rewrite Nat.sub_0_r.
  induction l.
  - simpl; rewrite incr_all_seq...
  - destruct a.
    simpl.
    rewrite <- IHl.
    rewrite nc_transpo_S.
    app_nat_fun_unfold (incr_all (nc_transpo n n0 n1) 1) (incr_all (compo_nc_transpo n l) 1) 0 0.
    unfold nth.
    change 1 with (length (0 :: nil)) at 2.
    change (0 :: incr_all (compo_nc_transpo n l) 1) with ((0 :: nil) ++ incr_all (compo_nc_transpo n l) 1).
    rewrite app_nat_fun_right; [ | reflexivity | ].
    2:{ rewrite incr_all_length.
        rewrite compo_nc_transpo_length.
        apply all_lt_nc_transpo. }
    rewrite app_nat_fun_incr_all...
Qed.

Lemma transpo_is_perm : forall n i, is_perm (transpo n i) = true.
Proof with try reflexivity; try assumption.
  intros n i.
  splitb.
  - rewrite transpo_length.
    apply all_lt_transpo.
  - apply all_distinct_transpo.
Qed.

Lemma compo_transpo_is_perm : forall n l, is_perm (compo_transpo n l) = true.
Proof with try reflexivity; try assumption.
  intros n l.
  induction l.
  - apply Id_is_perm.
  - simpl.
    apply compo_perm_is_perm...
    + apply transpo_is_perm.
    + rewrite transpo_length; rewrite compo_transpo_length...
Qed.

Lemma nc_transpo_is_perm : forall n i j, is_perm (nc_transpo n i j) = true.
Proof with try reflexivity; try assumption.
  intros n i j.
  destruct (decomp_nc_transpo n i j).
  rewrite e.
  apply compo_transpo_is_perm.
Qed.

Lemma compo_nc_transpo_is_perm : forall n l, is_perm (compo_nc_transpo n l) = true.
Proof with try reflexivity; try assumption.
  intros n l.
  induction l.
  - apply Id_is_perm.
  - destruct a; simpl.
    apply compo_perm_is_perm...
    + apply nc_transpo_is_perm.
    + rewrite nc_transpo_length; rewrite compo_nc_transpo_length...
Qed.

Lemma decomp_perm_nc_transpo : forall p,
    is_perm p = true ->
    p <> nil ->
    {l & p = compo_nc_transpo ((length p) - 1) l}.
Proof with try reflexivity; try assumption.
  intro p.
  remember (length p).
  revert p Heqn.
  induction n; [ | destruct n]; intros p Heqn Hperm Hnnil.
  - destruct p; inversion Heqn; exfalso; apply Hnnil...
  - split with nil.
    destruct p; [inversion Heqn | destruct p; [ | inversion Heqn] ].
    destruct n...
    apply andb_prop in Hperm as [Hal _].
    simpl in Hal.
    inversion Hal.
  - destruct (perm_surj p 0 0 Hperm) as [i [Hlt Heqi]]; [lia | ].
    destruct (nth_split_Type i p 0) as [(la,lb) Heqp Hlenp]...
    destruct la.
    { simpl in Heqp.
      destruct (IHn (downshift lb 0)) as [l Heql].
      1,2,3:replace (downshift lb 0)
               with (downshift (0 :: lb) 0)
                 by (rewrite downshift_eq; reflexivity); rewrite<- Heqi at 1; rewrite<- Heqp.
      + apply Nat.succ_inj.
        rewrite downshift_perm_length; [ | lia | ]...
        rewrite<- Heqn...
      + apply downshift_perm...
      + remember (downshift p 0).
        destruct l; [ | intro H; inversion H].
        exfalso.
        assert (length (@nil nat) = length (downshift p 0)); [rewrite Heql | ]...
        rewrite downshift_perm_length in H.
        * rewrite <- Heqn in H.
          inversion H.
        * lia.
        * apply Hperm.
      + split with (map (fun x => (S (fst x), S (snd x))) l).
        rewrite Heqp.
        rewrite Heqi.
        replace lb with (incr_all (downshift lb 0) 1).
        2:{ apply incr_all_downshift_0.
            apply all_distinct_right with (@nil nat).
            apply andb_prop in Hperm as [_ Had].
            rewrite<- Heqi; rewrite<- Heqp... }
        rewrite Heql.
        rewrite incr_all_compo_nc_transpo... }
    destruct n0.
    { rewrite Heqp in Hperm.
      rewrite Heqi in Hperm.
      simpl in Hperm.
      apply andb_prop in Hperm as [_ Had].
      simpl in Had.
      apply andb_prop in Had as [H _].
      apply negb_true_iff in H.
      rewrite In_nat_bool_app in H.
      apply orb_false_iff in H as [_ H].
      simpl in H.
      inversion H. }
    simpl in Heqp.
    destruct (IHn (downshift (la ++ (S n0) :: lb) 0)) as [l Heql].
    + apply Nat.succ_inj.
      rewrite downshift_length.
      * rewrite Heqn.
        rewrite Heqp.
        simpl; rewrite 2 app_length...
      * rewrite Heqp in Hperm.
        rewrite Heqi in Hperm.
        apply andb_prop in Hperm as [_ Had].
        change (S n0 :: la ++ 0 :: lb) with ((S n0 :: la) ++ 0 :: lb) in Had.
        apply all_distinct_right in Had as Had1.
        apply all_distinct_left in Had.
        apply orb_false_iff in Had.
        change (fix In_nat_bool (n : nat) (l : list nat) {struct l} : bool :=
                  match l with
                  | nil => false
                  | k :: l0 => (n =? k) || In_nat_bool n l0
                  end) with In_nat_bool in Had.
        destruct Had as [H1 Had2].
        rewrite In_nat_bool_app.
        apply orb_false_intro...
    + splitb.
      * rewrite<- downshift_all_lt...
        rewrite downshift_length.
        2:{ rewrite Heqp in Hperm.
            rewrite Heqi in Hperm.
            apply andb_prop in Hperm as [_ Had].
            change (S n0 :: la ++ 0 :: lb) with ((S n0 :: la) ++ 0 :: lb) in Had.
            apply all_distinct_right in Had as Had1.
            apply all_distinct_left in Had.
            apply orb_false_iff in Had.
            change (fix In_nat_bool (n : nat) (l : list nat) {struct l} : bool :=
                      match l with
                      | nil => false
                      | k :: l0 => (n =? k) || In_nat_bool n l0
                      end) with In_nat_bool in Had.
            destruct Had as [H1 Had2].
            rewrite In_nat_bool_app.
            apply orb_false_intro... }
        rewrite all_lt_app.
        rewrite Heqp in Hperm.
        apply andb_prop in Hperm as [Hal _].
        change (length (S n0 :: la ++ nth i p 0 :: lb)) with (S (length (la ++ nth i p 0 :: lb))) in Hal.
        rewrite app_length in *.
        simpl in Hal.
        apply andb_prop in Hal as [Hlt1 Hal].
        rewrite all_lt_app in Hal.
        apply andb_prop in Hal as [Hala Hal].
        simpl in Hal.
        apply andb_prop in Hal as [Hlt2 Halb].
        rewrite Heqi in Hlt2.
        simpl.
        splitb...
        splitb...
      * apply downshift_keep_all_distinct.
        apply cond_all_distinct.
        apply andb_prop in Hperm as [_ Had].
        rewrite Heqp in Had.
        rewrite Heqi in Had.
        clear - Had.
        revert Had.
        induction la; intros Had n1 n2 k Hlt1 Hlt2 Heq.
        -- simpl in Had.
           apply andb_prop in Had as [nHin Had].
           apply andb_prop in Had as [_ Had].
           apply cond_all_distinct_inv with (S n0 :: lb) k...
           splitb...
        -- destruct n1; destruct n2...
           ++ simpl in Heq.
              exfalso.
              symmetry in Heq.
              simpl in Hlt2.
              apply Lt.lt_S_n in Hlt2.
              apply neg_nth_eq in Heq...
              simpl in Had.
              change (match a with | 0 => false | S m' => n0 =? m' end) with (S n0 =? a) in Had.
              apply andb_prop in Had as [nHin Had].
              apply negb_true_iff in nHin.
              apply orb_false_iff in nHin as [nHeq _].
              apply andb_prop in Had as [nHin _].
              apply negb_true_iff in nHin.
              rewrite In_nat_bool_app in nHin.
              apply orb_false_iff in nHin as [nHina nHin].
              simpl in nHin.
              apply orb_false_iff in nHin as [_ nHinb].
              rewrite In_nat_bool_app.
              apply orb_false_iff.
              split...
              simpl.
              apply orb_false_iff; split...
              rewrite Nat.eqb_sym...
           ++ simpl in Heq.
              exfalso.
              simpl in Hlt1.
              apply Lt.lt_S_n in Hlt1.
              apply neg_nth_eq in Heq...
              simpl in Had.
              change (match a with | 0 => false | S m' => n0 =? m' end) with (S n0 =? a) in Had.
              apply andb_prop in Had as [nHin Had].
              apply negb_true_iff in nHin.
              apply orb_false_iff in nHin as [nHeq _].
              apply andb_prop in Had as [nHin _].
              apply negb_true_iff in nHin.
              rewrite In_nat_bool_app in nHin.
              apply orb_false_iff in nHin as [nHina nHin].
              simpl in nHin.
              apply orb_false_iff in nHin as [_ nHinb].
              rewrite In_nat_bool_app.
              apply orb_false_iff.
              split...
              simpl.
              apply orb_false_iff; split...
              rewrite Nat.eqb_sym...
           ++ replace n2 with n1...
              simpl in Heq.
              simpl in Hlt1, Hlt2.
              apply Lt.lt_S_n in Hlt1.
              apply Lt.lt_S_n in Hlt2.
              apply IHla with k...
              simpl in Had.
              apply andb_prop in Had as [nHin Had].
              apply negb_true_iff in nHin.
              apply orb_false_iff in nHin as [_ nHin].
              apply andb_prop in Had as [_ Had].
              splitb...
              apply negb_true_iff...
    + apply not_eq_sym.
      rewrite downshift_app.
      rewrite downshift_gt...
      apply app_cons_not_nil.
    + assert (0 :: (la ++ S n0 :: lb) = 0 :: incr_all (compo_nc_transpo (S n - 1) l) 1) as Heq0.
      { replace (incr_all (compo_nc_transpo (S n - 1) l) 1) with (la ++ S n0 :: lb)...
        replace la with (incr_all (downshift la 0) 1).
        2:{ apply incr_all_downshift_0.
            apply all_distinct_left with lb.
            rewrite Heqp in Hperm.
            rewrite Heqi in Hperm.
            apply andb_prop in Hperm as [_ Had].
            apply andb_prop in Had as [_ Had]... }
        replace lb with (incr_all (downshift lb 0) 1).
        2:{ apply incr_all_downshift_0.
            apply all_distinct_right with la.
            rewrite Heqp in Hperm.
            rewrite Heqi in Hperm.
            apply andb_prop in Hperm as [_ Had].
            apply andb_prop in Had as [_ Had]... }
        change (S n0 :: incr_all (downshift lb 0) 1) with (incr_all (n0 :: downshift lb 0) 1).
        rewrite<- incr_all_app.
        rewrite downshift_app in Heql.
        rewrite downshift_gt in Heql...
        simpl in Heql.
        rewrite Heql... }
      split with ((0 , i) :: map (fun x : nat * nat => (S (fst x), S (snd x))) l).
      simpl.
      change (S n) with (S (S n) - 1).
      rewrite<- incr_all_compo_nc_transpo.
      rewrite <- Heq0.
      change (0 :: la ++ S n0 :: lb) with (nil ++ 0 :: la ++ S n0 :: lb).
      rewrite app_nc_transpo...
      * rewrite Heqp.
        rewrite Heqi...
      * rewrite Heqn.
        rewrite Heqp.
        repeat (simpl; rewrite app_length).
        simpl; lia.
      * simpl.
        simpl in Hlenp.
        rewrite Hlenp...
Qed.

Lemma decomp_perm_transpo : forall p,
    is_perm p = true ->
    p <> nil ->
    {l & p = compo_transpo ((length p) - 1) l}.
Proof with try reflexivity; try assumption.
  intros p Hperm Hnnil.
  destruct (decomp_perm_nc_transpo p Hperm Hnnil) as [l Heqp].
  remember (length p).
  rewrite Heqp.
  destruct n.
  { destruct p; try now (exfalso; apply Hnnil); try now inversion Heqn. }
  clear.
  simpl.
  rewrite Nat.sub_0_r.
  induction l.
  - split with nil...
  - destruct a.
    simpl.
    destruct (decomp_nc_transpo n n0 n1) as [l_nc Heq].
    rewrite Heq.
    destruct IHl as [l0 Heql0].
    rewrite Heql0.
    split with (l_nc ++ l0).
    rewrite app_compo_transpo...
Qed.

Lemma Perm_rect {A} :
  forall P : list nat -> list A -> Type,
    (forall l, P (Id (length l)) l) ->
    (forall l i, l <> nil -> P (transpo ((length l) - 1) i) l) ->
    (forall f1 f2 l, is_perm f1 = true -> is_perm f2 = true -> length l = length f1 -> length f2 = length f1 ->
                        P f1 l -> P f2 (app_nat_fun f1 l) -> P (app_nat_fun f2 f1) l) ->
    forall f l, is_perm f = true -> length f = length l -> P f l.
Proof with try reflexivity; try assumption.
  intros P Hid Htranspo Htrans f l Hperm Hlen.
  destruct f.
  { destruct l; try now inversion Hlen.
    change nil with (Id (length (@nil A))) at 1.
    apply Hid... }  
  revert P Hid Htranspo Htrans.
  destruct (decomp_perm_transpo (n :: f)) as [lt Heq]; [ | intros H; inversion H | ]...
  rewrite Hlen in Heq.
  rewrite Heq.
  assert (l <> nil) as Hnnil.
  { intros H; destruct l; try now inversion Hlen; try now inversion H. }
  clear f n Heq Hlen Hperm.
  revert l Hnnil.
  induction lt; intros l0 Hnnil P Hid Htranspo Htrans.
  - unfold compo_transpo.
    destruct l0; try now (exfalso; apply Hnnil).
    replace (S (length (a :: l0) - 1)) with (length (a :: l0)) by length_lia.
    apply Hid.
  - simpl; apply Htrans.
    + apply compo_transpo_is_perm.
    + apply transpo_is_perm.
    + rewrite compo_transpo_length.
      destruct l0; try now (exfalso; apply Hnnil).
      length_lia.
    + rewrite transpo_length; rewrite compo_transpo_length...
    + apply IHlt...
    + replace (length l0 - 1) with (length (app_nat_fun (compo_transpo (length l0 - 1) lt) l0) - 1) at 1.
      2:{ rewrite app_nat_fun_length...
          rewrite compo_transpo_length.
          length_lia. }
      apply Htranspo...
      intros H.
      assert (length (app_nat_fun (compo_transpo (length l0 - 1) lt) l0) = 0).
      { change 0 with (length (@nil A)) at 2.
        rewrite H... }
      rewrite app_nat_fun_length in H0...
      rewrite compo_transpo_length in H0.
      length_lia.
Qed.

