(* Properties of lists of natural numbers that represent permutations. *)

From Stdlib Require Import Bool PeanoNat CMorphisms Lia.
From OLlibs Require Import funtheory List_more.
Require Import List_nat Fun_nat Transposition length_lia.

Ltac splitb := apply andb_true_intro; split.


(* PERMUTATION DEFINITION *)

Definition is_perm l := all_lt l (length l) && all_distinct l.

Definition perm := {p & is_perm p = true}.
Definition perm_of n := {p : _ & is_perm p = true & length p = n}.


(* Some facts about is_perm *)

Lemma tail_perm : forall l k,
  is_perm (k :: l) = true -> is_perm (downshift l k) = true.
Proof with try assumption.
intros l k Hp.
apply andb_true_iff in Hp as [Hp1 Hp2].
simpl in Hp1; apply andb_true_iff in Hp1 as [Hp1 Hp3].
apply Nat.ltb_lt in Hp1.
simpl in Hp2; apply andb_true_iff in Hp2 as [Hp2 Hp4].
apply negb_true_iff in Hp2.
apply andb_true_iff; split.
- rewrite downshift_length...
  rewrite all_lt_downshift by (apply Nat.leb_le; lia)...
- apply downshift_keep_all_distinct; assumption.
Qed.

Lemma perm_surj : forall p k0 k, is_perm p = true -> k < length p ->
  { i : _ & i < length p & nth i p k0 = k }.
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
    exists 0; [ lia | reflexivity ].
  + apply IHn with _ k0 (pred k) in Hperm; [ | | lia ].
    * destruct Hperm as [i Hnth1 Hnth2].
      exists (S i); [ lia | simpl ].
      rewrite nth_indep with _ _ _ _ (pred k0) in Hnth2 by (rewrite downshift_length; assumption).
      rewrite nth_ge_downshift in Hnth2; [ | assumption | ].
      -- assert (In_nat_bool (nth i p k0) p = true)
           by (apply cond_In_nat_bool; now exists (k0,i)).
         destruct (nth i p k0); try lia.
         destruct k; [ reflexivity | exfalso ].
         simpl in Hnth2; subst.
         destruct n0; try lia.
         rewrite Hn0 in H; inversion H.
      -- rewrite nth_indep with _ _ _ _ (pred k0) by (rewrite downshift_length; assumption); lia.
    * now rewrite downshift_length.
  + assert (k < n0) as Hlt3
      by (apply Nat.ltb_ge in Hlt2; apply Nat.eqb_neq in Heqk; lia).
    apply IHn with _ k0 k in Hperm.
    * destruct Hperm as [i Hnth1 Hnth2].
      exists (S i); [ lia | simpl ].
      now rewrite nth_lt_downshift in Hnth2; try lia. 
    * now rewrite downshift_length.
    * apply andb_true_iff in Hperm1 as [Hperm1 _]; simpl in Hperm1.
      apply Nat.ltb_lt in Hperm1; lia.
Qed.

Lemma decomp_perm : forall l k, k < length l -> is_perm l = true ->
  {' (la, lb) : _ & l = la ++ k :: lb & prod (In_nat_bool k la = false) (In_nat_bool k lb = false) }.
Proof with try reflexivity; try assumption.
  intros l k Hlen Hperm.
  destruct (perm_surj l 0 k Hperm Hlen) as [i Hleni Heq].
  destruct (nth_splitT l 0 Hleni) as [(la,lb) Heql Heq_len].
  split with (la, lb); [ | split].
  - rewrite<- Heq...
  - apply andb_prop in Hperm as (_ & Had).
    rewrite Heql, Heq in Had.
    apply all_distinct_left with lb...
  - apply andb_prop in Hperm as (_ & Had).
    rewrite Heql, Heq in Had.
    apply all_distinct_right with la...
Qed.

Lemma downshift_perm_length : forall l k, k < length l -> is_perm l = true ->
  length (downshift l k) = pred (length l).
Proof with try reflexivity; try assumption.
  intros l k Hlen Hperm.
  destruct (decomp_perm l k Hlen Hperm) as [(la & lb) Heq (nHinla & nHinlb)].
  rewrite Heq, downshift_app, 2 length_app, downshift_eq.
  simpl; rewrite Nat.add_succ_r, 2 downshift_length...
Qed.

Lemma downshift_perm : forall l k,
  is_perm l = true -> is_perm (downshift l k) = true.
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
    rewrite <- all_lt_downshift with _ _ k in Halt...
    simpl in Hlt.
    apply Nat.leb_le; lia.
  - rewrite downshift_if_all_lt...
    apply Nat.ltb_nlt in Hlt.
    apply andb_prop in Hperm as (Hal & _).
    apply all_lt_leq with (length l); [ assumption | lia ].
Qed.

Lemma all_distinct_app_perm : forall (l : list nat) p, length p = length l -> is_perm p = true ->
  all_distinct (app_nat_fun p l) = all_distinct l.
Proof with try reflexivity; try assumption.
  destruct l...
  unfold app_nat_fun.
  intros p Hlen Hperm.
  destruct (andb_prop _ _ Hperm) as (H1 & H2).
  simpl in Hlen.
  case_eq (all_distinct (n :: l)); intros Hal; symmetry.
  - symmetry; apply cond_all_distinct.
    intros n1 n2 k Hlt1 Hlt2 Heq.
    assert (H := cond_all_distinct_inv (n :: l)).
    specialize (H Hal) as H.
    clear Hal.
    assert (H0 := cond_all_distinct_inv p).
    specialize (H0 H2).
    unfold app_nat_fun_dflt in Hlt1, Hlt2; rewrite length_map in Hlt1 , Hlt2.
    apply H0 with n...
    apply H with n; try (simpl; rewrite<- Hlen)...
    + apply cond_all_lt_inv...
    + apply cond_all_lt_inv...
    + rewrite 2 nth_nth_nth_map; [ | left | left]...
      rewrite 2 nth_indep with _ _ _ n k by (rewrite length_map; assumption)...
  - apply cond_all_distinct_false_inv with _ n in Hal as ((k1 & k2) & (Hlt1 & (Hlt2 & (nHeq & Heq)))).
    simpl in Hlt1 , Hlt2.
    rewrite<- Hlen in Hlt1, Hlt2.
    destruct (perm_surj _ n k1 Hperm Hlt1) as [i1 Hlti1 Heqk1].
    destruct (perm_surj _ n k2 Hperm Hlt2) as [i2 Hlti2 Heqk2].
    symmetry; apply cond_all_distinct_false with n i1 i2.
    + unfold app_nat_fun_dflt; rewrite length_map...
    + unfold app_nat_fun_dflt; rewrite length_map...
    + intro H.
      apply nHeq.
      apply cond_all_distinct_inv with p n...
      rewrite<- Heqk1, <- Heqk2, H...
    + unfold app_nat_fun_dflt; rewrite <- 2 nth_nth_nth_map with (dn := n); [ | left | left ]...
      rewrite Heqk1, Heqk2...
Qed.

Lemma all_lt_app_perm : forall (l : list nat) n p, length p = length l -> is_perm p = true ->
  all_lt (app_nat_fun p l) n = all_lt l n.
Proof with try reflexivity; try assumption.
  intros l n p Hlen Hperm.
  case_eq (all_lt l n); intros Heq; symmetry.
  - destruct l...
    symmetry; apply cond_all_lt.
    intros k0 k Hlt.
    unfold app_nat_fun, app_nat_fun_dflt  in *.
    rewrite length_map in Hlt.
    rewrite (nth_indep _ k0 n0) by (rewrite length_map; assumption).
    rewrite<- nth_nth_nth_map with (dn := n0); [ | left ]...
    apply cond_all_lt_inv...
    apply cond_all_lt_inv...
    apply andb_prop in Hperm as (H & _)...
    rewrite<- Hlen...
  - destruct l; try now inversion Heq...
    unfold app_nat_fun; unfold app_nat_fun_dflt.
    destruct (cond_all_lt_false_inv _ _ Heq n0) as (k & (Hlen' & Hge)).
    rewrite<- Hlen in Hlen'.
    destruct (perm_surj _ n0 k Hperm Hlen') as [i Hlen'' Heqi].
    symmetry; apply cond_all_lt_false with i n0.
    + rewrite length_map...
    + rewrite <- nth_nth_nth_map with (dn := n0); [ | left ]...
      rewrite Heqi...
Qed.

Lemma compo_perm_is_perm : forall l1 l2, is_perm l1 = true -> is_perm l2 = true -> length l1 = length l2 ->
  is_perm (l1 ∘ l2) = true.
Proof.
  intros l1 l2 Hp1 Hp2 Hlen; splitb.
  - rewrite all_lt_app_perm; try assumption.
    apply andb_prop in Hp2 as (Hp2 & _).
    destruct l2; [ reflexivity | ].
    unfold app_nat_fun.
    unfold app_nat_fun_dflt; rewrite length_map.
    now rewrite Hlen.
  - apply andb_prop in Hp2 as (Halt2 & Had2).
    now rewrite all_distinct_app_perm.
Qed.

Lemma p_compo n (p2 : perm_of n) (p1 : perm_of n) : perm_of n.
Proof.
destruct p1 as [p1 Hp1 Hlen1]; destruct p2 as [p2 Hp2 Hlen2]; simpl in Hlen1; symmetry in Hlen2; subst.
now exists (p1 ∘ p2); [ apply compo_perm_is_perm | rewrite app_nat_fun_length; simpl ].
Defined.

Lemma Id_is_perm : forall n, is_perm (Id n) = true.
Proof. intros n; splitb; [ rewrite length_seq; apply all_lt_seq; lia | apply all_distinct_seq ]. Qed.

Lemma p_Id n : perm_of n.
Proof. exists (Id n); [ apply Id_is_perm | apply length_seq ]. Defined.

Lemma cfun_is_perm : forall n m, is_perm (cfun n m) = true.
Proof.
  intros n m; unfold cfun; splitb.
  - rewrite length_app, 2 length_seq.
    replace (m + n) with (n + m) by lia.
    apply all_lt_cfun.
  - apply all_distinct_cfun.
Qed.

Lemma p_cfun n m : perm_of (n + m).
Proof. exists (cfun n m); [ apply cfun_is_perm | apply cfun_length ]. Defined.

Lemma append_perm_is_perm : forall f1 f2,
  is_perm f1 = true -> is_perm f2 = true -> is_perm (f1 +++ f2) = true.
Proof with try reflexivity; try assumption.
  intros f1 f2 Hp1 Hp2.
  apply andb_prop in Hp1 as (Hal1 & Had1).
  apply andb_prop in Hp2 as (Hal2 & Had2).
  splitb.
  - rewrite length_app, shift_length.
    apply append_fun_all_lt...
  - apply all_distinct_app...
Qed.

Lemma p_append n m (p1 : perm_of n) (p2 : perm_of m) : perm_of (n + m).
Proof.
destruct p1 as [p1 Hp1 Hlen1]; destruct p2 as [p2 Hp2 Hlen2].
exists (p1 +++ p2); [ now apply append_perm_is_perm | rewrite length_app, shift_length; lia ].
Defined.

Lemma transpo_is_perm : forall n i, is_perm (transpo n i) = true.
Proof. intros n i; splitb; [ rewrite transpo_length; apply all_lt_transpo | apply all_distinct_transpo ]. Qed.

Lemma p_transpo n (i : nat) : perm_of (S n).
Proof. exists (transpo n i); [ apply transpo_is_perm | apply transpo_length ]. Defined.

Lemma compo_transpo_is_perm : forall n l, is_perm (compo_transpo n l) = true.
Proof.
  induction l.
  - apply Id_is_perm.
  - simpl; apply compo_perm_is_perm; try assumption.
    + apply transpo_is_perm.
    + now rewrite transpo_length, compo_transpo_length.
Qed.

Lemma p_compo_transpo n (l : list nat) : perm_of (S n).
Proof. exists (compo_transpo n l); [ apply compo_transpo_is_perm | apply compo_transpo_length ]. Defined.

Lemma nc_transpo_is_perm : forall n i j, is_perm (nc_transpo n i j) = true.
Proof.
intros n i j.
destruct (decomp_nc_transpo n i j) as [l Heq]; rewrite Heq.
apply compo_transpo_is_perm.
Qed.

Lemma p_nc_transpo n (i j : nat) : perm_of (S n).
Proof. exists (nc_transpo n i j); [ apply nc_transpo_is_perm | apply nc_transpo_length ]. Defined.

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

Lemma p_compo_nc_transpo n (l : list (nat * nat)) : perm_of (S n).
Proof. exists (compo_nc_transpo n l); [ apply compo_nc_transpo_is_perm | apply compo_nc_transpo_length ]. Defined.

Lemma is_perm_length_1_inv : forall n, is_perm (n :: nil) = true -> n = 0.
Proof.
intros n Hperm.
apply andb_prop in Hperm as [Hal Had].
simpl in Hal; rewrite andb_true_r in Hal; apply Nat.ltb_lt in Hal.
lia.
Qed.

Lemma is_perm_length_2_inv : forall n m,
  is_perm (n :: m :: nil) = true -> { n = 0 /\ m = 1 } + { n = 1 /\ m = 0 }.
Proof.
intros n m Hperm.
apply andb_prop in Hperm as [Hal Had].
simpl in Hal; rewrite andb_true_r in Hal; apply andb_prop in Hal as [Hn Hm].
apply Nat.ltb_lt in Hn; apply Nat.ltb_lt in Hm.
destruct n; destruct m; try now inversion Had.
- destruct m; try (exfalso; lia).
  now left.
- destruct n; try (exfalso; lia).
  now right.
- destruct n; destruct m; try (exfalso; lia).
  inversion Had.
Qed.

Lemma app_nat_fun_vs_cons {A} : forall l1 l2 (a : A) n p,
  length (n :: p) = length l2 -> is_perm (n :: p) = true ->
  a :: l1 = (n :: p) ∘ l2 -> {' (la, lb) | l2 = la ++ a :: lb & length la = n }.
Proof.
  intros l1 l2 a n p Hlen Hperm Heq.
  destruct l2; try now inversion Heq.
  unfold app_nat_fun, app_nat_fun_dflt in Heq.
  rewrite map_cons in Heq.
  remember (a0 :: l2) as l3.
  inversion Heq; subst.
  apply nth_splitT.
  apply andb_prop in Hperm as (Halt & _).
  apply andb_prop in Halt as (Hlt & _).
  apply Nat.ltb_lt in Hlt; lia.
Qed.


(* Permutation by Blocks *)
Lemma concat_perm {A} : forall p1 (L1 L2 : list (list A)) lp,
    length p1 = length L1 ->
    length p1 = length lp ->
    length L1 = length L2 ->
    is_perm p1 = true ->
    (forall i,
        i < length p1 ->
        (is_perm (nth (nth i p1 0) lp nil) = true) *
        (length (nth (nth i p1 0) lp nil) = length (nth (nth i p1 0) L1 nil)) *
        (nth i L2 nil = app_nat_fun (nth (nth i p1 0) lp nil) (nth (nth i p1 0) L1 nil))) ->
    { p : _ & is_perm p = true & prod (length p = length (concat L1)) (p ∘ (concat L1) = concat L2) }.
Proof with try reflexivity; try assumption; try length_lia.
  intros p1 L1 L2; revert p1 L1; induction L2; intros p1 L1 lp Hlen1 Hlenp Hlen2 Hperm H.
  - split with nil; destruct L1; try now inversion Hlen2.
  - destruct p1 as [ | i p1]; [ destruct L1; inversion Hlen1; now inversion Hlen2 | ].
    destruct (andb_prop _ _ Hperm) as (Hal & Had); simpl in Hal, Had.
    apply andb_prop in Hal as (Hlt & Hal); apply Nat.ltb_lt in Hlt.
    apply andb_prop in Had as (nHin & Had); apply negb_true_iff in nHin.
    destruct (@nth_splitT _ i lp nil) as [(lpa,lpb) Heqlp Hlenlpa]...
    destruct (@nth_splitT _ i L1 nil) as [(L1a,L1b) HeqL1 HlenL1a]...
    specialize (IHL2 (downshift p1 i) (L1a ++ L1b) (lpa ++ lpb)) as [p Hperm' [Hlen' Heq']].
    + rewrite HeqL1 in Hlen1; rewrite downshift_length...
    + rewrite Heqlp in Hlenp; rewrite downshift_length...
    + rewrite HeqL1 in Hlen2...
    + rewrite <- downshift_eq; apply downshift_perm...
    + intros j Hltj.
      rewrite downshift_length in Hltj...
      case_eq (nth j p1 0 <? i); intros Hcase; [apply Nat.ltb_lt in Hcase | apply Nat.ltb_nlt in Hcase].
      * rewrite nth_downshift_lt...
        destruct (H (S j)) as ((Hpermj & Hlenj) & Heqj)...
        split; [ split |].
        -- rewrite Heqlp in Hpermj.
           rewrite app_nth1 by now rewrite Hlenlpa.
           rewrite<- (app_nth1 _ (nth i lp nil :: lpb)) by now rewrite Hlenlpa...
        -- rewrite Heqlp, HeqL1 in Hlenj.
           rewrite app_nth1 by now rewrite Hlenlpa.
           rewrite app_nth1 by now rewrite HlenL1a.
           rewrite<- (app_nth1 _ (nth i lp nil :: lpb)) by now rewrite Hlenlpa.
           rewrite<- (app_nth1 _ (nth i L1 nil :: L1b)) by now rewrite HlenL1a...
        -- change (nth j L2 nil) with (nth (S j) (a :: L2) nil).
           change (nth j p1 0) with (nth (S j) (i :: p1) 0).
           rewrite 2 app_nth1...
           rewrite Heqj, Heqlp, HeqL1.
           rewrite 2 app_nth1...
      * assert (nth j p1 0 <> i) by now apply cond_negb_In_nat_bool.
        change 0 with (pred 0).
        rewrite nth_downshift_ge...
        destruct (H (S j)) as ((Hpermj & Hlenj) & Heqj)...
        rewrite app_nth2 by (rewrite Hlenlpa ; lia).
        rewrite app_nth2 by (rewrite HlenL1a ; lia).
        replace (nth (pred (nth j p1 0) - length lpa) lpb nil)
          with (nth (nth j p1 0 - length lpa) (nth i lp nil :: lpb) nil)
          by now replace (nth j p1 0 - length lpa) with (S (pred (nth j p1 0) - length lpa)) by lia.
        replace (nth (pred (nth j p1 0) - length L1a) L1b nil)
          with (nth (nth j p1 0 - length L1a) (nth i L1 nil :: L1b) nil)
          by now replace (nth j p1 0 - length L1a) with (S (pred (nth j p1 0) - length L1a)) by lia.
        rewrite<- (app_nth2 lpa); [| rewrite Hlenlpa ]...
        rewrite<- (app_nth2 L1a); [ | rewrite HlenL1a ]...
        split; [ split |].
        -- change (nth j p1 0) with (nth (S j) (i :: p1) 0).
           rewrite Heqlp in Hpermj...
        -- rewrite Heqlp, HeqL1 in Hlenj.
           change (nth j p1 0) with (nth (S j) (i :: p1) 0)...
        -- change (nth j L2 nil) with (nth (S j) (a :: L2) nil).
           rewrite HeqL1, Heqlp in Heqj... 
    + split with (incr_all (nth i lp nil) (length (concat L1a)) ++
                    shift p (length (concat L1a)) (length (nth i lp nil))); [splitb | split].
      * rewrite all_lt_app; splitb.
        -- apply all_lt_leq
            with (length (incr_all (nth i lp nil) (length (concat L1a))) + length (concat L1a))...
           rewrite shift_length, Nat.add_comm, all_lt_shift_true...
           destruct (H 0) as ((Hpermi & _) & _)...
           apply andb_prop in Hpermi as (Hali & _)...
        -- rewrite length_app, shift_length, shift_length.
           apply andb_prop in Hperm'; destruct Hperm' as (Hal' & _).
           rewrite all_lt_shift_true...
      * destruct (H 0) as ((Hpermi & _) & _); [length_lia | ].
        apply andb_prop in Hpermi as (Hali & Hadi).
        apply andb_prop in Hperm' as (Hal' & Had').
        rewrite all_distinct_app_commu.
        apply all_distinct_app_shift...
      * destruct (H 0) as ((_ & Hleni) & _)...
        rewrite HeqL1...
      * destruct (H 0) as ((Hpermi & Hleni) & Heqi')...
        change (nth 0 (i :: p1) 0) with i in Hpermi, Hleni, Heqi'.
        apply andb_prop in Hpermi as (Hali & Hadi).
        rewrite app_nat_fun_app.
        rewrite HeqL1.
        replace (concat (L1a ++ nth i L1 nil :: L1b))
           with (concat L1a ++ (nth i L1 nil) ++ concat L1b) by now rewrite concat_app.
        rewrite app_nat_fun_right;
          [ | reflexivity | apply all_lt_leq with (length (nth i lp nil)) ; [ assumption | length_lia] ].
        rewrite app_nat_fun_left by now rewrite<- Hleni.
        simpl concat; change a with (nth 0 (a :: L2) nil).
        rewrite Heqi'.
        replace (concat L2)
           with (app_nat_fun (shift p (length (concat L1a)) (length (nth i lp nil)))
                             (concat L1a ++ nth i L1 nil ++ concat L1b))...
        rewrite<- Heq'.
        rewrite Hleni.
        rewrite concat_app.
        apply andb_prop in Hperm' as (Hal' & _).
        rewrite Hlen', concat_app, length_app in Hal'.
        destruct p.
        -- simpl; rewrite 2 app_nat_fun_nil...
        -- rewrite<- length_app in Hal'.
           apply app_nat_fun_shift...
Qed.

Lemma perm_block {A} : forall p1 (L1 L2 : list (list A)),
  length p1 = length L1 -> is_perm p1 = true ->
  p1 ∘ L1 = L2 ->
    { p : _ & is_perm p = true & prod (length p = length (concat L1)) (p ∘ (concat L1) = concat L2) }.
Proof with try reflexivity; try assumption; try length_lia.
  intros p1 L1 L2 Hlen Hperm Heq.
  apply concat_perm with p1 (map (fun x => Id (length x)) L1)...
  - rewrite <- Heq.
    destruct p1; destruct L1; try now inversion Hlen.
    unfold app_nat_fun; unfold app_nat_fun_dflt; rewrite length_map; symmetry...
  - rewrite<- Heq.
    apply andb_prop in Hperm as (Hal & _); rewrite Hlen in Hal; clear - Hal.
    induction p1; intros i Hleni; try (now inversion Hleni); destruct i; simpl.
    + apply andb_prop in Hal as (Hlt & _); clear - Hlt; apply Nat.ltb_lt in Hlt.
      revert a Hlt; induction L1; intros n Hlt; [inversion Hlt | ].
      destruct n; simpl.
      * split; [ split | ]...
        -- apply Id_is_perm.
        -- rewrite app_Id...
      * replace (nth n L1 a) with (nth 0 (app_nat_fun (n :: p1) L1) nil); [ apply IHL1 | ]...
        destruct L1...
        app_nat_fun_unfold p1 L1 n l.
        change (nth 0 (nth n (l :: L1) l :: app_nat_fun p1 (l :: L1)) nil) with (nth n (l :: L1) l).
        apply nth_indep...
    + destruct L1; [ simpl; destruct (nth i p1 0) ; now repeat split | ].
      simpl in Hal; apply andb_prop in Hal as (_ & Hal).
      app_nat_fun_unfold p1 L1 a l.
      apply IHp1...
Qed.


(* Transposition Decomposition *)
Lemma nc_transpo_S : forall i j k, nc_transpo (S i) (S j) (S k) = 0 :: incr_all (nc_transpo i j k) 1.
Proof.
  intros i j k.
  unfold nc_transpo.
  case_eq (S j <? S k); intros Hcase1;
    [ replace (j <? k) with true; case_eq (S k <=? S i); intros Hcase2 | ].
  - replace (k <=? i) with true.
    simpl; rewrite shift_app; simpl; rewrite shift_app; simpl.
    rewrite 3 incr_all_seq.
    repeat f_equal; lia.
  - replace (k <=? i) with false.
    now simpl; rewrite incr_all_seq.
  - replace (j <? k) with false.
    now simpl; rewrite incr_all_seq.
Qed.

Lemma incr_all_compo_nc_transpo : forall n l,
    0 :: incr_all (compo_nc_transpo n l) 1
  = compo_nc_transpo (S n) (map (fun x => (S (fst x), S (snd x))) l).
Proof with try reflexivity; try assumption.
  induction l.
  - simpl; rewrite incr_all_seq...
  - destruct a.
    simpl.
    rewrite <- IHl.
    rewrite nc_transpo_S.
    app_nat_fun_unfold (shift (nc_transpo n n0 n1) 0 1) (shift (compo_nc_transpo n l) 0 1) 0 0.
    unfold nth.
    change 1 with (length (0 :: nil)) at 2.
    change (0 :: shift (compo_nc_transpo n l) 0 1) with ((0 :: nil) ++ shift (compo_nc_transpo n l) 0 1).
    rewrite app_nat_fun_right; [ now rewrite app_nat_fun_incr_all | reflexivity | ].
    rewrite shift_length, compo_nc_transpo_length.
    apply all_lt_nc_transpo.
Qed.

Lemma decomp_perm_nc_transpo : forall p, is_perm p = true -> p <> nil ->
  {l & p = compo_nc_transpo ((length p) - 1) l}.
Proof with try reflexivity; try assumption.
  intro p.
  remember (length p); revert p Heqn; induction n; [ | destruct n]; intros p Heqn Hperm Hnnil.
  - destruct p; inversion Heqn; exfalso; apply Hnnil...
  - split with nil.
    destruct p; [inversion Heqn | destruct p; [ | inversion Heqn] ].
    destruct n...
    apply andb_prop in Hperm as [Hal _].
    inversion Hal.
  - destruct (perm_surj p 0 0 Hperm) as [i Hlt Heqi]; [lia | ].
    destruct (@nth_splitT _ i p 0) as [(la,lb) Heqp Hlenp]...
    destruct la.
    { simpl in Heqp.
      destruct (IHn (downshift lb 0)) as [l Heql].
      1,2,3:replace (downshift lb 0) with (downshift (0 :: lb) 0)
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
      + split with (map (fun x => (S (fst x),S (snd x))) l).
        rewrite Heqp.
        rewrite Heqi.
        replace lb with (incr_all (downshift lb 0) 1)
          by (apply shift_downshift; apply all_distinct_right with (@nil nat);
              apply andb_prop in Hperm as [_ Had]; rewrite<- Heqi; now rewrite<- Heqp).
        rewrite Heql.
        simpl; replace (n - 0) with n by lia.
        rewrite incr_all_compo_nc_transpo... }
    destruct n0.
    { rewrite Heqp in Hperm.
      rewrite Heqi in Hperm.
      simpl in Hperm.
      apply andb_prop in Hperm as [_ Had].
      simpl in Had.
      rewrite In_nat_bool_app in Had.
      apply andb_prop in Had as [H _].
      apply negb_true_iff in H.
      apply orb_false_iff in H as [_ H].
      inversion H. }
    simpl in Heqp.
    destruct (IHn (downshift (la ++ (S n0) :: lb) 0)) as [l Heql].
    + apply Nat.succ_inj.
      rewrite downshift_length.
      * rewrite Heqn, Heqp.
        simpl; rewrite 2 length_app...
      * rewrite Heqp, Heqi in Hperm.
        apply andb_prop in Hperm as [_ Had].
        change (S n0 :: la ++ 0 :: lb) with ((S n0 :: la) ++ 0 :: lb) in Had.
        apply all_distinct_right in Had as Had1.
        apply all_distinct_left in Had.
        simpl in Had.
        rewrite In_nat_bool_app.
        apply orb_false_intro...
    + change (downshift (la ++ S n0 :: lb) 0) with (downshift (0 :: la ++ S n0 :: lb) 0).
      apply downshift_perm.
      replace (0 :: la ++ S n0 :: lb) with (app_nat_fun (nc_transpo (S n) 0 i) p).
      2:{ rewrite Heqp, Heqi.
          change (S n0 :: la ++ 0 :: lb) with (nil ++ S n0 :: la ++ 0 :: lb).
          rewrite app_nc_transpo...
          - rewrite Heqp in Heqn; length_lia.
          - length_lia. }
      apply compo_perm_is_perm...
      * apply nc_transpo_is_perm.
      * rewrite nc_transpo_length...
    + apply not_eq_sym.
      rewrite downshift_app, downshift_gt...
      apply app_cons_not_nil.
    + split with ((0, i) :: map (fun x => (S (fst x), S (snd x))) l).
      simpl.
      rewrite<- incr_all_compo_nc_transpo.
      replace (0 :: incr_all (compo_nc_transpo n l) 1) with (nil ++ 0 :: la ++ S n0 :: lb).
      2:{ replace (incr_all (compo_nc_transpo n l) 1) with (la ++ S n0 :: lb)...
          replace la with (incr_all (downshift la 0) 1).
          2:{ apply shift_downshift.
              apply all_distinct_left with lb.
              rewrite Heqp in Hperm.
              rewrite Heqi in Hperm.
              apply andb_prop in Hperm as [_ Had].
              apply andb_prop in Had as [_ Had]... }
          replace lb with (incr_all (downshift lb 0) 1).
          2:{ apply shift_downshift.
              apply all_distinct_right with la.
              rewrite Heqp in Hperm.
              rewrite Heqi in Hperm.
              apply andb_prop in Hperm as [_ Had].
              apply andb_prop in Had as [_ Had]... }
          change (S n0 :: shift (downshift lb 0) 0 1) with (shift (n0 :: downshift lb 0) 0 1).
          rewrite <- shift_app.
          rewrite downshift_app in Heql.
          rewrite downshift_gt in Heql...
          simpl in Heql.
          rewrite Heql.
          now replace (n - 0) with n by lia. }
      rewrite app_nc_transpo...
      * rewrite Heqp; rewrite Heqi...
      * rewrite Heqp in Heqn; length_lia.
      * simpl in *; rewrite Hlenp...
Qed.

Lemma p_decomp_nc_transpo : forall n (p : perm_of (S n)),
  {l & p = p_compo_nc_transpo n l}.
Proof.
intros n [p Hp Hlen]; destruct (decomp_perm_nc_transpo p) as [l Heq]; [ assumption | | ].
- destruct p; inversion Hlen; intros Heq'; inversion Heq'.
- rewrite Hlen in Heq; simpl in Heq; replace (n - 0) with n in Heq by lia.
  exists l.
  unfold p_compo_nc_transpo.
  apply eq_sigT2_uncurried; simpl.
  exists Heq; [ apply (Eqdep_dec.UIP_dec bool_dec) | apply (Eqdep_dec.UIP_dec Nat.eq_dec) ].
Qed.

Lemma decomp_perm_transpo : forall p, is_perm p = true -> p <> nil ->
  {l & p = compo_transpo (length p - 1) l}.
Proof.
  intros p Hperm Hnnil.
  destruct (decomp_perm_nc_transpo p Hperm Hnnil) as [l Heqp].
  remember (length p); rewrite Heqp.
  destruct n.
  { destruct p; try now (exfalso; apply Hnnil); try now inversion Heqn. }
  clear; simpl; rewrite Nat.sub_0_r.
  induction l.
  - now split with nil.
  - destruct a; simpl.
    destruct (decomp_nc_transpo n n0 n1) as [l_nc Heq]; rewrite Heq.
    destruct IHl as [l0 Heql0]; rewrite Heql0.
    split with (l_nc ++ l0).
    symmetry; apply app_compo_transpo.
Qed.

Lemma p_decomp_transpo : forall n (p : perm_of (S n)),
  {l & p = p_compo_transpo n l}.
Proof.
intros n [p Hp Hlen]; destruct (decomp_perm_transpo p) as [l Heq]; [ assumption | | ].
- destruct p; inversion Hlen; intros Heq'; inversion Heq'.
- rewrite Hlen in Heq; simpl in Heq; replace (n - 0) with n in Heq by lia.
  exists l.
  unfold p_compo_nc_transpo.
  apply eq_sigT2_uncurried; simpl.
  exists Heq; [ apply (Eqdep_dec.UIP_dec bool_dec) | apply (Eqdep_dec.UIP_dec Nat.eq_dec) ].
Qed.

Lemma perm_inv : forall p, is_perm p = true ->
  { p_inv : _ & prod (app_nat_fun p_inv p = Id (length p)) (app_nat_fun p p_inv = Id (length p))
              & prod (is_perm p_inv = true) (length p = length p_inv) }.
Proof.
intros p Hperm.
destruct p; [ exists nil; split; split; reflexivity | ].
remember (n :: p) as q.
destruct (decomp_perm_transpo _ Hperm) as [l Hdec]; [ intros Heq; rewrite Heqq in Heq; inversion Heq | ].
assert (0 < length q) as Hlen by (rewrite Heqq; simpl; lia).
clear Heqq; revert q Hlen Hdec Hperm; induction l; intros q Hlen Hdec Hperm.
- exists (Id (length q)); split.
  + rewrite app_Id.
    rewrite Hdec; simpl.
    now rewrite length_seq.
  + rewrite app_nat_fun_Id_r; rewrite Hdec; simpl.
    * now rewrite length_seq.
    * apply all_lt_seq.
      now rewrite length_seq.
  + apply Id_is_perm.
  + now rewrite length_seq.
- specialize IHl with (compo_transpo (length q - 1) l).
  rewrite compo_transpo_length in IHl.
  replace (S (length q - 1)) with (length q) in IHl by lia.
  assert (is_perm (compo_transpo (length q - 1) l) = true) as IH by (apply compo_transpo_is_perm).
  apply (IHl Hlen eq_refl) in IH as [qinv [Happl Happr] [Hp Hl]].
  exists (app_nat_fun qinv (transpo (length q - 1) a)); split.
  + rewrite asso_app_nat_fun.
    rewrite Hdec at 2.
    simpl compo_transpo.
    rewrite <- (asso_app_nat_fun (transpo (length q - 1) a)).
    rewrite transpo_idem.
    replace (S (length q - 1)) with (length (compo_transpo (length q - 1) l))
      by (now rewrite compo_transpo_length).
    now rewrite app_Id.
  + rewrite <- asso_app_nat_fun.
    rewrite Hdec at 1.
    simpl compo_transpo.
    rewrite ? asso_app_nat_fun.
    rewrite <- (asso_app_nat_fun (compo_transpo (length q - 1) l)).
    rewrite Happr.
    replace (length q) with (length (transpo (length q - 1) a)) at 2 by (rewrite transpo_length; lia).
    rewrite app_Id, transpo_idem.
    f_equal; lia.
  + apply compo_perm_is_perm; [ assumption | | ].
    * apply transpo_is_perm.
    * length_lia.
  + rewrite app_nat_fun_length; [ assumption | ].
    rewrite transpo_length, <- Hl; lia.
Qed.

Lemma p_inv n (p : perm_of n) :
  { p_inv : perm_of n & projT1 (sigT_of_sigT2 p_inv) ∘ projT1 (sigT_of_sigT2 p) = Id n
                      & projT1 (sigT_of_sigT2 p) ∘ projT1 (sigT_of_sigT2 p_inv) = Id n }.
Proof.
destruct p as [p Hp Hlen].
destruct (perm_inv p) as [p_inv [Hinv1 Hinv2] [Hp2 Hlen2]]; [ assumption | simpl ].
rewrite Hlen in Hinv1, Hinv2, Hlen2; symmetry in Hlen2.
exists (existT2 _ _ p_inv Hp2 Hlen2); assumption.
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
    change nil with (Id (length (@nil A))) at 1; apply Hid... }
  destruct (decomp_perm_transpo (n :: f)) as [lt Heq]; [ | intros H; inversion H | ]...
  rewrite Hlen in Heq.
  rewrite Heq.
  assert (l <> nil) as Hnnil by (intros H; destruct l; try now inversion Hlen; try now inversion H).
  clear Hlen Heq Hperm f; revert l Hnnil P Hid Htranspo Htrans ;
    induction lt; intros l0 Hnnil P Hid Htranspo Htrans.
  - destruct l0; try now (exfalso; apply Hnnil).
    unfold compo_transpo.
    replace (S (length (a :: l0) - 1)) with (length (a :: l0)) by length_lia.
    apply Hid.
  - simpl; apply Htrans.
    + apply compo_transpo_is_perm.
    + apply transpo_is_perm.
    + rewrite compo_transpo_length.
      destruct l0; [ now exfalso; apply Hnnil | length_lia ].
    + rewrite transpo_length, compo_transpo_length...
    + apply IHlt...
    + replace (length l0 - 1) with (length (app_nat_fun (compo_transpo (length l0 - 1) lt) l0) - 1) at 1
        by (now rewrite app_nat_fun_length_cons; [ rewrite compo_transpo_length; length_lia | ]).
      apply Htranspo...
      intros H.
      assert (length (app_nat_fun (compo_transpo (length l0 - 1) lt) l0) = 0)
        by (now change 0 with (length (@nil A)) at 2; rewrite H).
      rewrite app_nat_fun_length_cons in H0...
      rewrite compo_transpo_length in H0; length_lia.
Qed.

(* UIP, eq_dec, ... *)
Lemma perm_eq_as_list : forall (p1 p2 : perm), projT1 p1 = projT1 p2 -> p1 = p2.
Proof. intros [l1 H1] [l2 H2]; simpl; intros Heq; subst; f_equal; apply (Eqdep_dec.UIP_dec bool_dec). Qed.

Lemma perm_eq_dec : forall (p1 p2 : perm), {p1 = p2} + {p1 <> p2}.
Proof.
  intros [p1 Hperm1] [p2 Hperm2].
  destruct (list_nat_eq_dec p1 p2).
  - left; subst; replace Hperm1 with Hperm2; try reflexivity.
    apply (Eqdep_dec.UIP_dec bool_dec).
  - right; intros H; inversion H; now apply n.
Qed.

Lemma UIP_perm : forall (p1 p2 : perm) (Heq1 Heq2 : p1 = p2), Heq1 = Heq2.
Proof. intros; apply Eqdep_dec.UIP_dec, perm_eq_dec. Qed.

Definition perm_eqb (p1 p2 : perm) :=
  match p1, p2 with
  | existT _ p1 _, existT _ p2 _ => list_nat_eqb p1 p2
  end.

Lemma perm_eqb_eq : forall p1 p2, perm_eqb p1 p2 = true <-> p1 = p2.
Proof.
  intros [p1 Hperm1] [p2 Hperm2]; split; intros Heq.
  - simpl in Heq; apply list_nat_eqb_eq in Heq; subst; replace Hperm1 with Hperm2; try reflexivity.
    apply (Eqdep_dec.UIP_dec bool_dec).
  - simpl; inversion Heq; now apply list_nat_eqb_eq.
Qed.

Lemma list_nat_eqb_neq : forall p1 p2, perm_eqb p1 p2 = false <-> p1 <> p2.
Proof.
  intros p1 p2.
  case_eq (perm_eqb p1 p2); intros H; split.
  - intros H'; inversion H'.
  - intros Hneq; exfalso; apply Hneq; now apply perm_eqb_eq.
  - intros _ Heq; replace (perm_eqb p1 p2) with true in H by (symmetry; now apply perm_eqb_eq); inversion H.
  - trivial.
Qed.
