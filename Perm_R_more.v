Require Import Plus.
Require Import CMorphisms.
Require Import PeanoNat.

Require Import Injective.
Require Import List_more.
Require Export Perm_R.
Require Import List_Type_more.
Require Import List_more2.
Require Import List_nat.
Require Import Perm.
Require Import Fun_nat.
Require Import misc.


Instance Perm_R_refl' {A} : Proper (Logic.eq ==> @Perm_R A) (fun a => a).
Proof.
intros x y Heq.
rewrite Heq.
reflexivity.
Qed.

Lemma Perm_R_morph_transp {A} : forall P : list A -> Prop,
  (forall a b l1 l2, P (l1 ++ a :: b :: l2) -> P (l1 ++ b :: a :: l2)) ->
    Proper ((@Perm_R A) ==> iff) P.
Proof with try eassumption.
  assert (forall P : list A -> Prop,
             (forall a b l1 l2, P (l1 ++ a :: b :: l2) ->
                                P (l1 ++ b :: a :: l2)) ->
             forall l1 l2, Perm_R l1 l2 ->
                           forall l0, P (l0 ++ l1) -> P (l0 ++ l2))
    as Himp.
  { intros P HP l1 l2 H.
    refine (Perm_R_rect_transpo (fun l1' l2' => forall l0, P (l0 ++ l1') -> P (l0 ++ l2')) _ _ _ _ H); intros...
    - rewrite <- (app_nil_l l').
      rewrite app_comm_cons.
      rewrite app_assoc.
      apply H0.
      list_simpl...
    - apply HP...
    - apply H1.
      apply H0... }
  intros P HP l1 l2 H.
  split ; intro H'.
  - rewrite <- (app_nil_l l2).
    rewrite <- (app_nil_l l1) in H'.
    eapply Himp...
  - symmetry in H.
    rewrite <- (app_nil_l l1).
    rewrite <- (app_nil_l l2) in H'.
    eapply Himp...
Qed.

Lemma Perm_R_elt {A} : forall (a : A) l1 l2 l1' l2',
  Perm_R (l1 ++ l2) (l1' ++ l2') ->
    Perm_R (l1 ++ a :: l2) (l1' ++ a :: l2').
Proof.
  intros a l1 l2 l1' l2' HP.
  eapply Perm_R_trans.
  - apply Perm_R_sym.
    apply Perm_R_middle.
  - apply Perm_R_cons_app.
    assumption.
Defined.

Lemma Perm_R_vs_elt_inv {A} : forall (a : A) l l1 l2,
  Perm_R l (l1 ++ a :: l2) -> { pl | l = fst pl ++ a :: snd pl}.
Proof with try assumption ; try reflexivity.
  intros a l l1 l2 HP.
  remember (l1 ++ a :: l2) as l0.
  revert l1 l2 Heql0.
  rect_transpo (fun la lb => forall l1 l2 : list A,
                    lb = l1 ++ a :: l2 -> {pl : list A * list A | la = fst pl ++ a :: snd pl}) HP; intros l1 l2 Heql.
  - destruct l1 ; inversion Heql.
  - destruct l1 ; inversion Heql.
    + exists (@nil A, la)...
    + apply IHHperm1 in H1.
      destruct H1 as (pl & Heq) ; subst.
      exists (a0 :: fst pl, snd pl)...
  - destruct l1 ; inversion Heql ; subst.
    + exists (y :: nil, la)...
    + destruct l1 ; inversion H1 ; subst.
      * exists (@nil A, a0 :: l2)...
      * exists (a1 :: a0 :: l1, l2)...
  - destruct (IHHperm2 _ _ Heql) as (pl & Heq) ; subst.
    assert (Heq := IHHperm1 (fst pl) (snd pl) eq_refl).
    destruct Heq as (pl' & Heq) ; subst.
    exists pl'...
Qed.

Lemma Perm_R_vs_cons_inv {A} : forall (a : A) l l1,
  Perm_R l (a :: l1) -> {pl | l = fst pl ++ a :: snd pl}.
Proof.
intros a l l1 HP.
rewrite <- (app_nil_l (a :: l1)) in HP.
eapply Perm_R_vs_elt_inv ; eassumption.
Qed.

Lemma Perm_R_vs_2elts {A} : forall (s : A) t l1 l2 l3,
  Perm_R (l1 ++ s :: l2 ++ t :: l3) (s :: t :: l1 ++ l2 ++ l3).
Proof.
intros.
apply Perm_R_sym.
apply Perm_R_cons_app.
rewrite 2 app_assoc.
apply Perm_R_cons_app.
apply Perm_R_refl.
Defined.

Lemma Perm_R_vs_2elts_inv : forall A D (s : A) t G,
  Perm_R D (s :: t :: G) -> { tG |
    D = fst tG ++ s :: fst (snd tG) ++ t :: snd (snd tG)
 \/ D = fst tG ++ t :: fst (snd tG) ++ s :: snd (snd tG)}.
Proof.
intros A D s t G HP.
assert (HP' := HP).
apply Perm_R_vs_cons_inv in HP'.
destruct HP' as (pl & HP') ; subst.
apply Perm_R_sym in HP.
apply Perm_R_cons_app_inv in HP.
apply Perm_R_sym in HP.
apply Perm_R_vs_cons_inv in HP.
destruct HP as (pl' & HP).
symmetry in HP.
dichot_Type_elt_app_exec HP ; subst ;
rewrite <- ? app_assoc ;
rewrite <- ? app_comm_cons.
- exists (fst pl', (l, snd pl)).
  right.
  rewrite <- HP0.
  simpl.
  rewrite <- app_assoc.
  rewrite <- app_comm_cons.
  reflexivity.
- exists (fst pl, (l0, snd pl')).
  left.
  simpl.
  rewrite HP1.
  reflexivity.
Qed.

Lemma Perm_R_app_rot {A} : forall (l1 : list A) l2 l3,
  Perm_R (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
Proof.
intros l1 l2 l3.
rewrite (app_assoc l2).
apply Perm_R_app_comm.
Defined.

Lemma Perm_R_app_swap_app {A} : forall (l1 : list A) l2 l3,
  Perm_R (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
Proof.
intros.
repeat rewrite app_assoc.
apply Perm_R_app_tail.
apply Perm_R_app_comm.
Defined.

Lemma Perm_R_app_middle {A} : forall (l : list A) l1 l2 l3 l4,
  Perm_R (l1 ++ l2) (l3 ++ l4) ->
    Perm_R (l1 ++ l ++ l2) (l3 ++ l ++ l4).
Proof.
intros.
eapply Perm_R_trans.
apply Perm_R_app_swap_app.
eapply Perm_R_trans.
apply Perm_R_app_head.
- eassumption.
- apply Perm_R_app_swap_app.
Defined.

Lemma Perm_R_app_middle_inv {A} : forall (l : list A) l1 l2 l3 l4,
  Perm_R (l1 ++ l ++ l2) (l3 ++ l ++ l4) ->
    Perm_R (l1 ++ l2) (l3 ++ l4).
Proof.
  intros.
  apply Perm_R_app_inv_l with l.
  eapply Perm_R_trans.
  apply Perm_R_app_swap_app.
  eapply Perm_R_trans.
  - eassumption.
  - apply Perm_R_app_swap_app.
Defined.

Lemma Perm_R_app_app_inv {A} : forall (l1 l2 l3 l4 : list A),
  Perm_R (l1 ++ l2) (l3 ++ l4) -> { ql : _ & prod (prod
    (Perm_R l1 (fst (fst ql) ++ fst (snd ql)))
    (Perm_R l2 (snd (fst ql) ++ snd (snd ql)))) (prod
    (Perm_R l3 (fst (fst ql) ++ snd (fst ql)))
    (Perm_R l4 (fst (snd ql) ++ snd (snd ql)))) }.
Proof with try assumption.
induction l1 ; intros l2 l3 l4 HP.
- exists (@nil A, l3, (@nil A, l4)).
  split ; try split ; try split ; try apply Perm_R_refl...
- assert (Heq := HP).
  apply Perm_R_sym in Heq.
  apply Perm_R_vs_cons_inv in Heq.
  destruct Heq as [pl Heq].
  dichot_Type_elt_app_exec Heq ; subst.
  + rewrite <- ?app_comm_cons in HP.
    rewrite <- app_assoc in HP.
    rewrite <- app_comm_cons in HP.
    apply Perm_R_cons_app_inv in HP.
    rewrite app_assoc in HP.
    apply IHl1 in HP.
    destruct HP as (ql & (H1 & H2) & H3 & H4).
    exists (a :: fst (fst ql), snd (fst ql), (fst (snd ql), snd (snd ql))).
    simpl ; split ; try split ; try split...
    * apply Perm_R_skip...
    * apply Perm_R_sym.
      apply Perm_R_cons_app.
      apply Perm_R_sym...
  + rewrite <- ?app_comm_cons in HP.
    rewrite app_assoc in HP.
    apply Perm_R_cons_app_inv in HP.
    rewrite <- app_assoc in HP.
    apply IHl1 in HP.
    destruct HP as (ql & (H1 & H2) & H3 & H4).
    exists (fst (fst ql), snd (fst ql), (a :: fst (snd ql), snd (snd ql))).
    simpl ; split ; try split ; try split...
    * apply Perm_R_cons_app...
    * apply Perm_R_sym.
      apply Perm_R_cons_app.
      apply Perm_R_sym...
Defined.

Instance Perm_R_Forall {A} (P : A -> Prop) :
  Proper ((@Perm_R A) ==> Basics.impl) (Forall P).
Proof.
  intros l1 l2 H.
  apply Perm_R_to_Permutation_Type in H.
  apply Permutation_Type.Permutation_Type_Permutation in H.
  rewrite H ; reflexivity.
Qed.

Instance Perm_R_Exists {A} (P : A -> Prop) :
  Proper ((@Perm_R A) ==> Basics.impl) (Exists P).
Proof.
  intros l1 l2 H.
  apply Perm_R_to_Permutation_Type in H.
  apply Permutation_Type.Permutation_Type_Permutation in H.
  rewrite H ; reflexivity.
Qed.

Instance Perm_R_Forall_Type {A} (P : A -> Type) :
  Proper ((@Perm_R A) ==> Basics.arrow) (Forall_Type P).
Proof with try assumption.
  intros l1 l2 H.
  apply Perm_R_to_Permutation_Type in H.
  induction H ; intro H1...
  - inversion H1 ; subst.
    apply IHPermutation_Type in X0.
    constructor...
  - inversion H1.
    inversion X0.
    constructor...
    constructor...
  - apply IHPermutation_Type2.
    apply IHPermutation_Type1...
Qed.

Instance Perm_R_Exists_Type {A} (P : A -> Type) :
  Proper ((@Perm_R A) ==> Basics.arrow) (Exists_Type P).
Proof with try assumption.
intros l1 l2 H.
apply Perm_R_to_Permutation_Type in H.
induction H ; intro H1...
- inversion H1 ; subst.
  + apply Exists_Type_cons_hd...
  + apply IHPermutation_Type in X.
    apply Exists_Type_cons_tl...
- inversion H1 ; [ | inversion X ] ; subst.
  + apply Exists_Type_cons_tl.
    apply Exists_Type_cons_hd...
  + apply Exists_Type_cons_hd...
  + apply Exists_Type_cons_tl.
    apply Exists_Type_cons_tl...
- apply IHPermutation_Type2.
  apply IHPermutation_Type1...
Qed.

Lemma Perm_R_Forall2 {A B} (P : A -> B -> Type) :
  forall l1 l1' l2, Perm_R l1 l1' -> Forall2_Type P l1 l2 ->
    { l2' : _ & Perm_R l2 l2' & Forall2_Type P l1' l2' }.
Proof with try reflexivity; try assumption.
  intros l1 l1' l2 (p & (Hperm & Hlen & Heq)) H.
  assert (length l1 = length l2) as Hlen'.
  { clear - H.
    induction H...
    simpl; rewrite IHForall2_Type... }
  split with (app_nat_fun p l2).
  - split with p.
    rewrite Hlen.
    repeat split...
  - rewrite Heq.
    apply andb_prop in Hperm as (Hal & _).
    assert (Hal2 := Hal).
    rewrite Hlen in Hal, Hal2.
    rewrite Hlen' in Hal2.
    rename Hal into Hal1.
    clear - H Hal1 Hal2.
    induction p.
    + destruct l1; destruct l2; try now inversion H.
      apply Forall2_Type_nil.
    + simpl in Hal1, Hal2.
      apply andb_prop in Hal1 as (Hlt1 & Hal1).
      apply andb_prop in Hal2 as (Hlt2 & Hal2).
      specialize (IHp Hal1 Hal2).
      destruct l1; destruct l2; try now inversion IHp.
      app_nat_fun_unfold p l1 a a0.
      app_nat_fun_unfold p l2 a b.
      apply Forall2_Type_cons...
      remember (a0 :: l1) as l.
      remember (b :: l2) as l'.
      clear - H Hlt1 Hlt2.
      revert l l' Hlt1 Hlt2 H.
      induction a; intros l l' Hlt1 Hlt2 H; (destruct l; [ inversion Hlt1 | destruct l' ; [inversion Hlt2 | ]]).
      * inversion H...
      * simpl in Hlt1, Hlt2.
        apply IHa...
        inversion H...
Defined.

Lemma Perm_R_map_inv {A B} : forall(f : A -> B) l1 l2,
  Perm_R l1 (map f l2) -> { l : _ & l1 = map f l & (Perm_R l2 l) }.
Proof with try reflexivity; try assumption.
  intros f l1 l2 (p & (Hperm & Hlen & Heq)).
  simpl in Hlen.
  destruct (perm_inv _ Hperm) as (p_inv & ((Heq' & _) & Hperm_inv & Heq_len)).
  split with (app_nat_fun p_inv l2).
  - rewrite<- app_nat_fun_map.
    rewrite Heq.
    rewrite<- asso_app_nat_fun.
    rewrite Heq'.
    rewrite Hlen.
    rewrite app_Id...
  - split with p_inv.
    repeat split...
    rewrite<- Heq_len.
    rewrite<- map_length with _ _ f _.
    rewrite Heq.
    rewrite Hlen.
    destruct l1...
    unfold app_nat_fun; unfold app_nat_fun_dflt; rewrite map_length; rewrite Hlen...
Defined.

Lemma Perm_R_map_inv_inj {A B} : forall f : A -> B, injective f ->
  forall l1 l2, Perm_R (map f l1) (map f l2) -> Perm_R l1 l2.
Proof with try reflexivity; try assumption.
  intros f Hi l1 l2 (p & (Hperm & Hlen & Heq)).
  split with p.
  repeat split...
  - rewrite map_length in Hlen...
  - rewrite app_nat_fun_map in Heq.
    apply map_inj_local with f...
    intros x y _ _ Heq'.
    apply Hi...
Defined.

Lemma Perm_R_image {A B} : forall (f : A -> B) a l l',
  Perm_R (a :: l) (map f l') -> { a' | a = f a' }.
Proof.
intros f a l l' HP.
apply Perm_R_map_inv in HP.
destruct HP as [l'' Heq _].
destruct l'' ; inversion Heq.
eexists ; reflexivity.
Qed.

Lemma Perm_R_elt_map_inv {A B} : forall (f : A -> B) a l1 l2 l3 l4,
  Perm_R (l1 ++ a :: l2) (l3 ++ map f l4) ->
  (forall b, a <> f b) -> { pl | l3 = fst pl ++ a :: snd pl }.
Proof.
intros a l1 l2 l3 l4 f HP Hf.
apply Perm_R_sym in HP.
apply Perm_R_vs_elt_inv in HP.
destruct HP as ((l' & l'') & Heq).
dichot_Type_elt_app_exec Heq.
- subst.
  exists (l', l) ; reflexivity.
- exfalso.
  decomp_map_Type Heq1.
  apply Hf in Heq1.
  inversion Heq1.
Qed.

Instance Perm_R_flat_map {A B} f :
  Proper ((@Perm_R A) ==> (@Perm_R B)) (flat_map f).
Proof with try eassumption.
intros l1.
induction l1 ; intros l2 HP.
- destruct l2...
  + apply Perm_R_refl.
  + apply Perm_R_nil in HP.
    inversion HP.
- apply Perm_R_sym in HP.
  assert (Heq := HP).
  apply Perm_R_vs_cons_inv in Heq.
  destruct Heq as ((l' & l'') & Heq) ; subst.
  destruct l' ; apply Perm_R_sym in HP.
  + simpl in HP ; simpl ; apply Perm_R_app_head.
    apply IHl1.
    eapply Perm_R_cons_inv...
  + apply Perm_R_cons_app_inv in HP.
    apply IHl1 in HP.
    rewrite flat_map_app in HP ; simpl in HP.
    rewrite flat_map_app ; simpl.
    apply (Perm_R_app_head (f a)) in HP.
    apply (Perm_R_trans HP).
    rewrite ? app_assoc.
    apply Perm_R_app_tail.
    rewrite <- ? app_assoc.
    apply Perm_R_app_rot.
Defined.

Instance list_sum_perm_Type : Proper (@Perm_R nat ==> eq) list_sum.
Proof with try reflexivity.
intros l1 ; induction l1 ; intros l2 HP.
- apply Perm_R_nil in HP ; subst...
- assert (HP' := HP).
  apply Perm_R_sym in HP'.
  apply Perm_R_vs_cons_inv in HP'.
  destruct HP' as ((l3 & l4) & Heq) ; subst.
  apply Perm_R_cons_app_inv in HP.
  simpl ; erewrite IHl1 ; [ | apply HP ].
  rewrite 2 list_sum_app.
  simpl.
  rewrite 2 (plus_comm a).
  rewrite plus_assoc...
Qed.

