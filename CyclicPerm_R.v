Require Import CMorphisms.
Require Import Lia.
Require Import PeanoNat.

Require Import List_Type_more.

Require Import List_more2.
Require Import List_nat.
Require Import Fun_nat.
Require Import Perm.
Require Import Perm_R_more.
Require Import misc.

(** Definition *)

Definition cond_cyclicPerm l := {' (n , m) : _ & l = cfun (S n) (S m) } + { l = Id (length l) }.

Definition CyclicPerm_R {A} (l1 l2 : list A) :=
  { f : _ & cond_cyclicPerm f & prod (length f = length l1) (l2 = app_nat_fun f l1) }.

Lemma decomp_CyclicPerm_R {A} : forall (l1 l2 : list A),
  CyclicPerm_R l1 l2 ->
    {' (la , lb) : _ & la ++ lb = l1 & lb ++ la = l2 }.
Proof with try reflexivity.
  intros l1 l2 [f cp [Hlen Heq]].
  destruct cp.
  - destruct s as [[n m] Heqf].
    symmetry in Heqf; destruct Heqf.
    split with (app_nat_fun (Id (S n)) l1, app_nat_fun (incr_all (Id (S m)) (S n)) l1).
    + rewrite <- app_nat_fun_app.
      rewrite incr_all_seq.
      rewrite <- seq_app.
      simpl in Hlen.
      rewrite app_length in Hlen; simpl in Hlen; rewrite 2 seq_length in Hlen.
      replace (S n + S m) with (length l1) by lia.
      rewrite app_Id...
    + rewrite Heq.
      unfold cfun.
      rewrite app_nat_fun_app...
      rewrite incr_all_seq...
  - rewrite e in Heq.
    rewrite Hlen in Heq.
    rewrite app_Id in Heq.
    subst.
    split with (l1 , nil)...
    apply app_nil_r.
Qed.

Lemma CyclicPerm_R_commu {A} : forall (l1 l2 : list A),
  CyclicPerm_R (l1 ++ l2) (l2 ++ l1).
Proof with try reflexivity.
  intros l1 l2.
  destruct l1 ; [ | destruct l2].
  - split with (Id (length l2)); repeat split.
    + right; rewrite seq_length...
    + rewrite seq_length...
    + rewrite app_Id, app_nil_r...
  - split with (Id (length (a :: l1))); repeat split.
    + right; rewrite seq_length...
    + rewrite seq_length, app_nil_r...
    + rewrite app_nil_r, app_Id...
  - split with (cfun (length (a :: l1)) (length (a0 :: l2))); repeat split.
    + left; split with (length l1, length l2)...
    + length_lia.
    + rewrite app_cfun_eq...
Qed.

Instance CyclicPerm_Perm_R {A} : Proper (CyclicPerm_R ==> (@Perm_R A)) (fun a => a).
Proof.
intros l1 l2 [cp [[[n m] Heqcp] | Heqcp] [Hlen Heq]].
- symmetry in Heqcp; destruct Heqcp.
  split with (cfun (S n) (S m)); repeat split; try assumption.
  apply cfun_is_perm.
- simpl in *.
  rewrite Heqcp in Heq.
  rewrite Hlen in Heq.
  rewrite app_Id in Heq.
  now subst.
Qed.

Instance CyclicPerm_R_refl {A} : Reflexive (@CyclicPerm_R A).
Proof.
  intros l.
  split with (Id (length l)); repeat split.
  - now right; rewrite seq_length.
  - length_lia.
  - symmetry; apply app_Id.
Defined.

Instance CyclicPerm_R_sym {A} : Symmetric (@CyclicPerm_R A).
Proof with try reflexivity.
  intros l1 l2 [f [((n & m) & Heq) | Heq] [Hlen Heqf]].
  simpl in *; subst.
  - split with (cfun (S m) (S n)); repeat split.
    + left; split with (m, n)...
    + destruct l1.
      * destruct n; destruct m; try now inversion Hlen...
      * unfold app_nat_fun; unfold app_nat_fun_dflt.
        rewrite map_length; rewrite 2 cfun_length; lia.
    + rewrite<- asso_app_nat_fun.
      rewrite cfun_inv.
      replace (S n + S m) with (length l1).
      2:{ rewrite<- Hlen.
          unfold cfun.
          rewrite app_length; rewrite 2 seq_length; lia. }
      rewrite app_Id...
  - rewrite Hlen in Heq.
    split with (Id (length l2)); repeat split.
    + right.
      rewrite seq_length...
    + length_lia.
    + rewrite app_Id...
      rewrite Heqf, Heq.
      symmetry; apply app_Id.
Defined.

Instance CyclicPerm_R_trans {A} : Transitive (@CyclicPerm_R A).
Proof.
  intros l1 l2 l3 HC1 HC2.
  apply decomp_CyclicPerm_R in HC1 as [[la lb] Heq1 Heq2].
  apply decomp_CyclicPerm_R in HC2 as [[la' lb'] Heq3 Heq4].
  rewrite<- Heq2 in Heq3.
  symmetry in Heq3.
  apply dichot_Type_app in Heq3.
  destruct Heq3 as [[l2' [Hl1 Hl2]] | [l4' [Hr1 Hr2]]] ; subst.
  - rewrite <- app_assoc.
    rewrite (app_assoc lb').
    eapply CyclicPerm_R_commu.
  - rewrite <- app_assoc.
    rewrite app_assoc.
    eapply CyclicPerm_R_commu.
Defined.

Instance CyclicPerm_R_equiv {A} : Equivalence (@CyclicPerm_R A).
Proof.
split.
- apply CyclicPerm_R_refl.
- apply CyclicPerm_R_sym.
- apply CyclicPerm_R_trans.
Qed.

Lemma CyclicPerm_R_app {A} : forall l1 l2 l3 : list A,
  CyclicPerm_R (l1 ++ l2) l3 -> CyclicPerm_R (l2 ++ l1) l3.
Proof.
intros l1 l2 l3 HC.
apply (CyclicPerm_R_trans _ (l1 ++ l2)) ; try assumption.
eapply CyclicPerm_R_commu.
Defined.

Lemma CyclicPerm_R_app_rot {A} : forall (l1 : list A) l2 l3,
   CyclicPerm_R (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
Proof.
intros l1 l2 l3.
rewrite (app_assoc l2).
apply CyclicPerm_R_commu.
Defined.

Lemma CyclicPerm_R_last {A} : forall (a : A) l,
  CyclicPerm_R (a :: l) (l ++ a :: nil).
Proof.
intros.
rewrite <- (app_nil_l l).
rewrite app_comm_cons.
apply CyclicPerm_R_commu.
Defined.

Lemma CyclicPerm_R_swap {A} : forall a b : A,
  CyclicPerm_R (a :: b :: nil) (b :: a :: nil).
Proof.
intros.
change (a :: b :: nil) with ((a :: nil) ++ (b :: nil)).
change (b :: a :: nil) with ((b :: nil) ++ (a :: nil)).
apply CyclicPerm_R_commu.
Defined.

Lemma CyclicPerm_R_cons {A} : forall l1 (a : A) l2,
  CyclicPerm_R (l1 ++ (a :: nil)) l2 -> CyclicPerm_R (a :: l1) l2.
Proof.
intros l1 a l2 HC.
apply (CyclicPerm_R_app l1 (a :: nil)) ; assumption.
Defined.

Lemma CyclicPerm_R_morph_cons {A} : forall P : list A -> Prop,
  (forall a l, P (l ++ a :: nil) -> P (a :: l)) ->
  Proper (CyclicPerm_R ==> Basics.impl) P.
Proof with try eassumption.
assert (forall P : list A -> Prop,
         (forall a l, P (l ++ a :: nil) -> P (a :: l)) ->
         forall l1 l2, CyclicPerm_R l1 l2 -> P l1 -> P l2)
  as Himp.
{
  intros P HP l1 l2 HC.
  apply decomp_CyclicPerm_R in HC as [[l0 l3] Heql1 Heql2].
  subst.
  revert l0 ; induction l3 using rev_ind ; intros l0 HPl.
  - rewrite app_nil_r in HPl...
  - rewrite app_assoc in HPl.
    apply HP in HPl.
    rewrite <- app_assoc.
    rewrite <- app_comm_cons.
    rewrite app_nil_l...
    apply IHl3...
}
intros P HP l1 l2 HC H.
eapply Himp...
Qed.

Lemma CyclicPerm_R_nil {A} : forall l : list A,
  CyclicPerm_R nil l -> l = nil.
Proof.
  intros.
  apply Perm_R_nil.
  apply CyclicPerm_Perm_R.
  assumption.
Qed.

Lemma CyclicPerm_R_nil_cons {A} : forall l (a : A),
  CyclicPerm_R nil (a :: l) -> False.
Proof.
  intros l a HC.
  apply CyclicPerm_R_nil in HC.
  inversion HC.
Qed.

Lemma CyclicPerm_R_one {A} : forall a b : A,
    CyclicPerm_R (a :: nil) (b :: nil) -> a = b.
Proof.
  intros.
  apply Perm_R_length_1.
  apply CyclicPerm_Perm_R.
  assumption.
Qed.

Lemma CyclicPerm_R_two {A} : forall a1 a2 b1 b2 : A,
  CyclicPerm_R (a1 :: a2 :: nil) (b1 :: b2 :: nil) ->
    { a1 = b1 /\ a2 = b2 } +  { a1 = b2 /\ a2 = b1 }.
Proof.
  intros.
  apply Perm_R_length_2.
  apply CyclicPerm_Perm_R.
  assumption.
Qed.

Lemma CyclicPerm_R_one_inv {A} : forall l (a : A),
  CyclicPerm_R (a :: nil) l -> l = a :: nil.
Proof.
  intros.
  apply Perm_R_length_1_inv.
  apply CyclicPerm_Perm_R.
  assumption.
Qed.

Lemma CyclicPerm_R_two_inv {A} : forall (a : A) b l,
  CyclicPerm_R (a :: b :: nil) l ->
  { l = a :: b :: nil } + { l = b :: a :: nil }.
Proof.
  intros.
  apply Perm_R_length_2_inv.
  apply CyclicPerm_Perm_R.
  assumption.
Qed.

Lemma CyclicPerm_R_vs_elt_inv {A} : forall (a : A) l l1 l2,
  CyclicPerm_R l (l1 ++ a :: l2) ->
    { pl | l2 ++ l1 = snd pl ++ fst pl & l = fst pl ++ a :: snd pl }.
Proof.
  intros a l l1 l2 HC.
  apply decomp_CyclicPerm_R in HC as [[l0 l3] H1 H2]; subst.
  symmetry in H2.
  dichot_Type_elt_app_exec H2 ; subst.
  - exists (l0 ++ l1, l) ; simpl ; now rewrite <- app_assoc.
  - exists (l4, l2 ++ l3) ; simpl ; now rewrite <- app_assoc.
Qed.

Lemma CyclicPerm_R_vs_cons_inv {A} : forall (a : A) l l1,
  CyclicPerm_R l (a :: l1) ->
    { pl | l1 = snd pl ++ fst pl & l = fst pl ++ a :: snd pl }.
Proof.
  intros a l l1 HC.
  rewrite <- (app_nil_l (a::_)) in HC.
  apply CyclicPerm_R_vs_elt_inv in HC.
  destruct HC as [(l' & l'') H1 H2].
  rewrite app_nil_r in H1 ; subst.
  exists (l', l'') ; split ; reflexivity.
Qed.

Lemma CyclicPerm_R_app_app_inv {A} : forall l1 l2 l3 l4 : list A,
  CyclicPerm_R (l1 ++ l2) (l3 ++ l4) ->
     { ql : _ & prod (prod 
        (CyclicPerm_R l1 (fst (fst ql) ++ fst (snd ql)))
        (CyclicPerm_R l2 (snd (fst ql) ++ snd (snd ql))))
        (prod
        (CyclicPerm_R l3 (fst (fst ql) ++ snd (fst ql)))
        (CyclicPerm_R l4 (fst (snd ql) ++ snd (snd ql)))) }
   + { pl : _ & prod (prod
        (CyclicPerm_R l1 (l4 ++ fst pl))
        (CyclicPerm_R l3 (l2 ++ snd pl)))
        (CyclicPerm_R (fst pl) (snd pl)) }
   + { pl : _ & prod (prod
        (CyclicPerm_R l2 (l4 ++ fst pl))
        (CyclicPerm_R l3 (l1 ++ snd pl)))
        (CyclicPerm_R (fst pl) (snd pl)) }
   + { pl : _ & prod (prod
        (CyclicPerm_R l1 (l3 ++ fst pl))
        (CyclicPerm_R l4 (l2 ++ snd pl)))
        (CyclicPerm_R (fst pl) (snd pl)) }
   + { pl : _ & prod (prod
        (CyclicPerm_R l2 (l3 ++ fst pl))
        (CyclicPerm_R l4 (l1 ++ snd pl)))
        (CyclicPerm_R (fst pl) (snd pl)) }.
Proof with try assumption.
intros l1 l2 l3 l4 HC.
apply decomp_CyclicPerm_R in HC as [[lx ly] Hx Hy].
dichot_Type_app_exec Hx ; dichot_Type_app_exec Hy ; subst.
- left ; left ; left ; right.
  exists (l ++ l0 , l0 ++ l).
  simpl ; split ; [ split | ] ; 
    try (rewrite <- ? app_assoc ; apply CyclicPerm_R_app_rot).
  apply CyclicPerm_R_commu.
- dichot_Type_app_exec Hy0 ; subst.
  + left ; left ; left ; left.
    exists (l, l0, (lx, l5)).
    simpl ; split ; [ split | split ] ; try apply CyclicPerm_R_commu...
    * apply CyclicPerm_R_refl.
    * apply CyclicPerm_R_refl.
  + left ; right.
    exists (l1 ++ lx , lx ++ l1).
    split ; [ split | ] ; 
      try (rewrite <- ? app_assoc ; apply CyclicPerm_R_app_rot)...
    apply CyclicPerm_R_commu.
- dichot_Type_app_exec Hy1 ; subst.
  + left ; left ; right.
    exists (ly ++ l2, l2 ++ ly).
    split ; [ split | ] ; 
      try (rewrite <- ? app_assoc ; apply CyclicPerm_R_app_rot)...
    apply CyclicPerm_R_commu.
  + left ; left ; left ; left.
    exists (l, ly, (l3, l0)).
    simpl ; split ; [ split | split ] ; try apply CyclicPerm_R_commu...
    * apply CyclicPerm_R_refl.
    * apply CyclicPerm_R_refl.
- right.
  exists (l5 ++ l0, l0 ++ l5).
  split ; [ split | ] ; 
    try (rewrite <- ? app_assoc ; apply CyclicPerm_R_app_rot)...
  apply CyclicPerm_R_commu.
Defined.

(** [rev], [in], [map], [Forall], [Exists], etc. *)
Instance CyclicPerm_R_rev {A} : Proper (CyclicPerm_R ==> CyclicPerm_R) (@rev A).
Proof.
intro l ; induction l ; intros l' HC.
- apply CyclicPerm_R_nil in HC ; subst ; apply CyclicPerm_R_refl.
- apply CyclicPerm_R_sym in HC.
  apply CyclicPerm_R_vs_cons_inv in HC.
  destruct HC as [(l1 & l2) Heq1 Heq2] ; subst.
  simpl ; rewrite ? rev_app_distr ; simpl.
  rewrite <- app_assoc.
  apply CyclicPerm_R_commu.
Defined.

Instance CyclicPerm_R_in {A} (a : A) : Proper (CyclicPerm_R ==> Basics.impl) (In a).
Proof with try eassumption.
intros l l' HC Hin.
eapply Perm_R_in...
apply CyclicPerm_Perm_R...
Qed.

Instance CyclicPerm_R_map {A B} (f : A -> B) :
   Proper (CyclicPerm_R ==> CyclicPerm_R) (map f).
Proof.
intros l l' HC.
apply decomp_CyclicPerm_R in HC as [[lx ly] Hx Hy]; subst ; rewrite ? map_app.
apply CyclicPerm_R_commu.
Defined.

Lemma CyclicPerm_R_map_inv {A B} : forall(f : A -> B) l1 l2,
  CyclicPerm_R l1 (map f l2) ->
    { l : _ & l1 = map f l & (CyclicPerm_R l2 l) }.
Proof with try assumption.
induction l1 ; intros l2 HP.
- exists nil ; try reflexivity.
  simpl ; destruct l2...
  + apply CyclicPerm_R_refl.
  + apply CyclicPerm_R_nil in HP.
    inversion HP.
- apply CyclicPerm_R_sym in HP.
  assert (Heq := HP).
  apply CyclicPerm_R_vs_cons_inv in Heq.
  destruct Heq as [(l3 & l4) Heq1 Heq2].
  simpl in Heq1 ; simpl in Heq2 ; symmetry in Heq2.
  decomp_map_Type Heq2 ; subst ; simpl.
  exists (x :: l6 ++ l0).
  + simpl ; rewrite ? map_app ; reflexivity.
  + apply (CyclicPerm_R_commu l0).
Defined.

Instance CyclicPerm_R_Forall {A} (P : A -> Prop) :
  Proper (CyclicPerm_R ==> Basics.impl) (Forall P).
Proof with try eassumption.
intros l1 l2 HC HF.
eapply Perm_R_Forall...
apply CyclicPerm_Perm_R...
Qed.

Instance CyclicPerm_R_Exists {A} (P : A -> Prop) :
  Proper (CyclicPerm_R ==> Basics.impl) (Exists P).
Proof with try eassumption.
intros l1 l2 HC HE.
eapply Perm_R_Exists...
apply CyclicPerm_Perm_R...
Qed.

Instance CyclicPerm_R_Forall_Type {A} (P : A -> Type) :
  Proper (CyclicPerm_R ==> Basics.arrow) (Forall_Type P).
Proof with try eassumption.
intros l1 l2 HC HF.
eapply Perm_R_Forall_Type...
apply CyclicPerm_Perm_R...
Qed.

Instance CyclicPerm_R_Exists_Type {A} (P : A -> Type) :
  Proper (CyclicPerm_R ==> Basics.arrow) (Exists_Type P).
Proof with try eassumption.
intros l1 l2 HC HE.
eapply Perm_R_Exists_Type...
apply CyclicPerm_Perm_R...
Qed.

Lemma CyclicPerm_R_Forall2 {A B} (P : A -> B -> Type) :
  forall l1 l1' l2, CyclicPerm_R l1 l1' -> Forall2_Type P l1 l2 ->
    { l2' : _ & CyclicPerm_R l2 l2' & Forall2_Type P l1' l2' }.
Proof.
intros l1 l1' l2 HP.
revert l2.
apply decomp_CyclicPerm_R in HP as [[lx ly] Hx Hy]; subst.
intros l2' HF ; inversion HF ; subst.
- exists nil ; auto.
  + reflexivity.
  + symmetry in H0 ; apply app_eq_nil in H0 as [Heq1 Heq2] ; subst.
    constructor.
- destruct lx ; inversion H0 ; subst.
  + rewrite app_nil_l in H0 ; subst.
    exists (y :: l').
    * reflexivity.
    * rewrite app_nil_l in HF ; simpl ; rewrite app_nil_r ; assumption.
  + apply Forall2_Type_app_inv_l in X0 as ([(la & lb) H1 H2] & Heq).
    simpl in Heq ; rewrite Heq.
    exists (lb ++ y :: la).
    * rewrite app_comm_cons ; apply CyclicPerm_R_commu.
    * apply Forall2_Type_app ; auto.
      constructor ; auto.
Defined.

Lemma CyclicPerm_R_image {A B} : forall (f : A -> B) a l l',
  CyclicPerm_R (a :: l) (map f l') -> { a' | a = f a' }.
Proof.
intros f a l l' HP.
eapply Perm_R_image.
apply CyclicPerm_Perm_R ; eassumption.
Qed.

Definition app_cperm_nat {A} n (l : list A) :=
  skipn n l ++ firstn n l.

Lemma app_cperm_cfun {A} : forall n (l : list A),
    n <= length l ->
    app_cperm_nat n l = app_nat_fun (cfun n (length l - n)) l.
Proof with try reflexivity.
  intros n l Hle.
  rewrite<- (firstn_skipn n l) at 3.
  rewrite<- (firstn_length_le l) at 2; try assumption.
  replace (length l - n) with (length (skipn n l)).
  2:{ rewrite<- (firstn_skipn n l) at 2.
      rewrite app_length.
      rewrite firstn_length_le; try assumption.
      lia. }
  rewrite app_cfun_eq...
Qed.

Lemma cond_cyclicPerm_to_app_cperm : forall p,
    cond_cyclicPerm p ->
    { n & forall {A} (l : list A), length p = length l -> app_nat_fun p l = app_cperm_nat n l}.
Proof with try reflexivity.
  intros p Hperm.
  destruct Hperm as [[[n m] Heq]| Heq].
  - split with (S n).
    intros A l Hlen.
    rewrite Heq in Hlen |- *.
    rewrite cfun_length in Hlen.
    replace (S m) with (length l - S n) by lia.
    rewrite app_cperm_cfun...
    lia.
  - split with (length p).
    intros A l Hlen.
    rewrite Heq at 1; rewrite Hlen.
    rewrite app_Id.
    unfold app_cperm_nat.
    rewrite skipn_all2 by lia.
    rewrite firstn_all2 by lia...
Qed.

Lemma app_cperm_to_cond_cyclicPerm : forall n len,
  {p : _ & cond_cyclicPerm p
         & prod (length p = len)
                (forall {A} (l : list A), length p = length l -> app_nat_fun p l = app_cperm_nat n l)}.
Proof with try reflexivity.
  intros n len.
  destruct n; [ | case_eq ((S n) <? len); intros H ; [apply Nat.ltb_lt in H | apply Nat.ltb_nlt in H] ].
  - split with (Id len); [ | split].
    + right; rewrite seq_length...
    + apply seq_length.
    + intros A l Hlen.
      rewrite seq_length in Hlen.
      rewrite Hlen.
      rewrite app_Id.
      unfold app_cperm_nat; simpl.
      rewrite app_nil_r...
  - split with (cfun (S n) (S (pred (pred len) - n))); [ | split ].
    + left; split with (n , pred (pred len) - n)...
    + rewrite cfun_length.
      lia.
    + intros A l Hlen.
      rewrite cfun_length in Hlen.
      replace (S (Init.Nat.pred (Init.Nat.pred len) - n)) with (len - S n) by lia.
      unfold app_cperm_nat.
      rewrite <- (firstn_skipn (S n) l) at 1.
      rewrite<- (firstn_length_le l) at 1 by lia.
      replace (len - S n) with (length (skipn (S n) l)); [apply app_cfun_eq | ].
      rewrite skipn_length; lia.
  - split with (Id len);  [ | split].
    + right; rewrite seq_length...
    + apply seq_length.
    + intros A l Hlen.
      rewrite seq_length in Hlen; rewrite Hlen.
      rewrite app_Id.
      unfold app_cperm_nat.
      rewrite skipn_all2 by lia.
      rewrite firstn_all2 by lia...
Qed.

