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

Definition cond_cyclicPerm l := {' (n, m) : _ & l = cfun (S n) (S m) } + { l = Id (length l) }.

Lemma Id_cond_cyclic : forall n, cond_cyclicPerm (Id n).
Proof. intros; right; now rewrite seq_length. Qed.

Lemma cfun_S_cond_cyclic : forall n m, cond_cyclicPerm (cfun (S n) (S m)).
Proof. intros; left; now split with (n, m). Qed.

Lemma cfun_cond_cyclic : forall n m, cond_cyclicPerm (cfun n m).
Proof.
intros n m; destruct n ; [ | destruct m ].
- unfold cfun; simpl; rewrite app_nil_r.
  apply Id_cond_cyclic.
- unfold cfun; simpl; rewrite seq_cons.
  apply Id_cond_cyclic.
- apply cfun_S_cond_cyclic.
Qed.

Lemma cond_cyclic_cfun_lt {l} : cond_cyclicPerm l -> {' (n, m) : _ & l = cfun n m & m = 0 -> n = 0}.
Proof.
intros [[[n m] Heqcp] | Heqcp]; subst.
- now exists (S n, S m).
- exists (0, length l).
  + now unfold cfun; rewrite app_nil_r.
  + now intros _.
Qed.

Lemma cond_cyclic_cfun {l} : cond_cyclicPerm l -> {' (n, m) : _ & l = cfun n m }.
Proof. intros Hc; destruct (cond_cyclic_cfun_lt Hc) as [(n,m) Heq Hlt]; now exists (n,m). Qed.

Lemma cond_cyclic_is_perm {l} : cond_cyclicPerm l -> is_perm l = true.
Proof. intros Hc; destruct (cond_cyclic_cfun Hc) as [(n, m) Heq]; subst; apply cfun_is_perm. Qed.

Definition CyclicPerm_R {A} (l1 l2 : list A) :=
  { f : _ & cond_cyclicPerm f & prod (length f = length l1) (l2 = f ∘ l1) }.

Infix "~°~" := CyclicPerm_R (at level 70).


Section Properties.

Context {A : Type}.
Implicit Types la lb lc : list A.

Lemma CyclicPerm_R_commu : forall la lb, la ++ lb ~°~ lb ++ la.
Proof.
intros l1 l2.
split with (cfun (length l1) (length l2)); [ | split ].
- apply cfun_cond_cyclic.
- length_lia.
- symmetry; apply app_cfun_eq.
Defined.

Lemma decomp_CyclicPerm_R : forall la lb,
  la ~°~ lb -> {' (la', lb') : _ & la' ++ lb' = la & lb' ++ la' = lb }.
Proof.
intros l1 l2 [f Hc [Hlen Heq]]; subst.
destruct (cond_cyclic_cfun Hc) as [(n,m) Heq]; subst.
exists (Id n ∘ l1, seq n m ∘ l1).
- rewrite <- app_nat_fun_app, <- seq_app.
  rewrite cfun_length in Hlen; rewrite Hlen.
  apply app_Id.
- symmetry; apply app_nat_fun_app.
Qed.

Instance CyclicPerm_Perm_R : Proper (CyclicPerm_R ==> (@Perm_R A)) (fun a => a).
Proof. intros l1 l2 [f Hc [Hlen Heq]]; subst; now exists f; [ apply cond_cyclic_is_perm | ]. Defined.

Instance CyclicPerm_R_refl : Reflexive (@CyclicPerm_R A).
Proof.
  intros l.
  split with (Id (length l)); repeat split.
  - apply Id_cond_cyclic.
  - length_lia.
  - symmetry; apply app_Id.
Defined.

Instance CyclicPerm_R_sym : Symmetric (@CyclicPerm_R A).
Proof.
intros l l' [f Hc [Hlen Heq]]; subst.
destruct (cond_cyclic_cfun Hc) as [(n,m) Heq]; subst.
exists (cfun m n); [ | split ].
- apply cfun_cond_cyclic.
- rewrite app_nat_fun_length by assumption.
  length_lia.
- rewrite <- asso_app_nat_fun, cfun_inv.
  rewrite cfun_length in Hlen; rewrite Hlen.
  symmetry; apply app_Id.
Defined.

Instance CyclicPerm_R_trans : Transitive (@CyclicPerm_R A).
Proof.
intros l1 l2 l3 [c1 HC1 [Hlen1 Heq1]] [c2 HC2 [Hlen2 Heq2]]; subst.
destruct (cond_cyclic_cfun HC1) as [(i,j) Heq]; subst.
destruct (cond_cyclic_cfun HC2) as [(k,l) Heq]; subst.
rewrite app_nat_fun_length in Hlen2 by assumption.
rewrite_all cfun_length.
destruct (cfun_cfun i j k l) as [(n,m) Heq]; [ lia | ].
rewrite <- asso_app_nat_fun, Heq.
exists (cfun n m); [ | split ].
- apply cfun_cond_cyclic.
- rewrite <- Heq.
  rewrite app_nat_fun_length; rewrite ? cfun_length; lia.
- reflexivity.
Defined.

Global Instance CyclicPerm_R_equiv : Equivalence (@CyclicPerm_R A).
Proof.
split.
- apply CyclicPerm_R_refl.
- apply CyclicPerm_R_sym.
- apply CyclicPerm_R_trans.
Qed.

Lemma CyclicPerm_R_app : forall la lb lc, la ++ lb ~°~ lc -> lb ++ la ~°~ lc.
Proof. intros l1 l2 l3 HC; now transitivity (l1 ++ l2); [ apply CyclicPerm_R_commu | ]. Defined.

Lemma CyclicPerm_R_app_rot : forall la lb lc, la ++ lb ++ lc ~°~ lb ++ lc ++ la.
Proof. intros l1 l2 l3; rewrite (app_assoc l2); apply CyclicPerm_R_commu. Defined.

Lemma CyclicPerm_R_last : forall a la, a :: la ~°~ la ++ a :: nil.
Proof. intros a la; change (a :: la) with ((a :: nil) ++ la); apply CyclicPerm_R_commu. Defined.

Lemma CyclicPerm_R_swap : forall a b : A, a :: b :: nil ~°~ b :: a :: nil.
Proof. intros a b; change (b :: a :: nil) with ((b :: nil) ++ (a :: nil)); apply CyclicPerm_R_last. Defined.

Lemma CyclicPerm_R_cons : forall la a lb, la ++ a :: nil ~°~ lb -> a :: la ~°~ lb.
Proof. intros l1 a l2 HC; now apply (CyclicPerm_R_app l1 (a :: nil)). Defined.

Lemma CyclicPerm_R_morph_cons : forall P : list A -> Prop,
  (forall a l, P (l ++ a :: nil) -> P (a :: l)) ->  Proper (CyclicPerm_R ==> Basics.impl) P.
Proof.
enough (forall P : list A -> Prop,
         (forall a l, P (l ++ a :: nil) -> P (a :: l)) -> forall l1 l2, CyclicPerm_R l1 l2 -> P l1 -> P l2)
  as Himp by now intros P HP l1 l2 HC H; apply Himp with l1.
intros P HP l1 l2 HC.
apply decomp_CyclicPerm_R in HC as [[l0 l3] Heql1 Heql2]; subst.
revert l0 ; induction l3 using rev_ind ; intros l0 HPl.
- now rewrite app_nil_r in HPl.
- rewrite app_assoc in HPl.
  apply HP in HPl.
  rewrite <- app_assoc, <- app_comm_cons.
  now apply IHl3.
Qed.

Lemma CyclicPerm_R_nil : forall la, nil ~°~ la -> la = nil.
Proof. intros; now apply Perm_R_nil, CyclicPerm_Perm_R. Qed.

Lemma CyclicPerm_R_nil_cons : forall la a, nil ~°~ a :: la -> False.
Proof. intros l a HC; apply CyclicPerm_R_nil in HC; inversion HC. Qed.

Lemma CyclicPerm_R_one : forall a b : A, a :: nil ~°~ b :: nil -> a = b.
Proof. intros; now apply Perm_R_length_1, CyclicPerm_Perm_R. Qed.

Lemma CyclicPerm_R_two : forall a1 a2 b1 b2 : A,
  a1 :: a2 :: nil ~°~ b1 :: b2 :: nil -> { a1 = b1 /\ a2 = b2 } +  { a1 = b2 /\ a2 = b1 }.
Proof. intros; now apply Perm_R_length_2, CyclicPerm_Perm_R. Qed.

Lemma CyclicPerm_R_one_inv : forall la a, a :: nil ~°~ la -> la = a :: nil.
Proof. intros; now apply Perm_R_length_1_inv, CyclicPerm_Perm_R. Qed.

Lemma CyclicPerm_R_two_inv : forall a b la,
  a :: b :: nil ~°~ la -> { la = a :: b :: nil } + { la = b :: a :: nil }.
Proof. intros; now apply Perm_R_length_2_inv, CyclicPerm_Perm_R. Qed.

Lemma CyclicPerm_R_vs_elt_inv : forall a la lb lc,
  la ~°~ lb ++ a :: lc -> {'(l1', l2') | lc ++ lb = l2' ++ l1' & la = l1' ++ a :: l2' }.
Proof.
  intros a l l1 l2 HC.
  apply decomp_CyclicPerm_R in HC as [[l0 l3] H1 H2]; subst.
  symmetry in H2.
  dichot_Type_elt_app_exec H2 ; subst.
  - exists (l0 ++ l1, l) ; simpl ; now rewrite <- app_assoc.
  - exists (l4, l2 ++ l3) ; simpl ; now rewrite <- app_assoc.
Qed.

Lemma CyclicPerm_R_vs_cons_inv : forall a la lb,
  la ~°~ a :: lb -> {'(l1', l2') | lb = l2' ++ l1' & la = l1' ++ a :: l2' }.
Proof.
  intros a l l1 HC.
  rewrite <- (app_nil_l (a::_)) in HC.
  apply CyclicPerm_R_vs_elt_inv in HC; destruct HC as [(l' & l'') H1 H2].
  rewrite app_nil_r in H1 ; subst.
  now exists (l', l'').
Qed.

Lemma CyclicPerm_R_app_app_inv : forall la lb lc ld,
  la ++ lb ~°~ lc ++ ld ->
     {'(l1',l2',l3',l4') : _ & prod (la ~°~ l1' ++ l3') (lb ~°~ l2' ++ l4')
                             & prod (lc ~°~ l1' ++ l2') (ld ~°~ l3' ++ l4') }
   + {'(l1',l2') : _ & prod (la ~°~ ld ++ l1') (lc ~°~ lb ++ l2')
                     & l1' ~°~ l2' }
   + {'(l1',l2') : _ & prod (lb ~°~ ld ++ l1') (lc ~°~ la ++ l2')
                     & l1' ~°~ l2' }
   + {'(l1',l2') : _ & prod (la ~°~ lc ++ l1') (ld ~°~ lb ++ l2')
                     & l1' ~°~ l2' }
   + {'(l1',l2') : _ & prod (lb ~°~ lc ++ l1') (ld ~°~ la ++ l2')
                     & l1' ~°~ l2' }.
Proof.
intros l1 l2 l3 l4 HC.
apply decomp_CyclicPerm_R in HC as [[lx ly] Hx Hy].
dichot_Type_app_exec Hx ; dichot_Type_app_exec Hy ; subst.
- left ; left ; left ; right.
  exists (l ++ l0 , l0 ++ l).
  + split; rewrite <- ? app_assoc; apply CyclicPerm_R_app_rot.
  + apply CyclicPerm_R_commu.
- dichot_Type_app_exec Hy0 ; subst.
  + left ; left ; left ; left.
    exists (l, l0, lx, l5); split; try apply CyclicPerm_R_commu; reflexivity.
  + left ; right.
    exists (l1 ++ lx , lx ++ l1).
    * split; rewrite <- ? app_assoc; apply CyclicPerm_R_app_rot.
    * apply CyclicPerm_R_commu.
- dichot_Type_app_exec Hy1 ; subst.
  + left ; left ; right.
    exists (ly ++ l2, l2 ++ ly).
    * split; rewrite <- ? app_assoc; apply CyclicPerm_R_app_rot.
    * apply CyclicPerm_R_commu.
  + left ; left ; left ; left.
    exists (l, ly, l3, l0); split; try apply CyclicPerm_R_commu; reflexivity.
- right.
  exists (l5 ++ l0, l0 ++ l5).
  + split; rewrite <- ? app_assoc; apply CyclicPerm_R_app_rot.
  + apply CyclicPerm_R_commu.
Defined.

(** [rev], [in], [map], [Forall], [Exists], etc. *)
Instance CyclicPerm_R_rev : Proper (CyclicPerm_R ==> CyclicPerm_R) (@rev A).
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

Instance CyclicPerm_R_in (a : A) : Proper (CyclicPerm_R ==> Basics.impl) (In a).
Proof with try eassumption.
intros l l' HC Hin.
eapply Perm_R_in...
apply CyclicPerm_Perm_R...
Qed.

End Properties.


Instance CyclicPerm_R_map {A B} (f : A -> B) : Proper (CyclicPerm_R ==> CyclicPerm_R) (map f).
Proof.
intros l l' HC.
apply decomp_CyclicPerm_R in HC as [[lx ly] Hx Hy]; subst ; rewrite ? map_app.
apply CyclicPerm_R_commu.
Defined.

Lemma CyclicPerm_R_map_inv {A B} : forall(f : A -> B) l1 l2,
  l1 ~°~ map f l2 -> { l : _ & l1 = map f l & l2 ~°~ l }.
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

Lemma CyclicPerm_R_image {A B} : forall (f : A -> B) a l l',
  a :: l ~°~ map f l' -> { a' | a = f a' }.
Proof.
intros f a l l' HP.
eapply Perm_R_image.
apply CyclicPerm_Perm_R ; eassumption.
Qed.

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

Lemma CyclicPerm_R_Forall2 {A B} (P : A -> B -> Type) : forall l1 l1' l2,
  l1 ~°~ l1' -> Forall2_Type P l1 l2 -> { l2' : _ & l2 ~°~ l2' & Forall2_Type P l1' l2' }.
Proof.
intros l1 l1' l2 HP; revert l2.
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


(* Cyclic Permutations as Nat *)
Definition app_cperm_nat {A} n (l : list A) :=
  skipn n l ++ firstn n l.

Lemma app_cperm_cfun {A} : forall n (l : list A), n <= length l ->
  app_cperm_nat n l = app_nat_fun (cfun n (length l - n)) l.
Proof.
  intros n l Hle.
  rewrite<- (firstn_skipn n l) at 3.
  rewrite<- (firstn_length_le l) at 2; try assumption.
  replace (length l - n) with (length (skipn n l)); [ symmetry; apply app_cfun_eq | ].
  rewrite<- (firstn_skipn n l) at 2.
  rewrite app_length.
  rewrite firstn_length_le; try assumption; lia.
Qed.

Lemma cond_cyclicPerm_to_app_cperm : forall p, cond_cyclicPerm p ->
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

