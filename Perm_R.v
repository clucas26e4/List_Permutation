(* ll library for yalla *)

Require Import CMorphisms.
Require Import Lia.
Require Import PeanoNat.
Require Import EqNat.

Require Import Bool_more.
Require Import List_Type_more.
Require Import List_nat.
Require Import List_more2.
Require Import Perm.
Require Import Permutation_Type.
Require Import Transposition.
Require Import misc.
Require Import Fun_nat.
Set Implicit Arguments.

Section Perm_R.

  Variable A : Type.

  Definition Perm_R (l1 : list A) l2 : Type := {p  & prod (is_perm p = true) ((length p = length l1) * (l2 = app_nat_fun p l1))}.

End Perm_R.
(* Some facts about Perm_R *)

Lemma Perm_R_nil {A} : forall (l : list A),
    Perm_R nil l -> l = nil.
Proof with try reflexivity; try assumption.
  intros l Hperm.
  destruct Hperm as (f & (Hp & Hlen & Heq)).
  rewrite Heq...
Qed.

Lemma Perm_R_nil_cons {A} : forall (l : list A) x,
    Perm_R nil (x :: l) -> False.
Proof with try reflexivity; try assumption.
  intros l x Hperm.
  destruct Hperm as (f & (Hp & Hlen & Heq)).
  inversion Heq.
Qed.

Lemma Perm_R_skip {A} : forall l l' (x : A),
    Perm_R l l' ->
    Perm_R (x :: l) (x :: l').
Proof with try reflexivity; try assumption.
  intros l l' x (p & (Hperm & Hlen & Heq)).
  split with (0 :: incr_all p 1).
  repeat split.
  - change (0 :: incr_all p 1) with ((0 :: nil) ++ (incr_all p (length (0 :: nil)))).
    apply append_perm_is_perm...
  - simpl.
    rewrite incr_all_length.
    rewrite <- Hlen...
  - rewrite Heq.
    simpl.
    change (map (fun x0 : nat => match x0 with
                          | 0 => x
                          | S n => nth n l x
                                 end) (incr_all p 1)) with (app_nat_fun (incr_all p (length (x :: nil))) ((x :: nil) ++ l)).
    rewrite app_nat_fun_right...
    simpl in Hlen.
    clear Heq.
    apply andb_prop in Hperm as (Hal & _).
    rewrite <- Hlen...
Defined.

Lemma Perm_R_swap {A} : forall l (x y : A),
    Perm_R (x :: y :: l) (y :: x :: l).
Proof with try reflexivity; try assumption.
  intros l x y.
  split with (1 :: 0 :: (incr_all (Id (length l)) 2)).
  repeat split.
  - change (1 :: 0 :: (incr_all (Id (length l)) 2)) with ((1 :: 0 :: nil) ++ (incr_all (Id (length l)) (length (1 :: 0 :: nil)))).
    apply append_perm_is_perm...
    apply Id_is_perm.
  - simpl.
    rewrite incr_all_length.
    rewrite Id_length...
  - simpl.
    change (map
              (fun x0 : nat =>
                 match x0 with
                 | 0 => x
                 | 1 => y
                 | S (S n0) => nth n0 l x
                 end) (incr_all (Id (length l)) 2)) with
        (app_nat_fun (incr_all (Id (length l)) (length (x :: y :: nil))) ((x :: y :: nil) ++ l)).
    rewrite app_nat_fun_right.
    + rewrite app_Id...
    + apply all_lt_Id.
Defined.

(* Permutation over lists is an equivalence relation *)

Lemma Perm_R_refl {A} : forall (l : list A),
    Perm_R l l.
Proof with try reflexivity.
  intro l.
  split with (Id (length l)).
  repeat split.
  - apply Id_is_perm.
  - rewrite Id_length...
  - rewrite app_Id...
Defined.

Lemma Perm_R_trans {A} : forall (l1 l2 l3 : list A),
    Perm_R l1 l2 ->
    Perm_R l2 l3 ->
    Perm_R l1 l3.
Proof with try reflexivity; try assumption.
  intros l1 l2 l3 IHHp1 IHHp2.
  destruct IHHp1 as (p1 & (Hperm1 & Hlen1 & IHHp1)).
  destruct IHHp2 as (p2 & (Hperm2 & Hlen2 & IHHp2)).
  assert (length p2 = length p1).
  { rewrite Hlen2.
    rewrite IHHp1.
    destruct l1; [destruct p1 ; [ | inversion Hlen1] | ]...
    unfold app_nat_fun; rewrite map_length... }
  split with (app_nat_fun p2 p1).
  repeat split.
  - apply compo_perm_is_perm...
  - destruct p1.
    + destruct l1...
    + unfold app_nat_fun.
      rewrite map_length.
      rewrite H...
  - rewrite asso_app_nat_fun.
    rewrite<- IHHp1...
Defined.

Lemma Perm_R_sym {A} : forall (l1 l2 : list A),
    Perm_R l1 l2 ->
    Perm_R l2 l1.
Proof with try reflexivity; try assumption.
  intros l1 l2 (p & (Hperm & Hlen & Heq)).
  destruct (perm_has_inv p Hperm) as (p_inv & (Heq_inv & (Hperm_inv & Hlen_eq))).
  split with p_inv.
  repeat split...
  - rewrite Heq.
    rewrite <- Hlen_eq.
    destruct l1; unfold app_nat_fun; try now rewrite Hlen.
    rewrite map_length...
  - rewrite<- (app_Id l1).
    rewrite <- Hlen.
    rewrite<- Heq_inv.
    rewrite Heq.
    rewrite asso_app_nat_fun...
Defined.

Instance Perm_R_Equivalence A : Equivalence (@Perm_R A) | 10 := {
  Equivalence_Reflexive := @Perm_R_refl A ;
  Equivalence_Symmetric := @Perm_R_sym A ;
  Equivalence_Transitive := @Perm_R_trans A }.

Instance Perm_R_cons A :
 Proper (Logic.eq ==> @Perm_R A ==> @Perm_R A) (@cons A) | 10.
Proof with try reflexivity; try assumption.
  unfold Proper.
  repeat intro.
  destruct X as (p & (Hperm & Hlen & Heq)).
  rewrite H.
  apply Perm_R_skip.
  split with p.
  repeat split...
Defined.

Hint Resolve Perm_R_refl Perm_R_skip.

(* These hints do not reduce the size of the problem to solve and they
   must be used with care to avoid combinatoric explosions *)
Local Hint Resolve Perm_R_swap Perm_R_trans.
Local Hint Resolve Perm_R_sym.

Section Perm_R_properties.

Context {A : Type}.

Implicit Types a b : A.
Implicit Types l m : list A.

(* Compatibility with others operations on lists *)

Lemma Perm_R_length : forall (l1 l2 : list A),
    Perm_R l1 l2 ->
    length l1 = length l2.
Proof with try reflexivity.
  intros l1 l2 (f & (Hp & Hlen & Heq)).
  simpl in Hlen.
  rewrite Heq.
  symmetry.
  destruct l1...
  unfold app_nat_fun; rewrite map_length.
  apply Hlen.
Qed.

Lemma Perm_R_app_tail : forall (l l' tl : list A),
 Perm_R l l' -> Perm_R (l++tl) (l'++tl).
Proof with try reflexivity; try assumption.
  intros l l' tl (p & (Hperm & Hlen & Heq)).
  split with (p ++ incr_all (Id (length tl)) (length p)).
  repeat split.
  - apply append_perm_is_perm...
    apply Id_is_perm.
  - length_lia.
  - rewrite Hlen.
    rewrite append_fun_eq.
    + rewrite app_Id.
      rewrite Heq...
    + apply andb_prop in Hperm as (Hal & _).
      rewrite<- Hlen...
    + apply all_lt_Id.
Defined.

Lemma Perm_R_app_head : forall (l tl tl' : list A),
 Perm_R tl tl' -> Perm_R (l++tl) (l++tl').
Proof with try assumption; try reflexivity.
  intros l tl tl' (p & (Hperm & Hlen & Heq)).
  split with (Id (length l) ++ incr_all p (length l)).
  repeat split.
  - replace (length l) with (length (Id (length l))) at 2 by now rewrite Id_length.
    apply append_perm_is_perm...
    apply Id_is_perm.
  - length_lia.
  - rewrite append_fun_eq.
    + rewrite app_Id.
      rewrite Heq...
    + apply all_lt_Id.
    + apply andb_prop in Hperm as (Hal & _).
      rewrite<- Hlen...
Defined.

Theorem Perm_R_app : forall (l m l' m' : list A),
 Perm_R l l' -> Perm_R m m' -> Perm_R (l++m) (l'++m').
Proof with try assumption; try reflexivity.
  intros l m l' m' Hperm_l Hperm_m.
  transitivity (l' ++ m); [apply Perm_R_app_tail | apply Perm_R_app_head]...
Defined.

Global Instance Perm_R_app' :
 Proper (@Perm_R A ==> @Perm_R A ==> @Perm_R A) (@app A) | 10.
Proof.
  repeat intro; now apply Perm_R_app.
Defined.

Lemma Perm_R_add_inside : forall a (l l' tl tl' : list A),
  Perm_R l l' -> Perm_R tl tl' ->
  Perm_R (l ++ a :: tl) (l' ++ a :: tl').
Proof with try reflexivity; try assumption.
  intros a l l' tl tl' Hperm_l Hperm_tl.
  transitivity (l' ++ a :: tl) ; [ apply Perm_R_app_tail | apply Perm_R_app_head ]...
  apply Perm_R_cons...
Defined.  

Lemma Perm_R_cons_append : forall (l : list A) x,
  Perm_R (x :: l) (l ++ x :: nil).
Proof with try reflexivity; try assumption.
  intros l x.
  split with (cfun 1 (length l)).
  repeat split.
  - apply cfun_is_perm.
  - length_lia.
  - change (x :: l) with ((x :: nil) ++ l).
    change 1 with (length (x :: nil)).
    rewrite app_cfun_eq...
Defined.  
Local Hint Resolve Perm_R_cons_append.

Theorem Perm_R_app_comm : forall (l l' : list A),
  Perm_R (l ++ l') (l' ++ l).
Proof with try reflexivity; try assumption.
  intros l l'.
  split with (cfun (length l) (length l')).
  repeat split.
  - apply cfun_is_perm.
  - length_lia.
  - rewrite app_cfun_eq...
Qed.    
Local Hint Resolve Perm_R_app_comm.

Theorem Perm_R_cons_app : forall (l l1 l2:list A) a,
  Perm_R l (l1 ++ l2) -> Perm_R (a :: l) (l1 ++ a :: l2).
Proof with auto.
  intros l l1 l2 a Hperm.
  transitivity (a :: (l1 ++ l2))...
  transitivity (a :: (l2 ++ l1))...
  change (a :: l2 ++ l1) with ((a :: l2) ++ l1)...
Defined.
Local Hint Resolve Perm_R_cons_app.

Lemma Perm_R_Add_Type a l l' : Add_Type a l l' -> Perm_R (a::l) l'.
Proof.
  induction 1; simpl; trivial.
  eapply Perm_R_trans ; [ apply Perm_R_swap | ].
  now apply Perm_R_skip.
Defined.

Theorem Perm_R_middle : forall (l1 l2:list A) a,
    Perm_R (a :: l1 ++ l2) (l1 ++ a :: l2).
Proof.
  auto.
Defined.
Local Hint Resolve Perm_R_middle.

Theorem Perm_R_rev : forall (l : list A), Perm_R l (rev l).
Proof.
  induction l as [| x l]; simpl; trivial.
  eapply Perm_R_trans ; [ apply Perm_R_cons_append | ].
  apply Perm_R_app_tail. assumption.
Defined.

Global Instance Perm_R_rev' :
 Proper (@Perm_R A ==> @Perm_R A) (@rev A) | 10.
Proof.
  intros l1 l2 HP.
  eapply Perm_R_trans ; [ | eapply Perm_R_trans ].
  - apply Perm_R_sym.
    apply Perm_R_rev.
  - eassumption.
  - apply Perm_R_rev.
Defined.

Global Instance Perm_R_length' :
  Proper (@Perm_R A ==> Logic.eq) (@length A) | 10.
Proof.
  exact Perm_R_length.
Qed.

Theorem Perm_R_nil_app_cons : forall (l l' : list A) (x : A),
    Perm_R nil (l++x::l') -> False.
Proof.
  intros l l' x Hperm.
  refine (O_S (length l + length l') _).
  apply Perm_R_length in Hperm.
  rewrite app_length in Hperm.
  simpl in Hperm.
  rewrite<- Nat.add_succ_r.
  apply Hperm.
Qed.

Ltac InvAdd_Type := repeat (match goal with
 | H: Add_Type ?x _ (_ :: _) |- _ => inversion H; clear H; subst
 end).

Ltac finish_basic_perms_Type H :=
  try constructor; try rewrite Perm_R_swap; try constructor; trivial;
  (rewrite <- H; now apply Perm_R_Add_Type) ||
  (rewrite H; symmetry; now apply Perm_R_Add_Type).

Theorem Perm_R_cons_inv l l' a :
  Perm_R (a::l) (a::l') -> Perm_R l l'.
Proof with auto.
  intros (p & (Hperm & Hlen & Heq)).
  destruct p; try now inversion Heq.
  app_nat_fun_unfold p l n a.
  destruct (nth_split_Type n (a :: l) a) as [(la,lb) Heq' Hlenla].
  { apply andb_prop in Hperm as (Hal & _).
    apply andb_prop in Hal as (Hlt & _).
    apply Nat.ltb_lt in Hlt.
    rewrite <- Hlen... }
  replace (nth n (a :: l) a) with a in *.
  2:{ inversion Heq.
      rewrite<- H0.
      pattern a at 1.
      rewrite H0... }
  destruct la.
  - split with (downshift p n).
    repeat split.
    + apply tail_perm...
    + simpl.
      apply Nat.succ_inj in Hlen.
      rewrite downshift_length...
      clear Heq.
      apply andb_prop in Hperm as (_ & Had).
      apply negb_true_iff.
      apply andb_prop in Had as (nHin & _)...
    + apply andb_prop in Hperm as (Hal & Had).
      simpl in Hal, Had.
      apply andb_prop in Hal as (Hlt & Hal).
      apply andb_prop in Had as (nHin & Had).
      inversion Heq'.
      destruct n; try now inversion Hlenla.
      replace (app_nat_fun (downshift p 0) lb) with (app_nat_fun (incr_all (downshift p 0) 1) (a :: lb)).
      2:{ change (a :: lb) with ((a :: nil) ++ lb).
          change 1 with (length (a :: nil)).
          rewrite app_nat_fun_right...
          rewrite<- downshift_all_lt...
          inversion Hlenla; rewrite <- H0.
          simpl in Hlen.
          rewrite<- Hlen... }
      rewrite incr_all_downshift_0.
      2:{ apply negb_true_iff... }
      rewrite<- H0.
      inversion Heq...
  - inversion Heq'; subst.
    rename a0 into a.
    transitivity (a :: la ++ lb)...
    split with (downshift p (S (length la))).
    repeat split.
    + apply tail_perm...
    + simpl.
      simpl in Hlen.
      apply Nat.succ_inj in Hlen.
      rewrite app_length in Hlen.
      simpl in Hlen.
      rewrite Nat.add_succ_r in Hlen.
      rewrite downshift_length ; [ rewrite app_length | ]...
      clear Heq.
      apply andb_prop in Hperm as (_ & Had).
      apply negb_true_iff.
      apply andb_prop in Had as (nHin & _)...
    + change (a :: la ++ lb) with ((a :: la) ++ lb).
      change (S (length la)) with (length (a :: la)).
      rewrite<- app_nat_fun_downshift with _ _ a _.
      * inversion Heq...
      * apply negb_true_iff.
        apply andb_prop in Hperm as (_ & Had).
        apply andb_prop in Had as (nHin & _)...
      * apply andb_prop in Hperm as (Hal & _).
        simpl in Hal.
        apply andb_prop in Hal as (_ & Hal).
        simpl in Hlen.
        rewrite Hlen in Hal.
        rewrite app_length in Hal.
        simpl in Hal.
        rewrite Nat.add_succ_r in Hal.
        rewrite app_length...
Defined. 

Theorem Perm_R_Add_Type_inv a l1 l2 :
  Perm_R l1 l2 -> forall l1' l2', Add_Type a l1' l1 -> Add_Type a l2' l2 ->
                                  Perm_R l1' l2'.
Proof with auto.
  intros Hperm l1' l2' Hadd1 Hadd2.
  apply Perm_R_cons_inv with a.
  transitivity l1.
  { apply Perm_R_Add_Type... }
  transitivity l2...
  symmetry.
  apply Perm_R_Add_Type...
Defined.

Theorem Perm_R_app_inv (l1 l2 l3 l4:list A) a :
  Perm_R (l1++a::l2) (l3++a::l4) -> Perm_R (l1++l2) (l3 ++ l4).
Proof with auto.
  intros Hperm.
  apply Perm_R_cons_inv with a.  
  transitivity (l1 ++ a :: l2)...
  transitivity (l3 ++ a :: l4)...
Defined.
  
Theorem Perm_R_cons_app_inv l l1 l2 a :
  Perm_R (a :: l) (l1 ++ a :: l2) -> Perm_R l (l1 ++ l2).
Proof with auto.
  intros Hperm.
  apply Perm_R_cons_inv with a.
  transitivity (l1 ++ a :: l2)...
Defined.
  
Theorem Perm_R_app_inv_l : forall l l1 l2,
    Perm_R (l ++ l1) (l ++ l2) -> Perm_R l1 l2.
Proof with auto.
  induction l; intros l1 l2 Hperm; [ | apply IHl; apply Perm_R_cons_inv with a]...
Defined.
           
Theorem Perm_R_app_inv_r l l1 l2 :
  Perm_R (l1 ++ l) (l2 ++ l) -> Perm_R l1 l2.
Proof with auto.
  induction l; intros Hperm; [ rewrite 2 app_nil_r in Hperm | apply IHl; apply Perm_R_app_inv with a]...
Defined.   

Lemma Perm_R_length_1_inv: forall a l, Perm_R (a :: nil) l -> l = (a :: nil).
Proof with try reflexivity.
  intros a l (p & (Hperm & Hlen & Heq)).
  rewrite Heq.
  destruct p; try now inversion Hlen.
  destruct p; try now inversion Hlen.
  destruct n...
  apply andb_prop in Hperm as (Hal & _).
  apply andb_prop in Hal as (Hlt & _).
  inversion Hlt.
Qed.

Lemma Perm_R_length_1: forall a b, Perm_R (a :: nil) (b :: nil) -> a = b.
Proof.
  intros a b Hperm.
  apply Perm_R_length_1_inv in Hperm.
  inversion Hperm.
  reflexivity.
Qed.

Lemma Perm_R_length_2_inv :
  forall a1 a2 l, Perm_R (a1 :: a2 :: nil) l -> { l = (a1 :: a2 :: nil) } + { l = (a2 :: a1 :: nil) }.
Proof with try reflexivity.
  intros a1 a2 l (p & (Hperm & Hlen & Heq)).
  simpl in Hlen.
  do 3 (destruct p; try now inversion Hlen).
  destruct n; [ | destruct n].
  - destruct n0 ; [ | destruct n0].
    + apply andb_prop in Hperm as (_ & Had).
      apply andb_prop in Had as (nHin & _).
      inversion nHin.      
    + left.
      rewrite Heq...
    + apply andb_prop in Hperm as (Hal & _).
      apply andb_prop in Hal as (_ & Hal).
      apply andb_prop in Hal as (Hlt & _).
      inversion Hlt.
  - destruct n0 ; [ | destruct n0].
    + right.
      rewrite Heq...
    + apply andb_prop in Hperm as (_ & Had).
      apply andb_prop in Had as (nHin & _).
      inversion nHin.
    + apply andb_prop in Hperm as (Hal & _).
      apply andb_prop in Hal as (_ & Hal).
      apply andb_prop in Hal as (Hlt & _).
      inversion Hlt.
  - apply andb_prop in Hperm as (Hal & _).
    apply andb_prop in Hal as (Hlt & _).
    inversion Hlt.
Qed.

Lemma Perm_R_length_2 :
  forall a1 a2 b1 b2, Perm_R (a1 :: a2 :: nil) (b1 :: b2 :: nil) ->
                      { a1 = b1 /\ a2 = b2 } + { a1 = b2 /\ a2 = b1 }.
Proof with try reflexivity.
  intros a1 a2 b1 b2 Hperm.
  destruct (Perm_R_length_2_inv Hperm) as [Heq | Heq]; inversion Heq.
  - left; split...
  - right; split...
Qed.

Theorem Perm_R_in : forall (l l' : list A) (x : A),
    Perm_R l l' -> In x l -> In x l'.
Proof with try reflexivity; try assumption.
  intros l l' x (p & (Hperm & Hlen & Heq)) Hin.
  apply In_nth with _ _ _ x in Hin as [n (Hlen' & Heq')].
  rewrite <- Heq', Heq; clear Heq'.
  destruct l; try now inversion Hlen'.
  replace (nth n (a::l) x) with (nth n (a::l) a) by (apply nth_indep; assumption).
  destruct (perm_surj _ 0 n Hperm) as (i & (Hlen'' & Heq'')).
  { rewrite Hlen; simpl in Hlen'; simpl; lia. }
  rewrite <- Heq''.
  rewrite nth_nth...
  apply nth_In.
  rewrite app_nat_fun_length...
  intros H; inversion H.
Qed.

Global Instance Perm_R_in' :
  Proper (Logic.eq ==> @Perm_R A ==> iff) (@In A) | 10.
Proof with try reflexivity; try assumption.
  repeat red; intros; subst; eauto using Perm_R_in.
Qed.

Theorem Perm_R_in_Type : forall (l l' : list A) (x : A),
    Perm_R l l' -> In_Type x l -> In_Type x l'.
Proof with try reflexivity; try assumption.
  intros l l' x (p & (Hperm & Hlen & Heq)) Hin.
  apply In_nth_Type with _ _ x in Hin as [n Hlen' Heq'].
  rewrite <- Heq', Heq; clear Heq'.
  destruct l; try now (exfalso; inversion Hlen').
  replace (nth n (a::l) x) with (nth n (a::l) a) by (apply nth_indep; assumption).
  destruct (perm_surj _ 0 n Hperm) as (i & (Hlen'' & Heq'')).
  { rewrite Hlen; simpl in Hlen'; simpl; lia. }
  rewrite <- Heq''.
  rewrite nth_nth...
  apply nth_In_Type.
  rewrite app_nat_fun_length...
  intros H; inversion H.
Qed.

Global Instance Perm_R_in_Type' :
 Proper (Logic.eq ==> @Perm_R A ==> Basics.arrow) (@In_Type A) | 10.
Proof with try reflexivity; try assumption.
  intros l1 l2 Heq l1' l2' HP Hi ; subst.
  eauto using Perm_R_in_Type.
Qed.

End Perm_R_properties.

Section Perm_R_map.

Variable A B : Type.
Variable f : A -> B.

Lemma Perm_R_map l l' :
  Perm_R l l' -> Perm_R (map f l) (map f l').
Proof with try reflexivity; try assumption.
  intros (p & (Hperm & Hlen & Heq)).
  split with p.
  repeat split...
  - rewrite map_length...
  - rewrite app_nat_fun_map.
    rewrite Heq...
Qed.

Global Instance Perm_R_map' :
  Proper (@Perm_R A ==> @Perm_R B) (map f) | 10.
Proof.
  exact Perm_R_map.
Qed.

End Perm_R_map.

(* INDUCTION PRINCIPLE *)
Theorem Perm_R_rect_transpo {A} :
 forall P : list A -> list A -> Type,
   P nil nil ->
   (forall x l l', Perm_R l l' -> P l l' -> P (x :: l) (x :: l')) ->
   (forall x y l, P (y :: x :: l) (x :: y :: l)) ->
   (forall l l' l'', Perm_R l l' -> P l l' -> Perm_R l' l'' -> P l' l'' -> P l l'') ->
   forall l l', Perm_R l l' -> P l l'.
Proof with try assumption; try reflexivity.
  intros P Hnil Hskip Hswap Htrans.
  intros l l' Hperm.
  destruct Hperm as (p & (Hperm & Hlen & Heq)).
  simpl in Hlen.
  rewrite Heq.
  apply (Perm_rect (fun f => fun l => is_perm f = true -> P l (app_nat_fun f l)))...
  - clear l l' p Hperm Hlen Heq.
    intros l Hperm.
    rewrite app_Id.
    clear Hperm.
    induction l...
    apply Hskip...
  - clear l l' p Hperm Hlen Heq.
    intros l0 i Hnnil Hperm.
    clear Hperm.
    revert l0 Hnnil.
    induction i; intros l0 Hnnil.
    + unfold transpo.
      destruct l0; try now (exfalso; apply Hnnil).
      destruct l0.
      * simpl.
        apply Hskip...
      * replace (0 <? (length (a :: a0 :: l0)) - 1) with true...
        simpl.
        replace (map
                   (fun x : nat =>
                      match x with
                      | 0 => a
                      | 1 => a0
                      | S (S m0) => nth m0 l0 a
                      end) (incr_all (Id (length l0 - 0)) 2)) with l0; [apply Hswap | ].
        change (fun x : nat =>
                  match x with
                  | 0 => a
                  | 1 => a0
                  | S (S m0) => nth m0 l0 a
                  end) with (fun x => nth x (a :: a0 :: l0) a).
        change (map (fun x : nat => nth x (a :: a0 :: l0) a)
                    (incr_all (Id (length l0 - 0)) 2))
          with (app_nat_fun (incr_all (Id (length l0 - 0)) 2) (a :: a0 :: l0)).
        rewrite Nat.sub_0_r.
        change 2 with (length (a :: a0 :: nil)).
        change (a :: a0 :: l0) with ((a :: a0 :: nil) ++ l0).
        rewrite app_nat_fun_right; [rewrite app_Id | apply all_lt_Id]...
    + destruct l0; try now (exfalso; apply Hnnil).
      assert (forall n i, transpo (S n) (S i) = 0 :: incr_all (transpo n i) 1) as transpo_S.
      { clear.
        intros n i.
        unfold transpo.
        case_eq (i <? n); intros Hcase.
        - replace (S i <? S n) with true...
          rewrite incr_all_app.
          simpl.
          rewrite<- incr_all_plus.
          replace (S (S i) + 1) with (S (S (S i))) by lia...
        - replace (S i <? S n) with false... }
      destruct l0.
      * simpl.
        apply Hskip...
      * replace (length (a :: a0 :: l0) - 1) with (S (length (a0 :: l0) - 1)) by length_lia.
        rewrite transpo_S.
        app_nat_fun_unfold (incr_all (transpo (length (a0 :: l0) - 1) i) 1) (a0 :: l0) 0 a.
        change 1 with (length (a :: nil)) at 2...
        change (a :: a0 :: l0) with ((a :: nil) ++ a0 :: l0) at 3.
        rewrite app_nat_fun_right.
        2:{ replace (length (a0 :: l0)) with (S (length (a0 :: l0) - 1)) at 2 by length_lia.
            apply all_lt_transpo. }
        apply Hskip.
        -- split with (transpo (length (a0 :: l0) - 1) i).
           repeat split...
           ++ apply transpo_is_perm.
           ++ length_lia.
        -- apply IHi.
           intros H; inversion H.
  - clear l l' p Hperm Hlen Heq.
    intros f1 f2 l Hperm1 Hperm2 Hlen1 Hlen2 IH1 IH2 _.
    specialize_hyps.
    apply Htrans with (app_nat_fun f1 l)...
    + split with f1.
      repeat split...
      symmetry...
    + split with f2.
      repeat split...
      * rewrite Hlen2.
        destruct l; [destruct f1; try now inversion Hlen1 | ]...
        rewrite app_nat_fun_length...
        intro H; inversion H.
      * rewrite asso_app_nat_fun...
    + rewrite asso_app_nat_fun...    
Qed.

Ltac rect_transpo P Hperm :=
  let x := fresh "x" in
  let y := fresh "y" in
  let la := fresh "la" in
  let lb := fresh "lb" in
  let lc := fresh "lc" in
  let Hperm1 := fresh "Hperm1" in
  let IHHperm1 := fresh "IHHperm1" in
  let Hperm2 := fresh "Hperm2" in
  let IHHperm2 := fresh "IHHperm2" in
  refine (Perm_R_rect_transpo P  _ _ _ _ Hperm); clear Hperm; [ | intros x la lb Hperm1 IHHperm1 | intros x y la | intros la lb lc Hperm1 IHHperm1 Hperm2 IHHperm2].
  

Theorem Perm_R_ind_transpo {A} :
 forall P : list A -> list A -> Prop,
   P nil nil ->
   (forall x l l', Perm_R l l' -> P l l' -> P (x :: l) (x :: l')) ->
   (forall x y l, P (y :: x :: l) (x :: y :: l)) ->
   (forall l l' l'', Perm_R l l' -> P l l' -> Perm_R l' l'' -> P l' l'' -> P l l'') ->
   forall l l', Perm_R l l' -> P l l'.
Proof with try assumption.
  intros P Hnil Hskip Hswap Htrans l l' Hperm.
  apply Perm_R_rect_transpo...
Qed.

Ltac ind_transpo P Hperm :=
  let x := fresh "x" in
  let y := fresh "y" in
  let la := fresh "la" in
  let lb := fresh "lb" in
  let lc := fresh "lc" in
  let Hperm1 := fresh "Hperm1" in
  let IHHperm1 := fresh "IHHperm1" in
  let Hperm2 := fresh "Hperm2" in
  let IHHperm2 := fresh "IHHperm2" in
  refine (Perm_R_rect_transpo P  _ _ _ _ Hperm); clear Hperm; [ | intros x la lb Hperm1 IHHperm1 | intros x y la | intros la lb lc Hperm1 IHHperm1 Hperm2 IHHperm2].

Theorem Perm_R_ind_transpo_bis {A} :
 forall P : list A -> list A -> Prop,
   P nil nil ->
   (forall x l l', Perm_R l l' -> P l l' -> P (x :: l) (x :: l')) ->
   (forall x y l l', Perm_R l l' -> P l l' -> P (y :: x :: l) (x :: y :: l')) ->
   (forall l l' l'', Perm_R l l' -> P l l' -> Perm_R l' l'' -> P l' l'' -> P l l'') ->
   forall l l', Perm_R l l' -> P l l'.
Proof.
  intros P Hnil Hskip Hswap Htrans.
  assert (forall l, P l l).
  { induction l; auto. }
  apply Perm_R_ind_transpo.
  - apply Hnil.
  - apply Hskip.
  - intros x y l.
    apply Hswap; auto.
  - apply Htrans.
Qed.

Ltac ind_transpo_bis P Hperm :=
  let x := fresh "x" in
  let y := fresh "y" in
  let la := fresh "la" in
  let lb := fresh "lb" in
  let lc := fresh "lc" in
  let Hperm1 := fresh "Hperm1" in
  let IHHperm1 := fresh "IHHperm1" in
  let Hperm2 := fresh "Hperm2" in
  let IHHperm2 := fresh "IHHperm2" in
  refine (Perm_R_ind_transpo_bis P  _ _ _ _ Hperm); clear Hperm; [ | intros x la lb Hperm1 IHHperm1 | intros x y la | intros la lb lc Hperm1 IHHperm1 Hperm2 IHHperm2].

Theorem Perm_R_rect_transpo_bis {A} :
 forall P : list A -> list A -> Type,
   P nil nil ->
   (forall x l l', Perm_R l l' -> P l l' -> P (x :: l) (x :: l')) ->
   (forall x y l l', Perm_R l l' -> P l l' -> P (y :: x :: l) (x :: y :: l')) ->
   (forall l l' l'', Perm_R l l' -> P l l' -> Perm_R l' l'' -> P l' l'' -> P l l'') ->
   forall l l', Perm_R l l' -> P l l'.
Proof.
  intros P Hnil Hskip Hswap Htrans.
  assert (forall l, P l l).
  { induction l; auto. }
  apply Perm_R_rect_transpo.
  - apply Hnil.
  - apply Hskip.
  - intros x y l.
    apply Hswap; auto.
  - apply Htrans.
Qed.

Ltac rect_transpo_bis P Hperm :=
  let x := fresh "x" in
  let y := fresh "y" in
  let la := fresh "la" in
  let lb := fresh "lb" in
  let lc := fresh "lc" in
  let Hperm1 := fresh "Hperm1" in
  let IHHperm1 := fresh "IHHperm1" in
  let Hperm2 := fresh "Hperm2" in
  let IHHperm2 := fresh "IHHperm2" in
  refine (Perm_R_rect_transpo_bis P _ _ _ _ Hperm); clear Hperm; [ | intros x la lb Hperm1 IHHperm1 | intros x y la | intros la lb lc Hperm1 IHHperm1 Hperm2 IHHperm2].


(* PERMUTATION_TYPE = PERM_R *)
Require Import Permutation_Type_solve.

Lemma Permutation_Type_to_Perm_R {A} : forall l1 (l2 : list A),
    Permutation_Type l1 l2 ->
    Perm_R l1 l2.
Proof with try reflexivity; try assumption.
  intros l1 l2 Hp.
  induction Hp.
  - split with (Id 0).
    repeat split...
  - apply Perm_R_skip...
  - apply Perm_R_swap...
  - apply Perm_R_trans with l'...
Defined.

Lemma Perm_R_to_Permutation_Type {A} : forall (l1 : list A) l2,
    Perm_R l1 l2 ->
    Permutation_Type l1 l2.
Proof with try reflexivity; try assumption.
  intros l1 l2 Hperm.
  apply Perm_R_rect_transpo; try now (intros; constructor)...
  clear.
  intros l l' l'' _ Hperm1 _ Hperm2.
  transitivity l'...
Qed.
