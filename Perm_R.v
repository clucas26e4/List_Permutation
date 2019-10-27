(* Definition of the relation of Perm_R and basic properties. *)

Require Import CMorphisms.
Require Import Lia.
Require Import PeanoNat.

Require Import Bool_more.
Require Import List_more.
Require Import List_Type_more.

Require Import Permutation_Type.

Require Import List_nat.
Require Import Fun_nat.
Require Import Transposition.
Require Import length_lia.
Require Import Perm.

Set Implicit Arguments.



Definition Perm_R {A} (l1 l2 : list A) : Type :=
  { p : _ & is_perm p = true & prod (length p = length l1) (l2 = app_nat_fun p l1) }.

Infix "~~" := Perm_R (at level 70).

Definition Perm_R_to_perm {A} {l1 l2 : list A} : Perm_R l1 l2 -> perm := @sigT_of_sigT2 _ _ _.
Definition Perm_R_to_perm_of {A} {l1 l2 : list A} : Perm_R l1 l2 -> perm_of (length l1) := fun P =>
  existT2 _ _ (projT1 (sigT_of_sigT2 P)) (projT2 (sigT_of_sigT2 P)) (fst (projT3 P)).
Definition Perm_R_of_perm_of {A} {l : list A} (p : perm_of (length l)) : l ~~ projT1 (sigT_of_sigT2 p) ∘ l :=
  let (p0,Hp,Hl) as s return (l ~~ projT1 (sigT_of_sigT2 s) ∘ l) := p in existT2 _ _ p0 Hp (Hl, eq_refl).

(* Permutation over lists is an equivalence relation *)

Lemma Perm_R_refl {A} : forall (l : list A), l ~~ l.
Proof.
  intro l; split with (Id (length l)); repeat split.
  - apply Id_is_perm.
  - apply seq_length.
  - symmetry; apply app_Id.
Defined.

Lemma Perm_R_trans {A} : forall (l1 l2 l3 : list A), l1 ~~ l2 -> l2 ~~ l3 -> l1 ~~ l3.
Proof.
  intros l1 l2 l3 [p1 Hperm1 [Hlen1 IHHp1]] [p2 Hperm2 [Hlen2 IHHp2]].
  assert (length p2 = length p1) by (now rewrite Hlen2, IHHp1; apply app_nat_fun_length).
  split with (app_nat_fun p2 p1); repeat split.
  - now apply compo_perm_is_perm.
  - destruct p1.
    + now destruct l1.
    + rewrite app_nat_fun_length_cons; [ lia | intros Heq; inversion Heq ].
  - rewrite asso_app_nat_fun.
    now rewrite<- IHHp1.
Defined.

Lemma Perm_R_sym {A} : forall (l1 l2 : list A), l1 ~~ l2 -> l2 ~~ l1.
Proof.
  intros l1 l2 [p Hperm [Hlen Heq]].
  destruct (perm_inv p Hperm) as [p_inv [Heq_inv _ ] [Hperm_inv Hlen_eq]].
  split with p_inv; repeat split; [ assumption | | ].
  - rewrite Heq, <- Hlen_eq.
    now symmetry; apply app_nat_fun_length.
  - rewrite Heq, <- asso_app_nat_fun, Heq_inv, Hlen.
    symmetry; apply app_Id.
Defined.

Instance Perm_R_Equivalence A : Equivalence (@Perm_R A) | 10 := {
  Equivalence_Reflexive := @Perm_R_refl A ;
  Equivalence_Symmetric := @Perm_R_sym A ;
  Equivalence_Transitive := @Perm_R_trans A }.


(* Some facts about Perm_R *)

Section Perm_R_properties.

Context {A : Type}.

Implicit Types a b : A.
Implicit Types l m : list A.

Lemma Perm_R_nil : forall l, nil ~~ l -> l = nil.
Proof. intros l Hperm; destruct Hperm as [f Hp [Hlen Heq]]; now rewrite Heq. Qed.

Lemma Perm_R_nil_cons : forall l a, nil ~~ (a :: l) -> False.
Proof. intros l a Hp; apply Perm_R_nil in Hp; inversion Hp. Qed.

Theorem Perm_R_app : forall l m l' m', l ~~ l' -> m ~~ m' -> l ++ m ~~ l' ++ m'.
Proof.
intros l m l' m' [p Hperm [Hlen Heq]] [p' Hperm' [Hlen' Heq']].
split with (p +++ p'); repeat split; subst.
- now apply append_perm_is_perm.
- length_lia.
- apply andb_prop in Hperm as [Hal _].
  apply andb_prop in Hperm' as [Hal' _]; rewrite Hlen' in Hal'.
  now symmetry; apply pappend_fun_eq.
Defined.

Global Instance Perm_R_app' : Proper (@Perm_R A ==> @Perm_R A ==> @Perm_R A) (@app A) | 10.
Proof. repeat intro; now apply Perm_R_app. Defined.

Lemma Perm_R_app_tail : forall l l' tl, l ~~ l' -> l ++ tl ~~ l' ++ tl.
Proof. intros; now apply Perm_R_app. Defined.

Lemma Perm_R_app_head : forall l tl tl', tl ~~ tl' -> l ++ tl ~~ l ++ tl'.
Proof. intros; now apply Perm_R_app. Defined.

Lemma Perm_R_skip : forall l l' a, l ~~ l' -> a :: l ~~ a :: l'.
Proof.
intros l l' a HP.
change (a :: l) with ((a :: nil) ++ l).
change (a :: l') with ((a :: nil) ++ l').
now apply Perm_R_app_head.
Defined.

Instance Perm_R_cons : Proper (Logic.eq ==> @Perm_R A ==> @Perm_R A) (@cons A) | 10.
Proof. repeat intro; subst; now apply Perm_R_skip. Defined.

Lemma Perm_R_swap : forall l a b, a :: b :: l ~~ b :: a :: l.
Proof.
intros l a b.
change (a :: b :: l) with ((a :: b :: nil) ++ l).
change (b :: a :: l) with ((b :: a :: nil) ++ l).
apply Perm_R_app_tail.
now exists (1 :: 0 :: nil); repeat split.
Defined.


(* Compatibility with others operations on lists *)

Lemma Perm_R_length : forall l m, l ~~ m -> length l = length m.
Proof. intros l m [f Hp [Hlen Heq]]; subst; now rewrite app_nat_fun_length. Qed.

Global Instance Perm_R_length' : Proper (@Perm_R A ==> Logic.eq) (@length A) | 10.
Proof. exact Perm_R_length. Qed.

Lemma Perm_R_add_inside : forall a l l' tl tl', l ~~ l' -> tl ~~ tl' -> l ++ a :: tl ~~ l' ++ a :: tl'.
Proof. intros; now apply Perm_R_app; [ | apply Perm_R_skip ]. Defined.

Theorem Perm_R_app_comm : forall l l', l ++ l' ~~ l' ++ l.
Proof.
intros l l'.
split with (cfun (length l) (length l')); repeat split.
- apply cfun_is_perm.
- length_lia.
- symmetry; apply app_cfun_eq.
Defined.

Lemma Perm_R_cons_append : forall l a, a :: l ~~ l ++ a :: nil.
Proof. intros l a; change (a :: l) with ((a :: nil) ++ l); apply Perm_R_app_comm. Defined.

Theorem Perm_R_middle : forall l1 l2 a, a :: l1 ++ l2 ~~ l1 ++ a :: l2.
Proof. intros; now rewrite Perm_R_app_comm, app_comm_cons, Perm_R_app_comm. Defined.

Theorem Perm_R_cons_app : forall l l1 l2 a, l ~~ l1 ++ l2 -> a :: l ~~ l1 ++ a :: l2.
Proof. intros l l1 l2 a Hperm; rewrite Hperm; apply Perm_R_middle. Defined.

Lemma Perm_R_Add_Type a l l' : Add_Type a l l' -> a :: l ~~ l'.
Proof. intros Hadd; induction Hadd; [ reflexivity | rewrite <- IHHadd; apply Perm_R_swap ]. Defined.

Theorem Perm_R_rev : forall l, l ~~ rev l.
Proof. induction l; [ reflexivity | simpl; rewrite <- IHl; apply Perm_R_cons_append ]. Defined.

Global Instance Perm_R_rev' : Proper (@Perm_R A ==> @Perm_R A) (@rev A) | 10.
Proof. repeat intro; now rewrite <- 2 Perm_R_rev. Defined.

Theorem Perm_R_nil_app_cons : forall l m a, nil ~~ l ++ a :: m -> False.
Proof. intros l l' a Hperm; rewrite <- Perm_R_middle in Hperm; apply (Perm_R_nil_cons Hperm). Qed.

Theorem Perm_R_cons_inv l l' a : a :: l ~~ a :: l' -> l ~~ l'.
Proof with try assumption; try reflexivity.
intros [p Hperm [Hlen Heq]].
destruct p; [ inversion Heq | ].
destruct (andb_prop _ _ Hperm) as [Hal Had].
simpl in Hal; apply andb_prop in Hal as [_ Hal].
simpl in Had; apply andb_prop in Had as [Had _]; apply negb_true_iff in Had.
destruct (app_nat_fun_vs_cons _ _ _ _ _ Hlen Hperm Heq) as [(la,lb) Heql Hlenla]; subst...
assert (S (length p) = S (length (la ++ lb))) as Hlenp by (rewrite Heql in Hlen; length_lia).
apply downshift_perm with _ (length la) in Hperm; simpl in Hperm; rewrite Nat.eqb_refl in Hperm.
injection Heq; intros Heq'' _; subst; fold (app_nat_fun p (a :: l)) in *.
rewrite Heql, app_nat_fun_downshift...
- transitivity (la ++ lb).
  + destruct la; inversion Heql; subst...
    symmetry; apply Perm_R_middle.
  + exists (downshift p (length la)); repeat split...
    rewrite downshift_length by assumption; lia.
- now rewrite <- Hlenp.
Defined.

Theorem Perm_R_Add_Type_inv a l1 l2 : Perm_R l1 l2 ->
  forall l1' l2', Add_Type a l1' l1 -> Add_Type a l2' l2 -> l1' ~~ l2'.
Proof.
intros Hperm l1' l2' Hadd1 Hadd2.
apply Perm_R_cons_inv with a.
transitivity l1; [ now apply Perm_R_Add_Type | ].
transitivity l2; [ apply Hperm | now symmetry; apply Perm_R_Add_Type ].
Defined.

Theorem Perm_R_app_inv l1 l2 l3 l4 a : l1 ++ a :: l2 ~~ l3 ++ a :: l4 -> l1 ++ l2 ~~l3 ++ l4.
Proof. intros; apply Perm_R_cons_inv with a; now rewrite 2 Perm_R_middle. Defined.

Theorem Perm_R_cons_app_inv l l1 l2 a : a :: l ~~ l1 ++ a :: l2 -> l ~~ l1 ++ l2.
Proof. intros Hperm; rewrite <- (app_nil_l l); now apply Perm_R_app_inv with a. Defined.

Theorem Perm_R_app_inv_l : forall l l1 l2, l ++ l1 ~~ l ++ l2 -> l1 ~~ l2.
Proof. now induction l; intros l1 l2 Hperm; [ | apply IHl; apply Perm_R_cons_inv with a]. Defined.

Theorem Perm_R_app_inv_r l l1 l2 : l1 ++ l ~~ l2 ++ l -> l1 ~~ l2.
Proof. intros Hperm; rewrite 2 (Perm_R_app_comm _ l) in Hperm; apply (Perm_R_app_inv_l _ _ _ Hperm). Defined.

Lemma Perm_R_length_1_inv: forall a l, a :: nil ~~ l -> l = a :: nil.
Proof.
intros a l [p Hperm [Hlen Heq]].
destruct p; try now inversion Hlen.
destruct p; try now inversion Hlen.
rewrite Heq; simpl.
now destruct n.
Qed.

Lemma Perm_R_length_1: forall a b, a :: nil ~~ b :: nil -> a = b.
Proof. intros a b Hperm; apply Perm_R_length_1_inv in Hperm; now inversion Hperm. Qed.

Lemma Perm_R_length_2_inv : forall a1 a2 l,
  a1 :: a2 :: nil ~~ l -> { l = a1 :: a2 :: nil } + { l = a2 :: a1 :: nil }.
Proof.
intros a1 a2 l [p Hperm [Hlen Heq]].
do 3 (destruct p; try now inversion Hlen).
now apply is_perm_length_2_inv in Hperm as [[Hp1 Hp2] | [Hp1 Hp2]]; subst; simpl; [left | right].
Defined.

Lemma Perm_R_length_2 : forall a1 a2 b1 b2,
  a1 :: a2 :: nil ~~ b1 :: b2 :: nil -> { a1 = b1 /\ a2 = b2 } + { a1 = b2 /\ a2 = b1 }.
Proof.
intros a1 a2 b1 b2 Hperm.
now destruct (Perm_R_length_2_inv Hperm) as [Heq | Heq]; inversion Heq; subst; [left | right].
Defined.

Theorem Perm_R_in : forall l m a, l ~~ m -> In a l -> In a m.
Proof.
intros l m a [p Hperm [Hlen Heq]] Hin.
apply In_nth with _ _ _ a in Hin as [n (Hlen' & Heq')].
rewrite <- Heq', Heq; clear Heq'.
destruct l; try now inversion Hlen'.
replace (nth n (a0 :: l) a) with (nth n (a0 :: l) a0) by (apply nth_indep; assumption).
destruct (perm_surj _ 0 n Hperm) as [i Hlen'' Heq'']; [ lia | ]; subst.
rewrite nth_nth; [ | assumption ].
apply nth_In.
now  rewrite app_nat_fun_length_cons.
Qed.

Global Instance Perm_R_in' : Proper (Logic.eq ==> @Perm_R A ==> iff) (@In A) | 10.
Proof. repeat intro; subst; split; now apply Perm_R_in. Qed.

Theorem Perm_R_in_Type : forall l m a, l ~~ m -> In_Type a l -> In_Type a m.
Proof.
intros l m a [p Hperm [Hlen Heq]] Hin.
apply In_nth_Type with _ _ a in Hin as [n Hlen' Heq'].
rewrite <- Heq', Heq; clear Heq'.
destruct l; try now simpl in Hlen'; exfalso; lia.
replace (nth n (a0 :: l) a) with (nth n (a0 :: l) a0) by (apply nth_indep; assumption).
destruct (perm_surj _ 0 n Hperm) as [i Hlen'' Heq'']; [ lia | ]; subst.
rewrite nth_nth; [ | assumption ].
apply nth_In_Type.
now  rewrite app_nat_fun_length_cons.
Qed.

Global Instance Perm_R_in_Type' : Proper (Logic.eq ==> @Perm_R A ==> Basics.arrow) (@In_Type A) | 10.
Proof. repeat intro; subst; eapply Perm_R_in_Type; eassumption. Qed.

Lemma Perm_R_concat : forall p (L : list (list A)), length p = length L -> is_perm p = true ->
  Perm_R (concat L) (concat (p ∘ L)).
Proof.
intros p L Hlen Hperm.
destruct (perm_block p L (p ∘ L) Hlen Hperm eq_refl) as [q Hpermq [Hlenq Hcomp]].
rewrite <- Hcomp.
now exists q.
Defined.

End Perm_R_properties.

Section Perm_R_map.

Variable A B : Type.
Variable f : A -> B.

Lemma Perm_R_map l l' : l ~~ l' -> map f l ~~ map f l'.
Proof.
  intros [p Hperm [Hlen Heq]].
  split with p; repeat split; [ assumption | | ].
  - now rewrite map_length.
  - now rewrite app_nat_fun_map, Heq.
Defined.

Global Instance Perm_R_map' : Proper (@Perm_R A ==> @Perm_R B) (map f) | 10.
Proof. exact Perm_R_map. Defined.

End Perm_R_map.


(* INDUCTION PRINCIPLE *)
Theorem Perm_R_rect_transpo {A} :
 forall P : list A -> list A -> Type,
   P nil nil ->
   (forall x l l', l ~~ l' -> P l l' -> P (x :: l) (x :: l')) ->
   (forall x y l, P (y :: x :: l) (x :: y :: l)) ->
   (forall l l' l'', l ~~ l' -> P l l' -> l' ~~ l'' -> P l' l'' -> P l l'') ->
   forall l l', l ~~ l' -> P l l'.
Proof with try assumption; try reflexivity.
  intros P Hnil Hskip Hswap Htrans.
  intros l l' Hperm.
  destruct Hperm as [p Hperm [Hlen Heq]].
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
        replace (app_nat_fun_dflt (seq 2 (length l0 - 0)) (a :: a0 :: l0) a)
           with l0; [apply Hswap | ].
        rewrite Nat.sub_0_r.
        change (app_nat_fun_dflt (seq 2 (length l0)) (a :: a0 :: l0) a)
          with (app_nat_fun (seq 2 (length l0)) ((a :: a0 :: nil) ++ l0)).
        replace 2 with (0 + 2) by lia.
        rewrite <- incr_all_seq.
        rewrite app_nat_fun_right; [rewrite app_Id | | apply all_lt_seq ]...
    + destruct l0; try now (exfalso; apply Hnnil).
      assert (forall n i, transpo (S n) (S i) = 0 :: incr_all (transpo n i) 1) as transpo_S.
      { clear.
        intros n i.
        unfold transpo.
        case_eq (i <? n); intros Hcase.
        - replace (S i <? S n) with true...
          rewrite shift_app.
          simpl.
          rewrite ? incr_all_seq.
          replace (S (S i) + 1) with (S (S (S i))) by lia...
        - replace (S i <? S n) with false...
          rewrite ? incr_all_seq... }
      destruct l0.
      * simpl.
        apply Hskip...
      * replace (length (a :: a0 :: l0) - 1) with (S (length (a0 :: l0) - 1)) by length_lia.
        rewrite transpo_S.
        app_nat_fun_unfold (shift (transpo (length (a0 :: l0) - 1) i) 0 1) (a0 :: l0) 0 a.
        change 1 with (length (a :: nil)) at 2...
        change (a :: a0 :: l0) with ((a :: nil) ++ a0 :: l0) at 3.
        rewrite app_nat_fun_right; [ | reflexivity | ].
        2:{ replace (length (a0 :: l0)) with (S (length (a0 :: l0) - 1)) at 2 by length_lia.
            apply all_lt_transpo. }
        apply Hskip.
        -- split with (transpo (length (a0 :: l0) - 1) i); repeat split...
           ++ apply transpo_is_perm.
           ++ length_lia.
        -- apply IHi.
           intros H; inversion H.
  - clear l l' p Hperm Hlen Heq.
    intros f1 f2 l Hperm1 Hperm2 Hlen1 Hlen2 IH1 IH2 _.
    specialize (IH1 Hperm1); specialize (IH2 Hperm2).
    apply Htrans with (app_nat_fun f1 l)...
    + split with f1; repeat split...
      symmetry...
    + split with f2; repeat split...
      * rewrite Hlen2.
        destruct l; [destruct f1; try now inversion Hlen1 | ]...
        rewrite app_nat_fun_length_cons...
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
  refine (Perm_R_rect_transpo P  _ _ _ _ Hperm); clear Hperm;
    [ | intros x la lb Hperm1 IHHperm1 | intros x y la | intros la lb lc Hperm1 IHHperm1 Hperm2 IHHperm2].

Theorem Perm_R_ind_transpo {A} :
 forall P : list A -> list A -> Prop,
   P nil nil ->
   (forall x l l', l ~~ l' -> P l l' -> P (x :: l) (x :: l')) ->
   (forall x y l, P (y :: x :: l) (x :: y :: l)) ->
   (forall l l' l'', l ~~ l' -> P l l' -> l' ~~ l'' -> P l' l'' -> P l l'') ->
   forall l l', l ~~ l' -> P l l'.
Proof. intros; now apply Perm_R_rect_transpo. Qed.

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
  refine (Perm_R_rect_transpo P  _ _ _ _ Hperm); clear Hperm;
  [ | intros x la lb Hperm1 IHHperm1 | intros x y la | intros la lb lc Hperm1 IHHperm1 Hperm2 IHHperm2].

Theorem Perm_R_rect_transpo_bis {A} :
 forall P : list A -> list A -> Type,
   P nil nil ->
   (forall x l l', l ~~ l' -> P l l' -> P (x :: l) (x :: l')) ->
   (forall x y l l', l ~~ l' -> P l l' -> P (y :: x :: l) (x :: y :: l')) ->
   (forall l l' l'', l ~~ l' -> P l l' -> l' ~~ l'' -> P l' l'' -> P l l'') ->
   forall l l', l ~~ l' -> P l l'.
Proof.
  intros P Hnil Hskip Hswap Htrans.
  assert (forall l, P l l) as Hrefl by (now induction l; [ | apply Hskip; [ reflexivity | ] ]).
  apply Perm_R_rect_transpo; try assumption.
  now intros x y l; apply Hswap.
Qed.

Theorem Perm_R_ind_transpo_bis {A} :
 forall P : list A -> list A -> Prop,
   P nil nil ->
   (forall x l l', l ~~ l' -> P l l' -> P (x :: l) (x :: l')) ->
   (forall x y l l', l ~~ l' -> P l l' -> P (y :: x :: l) (x :: y :: l')) ->
   (forall l l' l'', l ~~ l' -> P l l' -> l' ~~ l'' -> P l' l'' -> P l l'') ->
   forall l l', l ~~ l' -> P l l'.
Proof. intros; now apply Perm_R_rect_transpo_bis. Qed.

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
  refine (Perm_R_ind_transpo_bis P  _ _ _ _ Hperm); clear Hperm;
  [ | intros x la lb Hperm1 IHHperm1 | intros x y la | intros la lb lc Hperm1 IHHperm1 Hperm2 IHHperm2].


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
  refine (Perm_R_rect_transpo_bis P _ _ _ _ Hperm); clear Hperm;
  [ | intros x la lb Hperm1 IHHperm1
    | intros x y la
    | intros la lb lc Hperm1 IHHperm1 Hperm2 IHHperm2].


(* Permutation_Type = Perm_R *)

Lemma Permutation_Type_to_Perm_R {A} : forall (l1 l2 : list A),
  Permutation_Type l1 l2 -> l1 ~~ l2.
Proof.
intros l1 l2 Hp; induction Hp.
- now split with (Id 0); repeat split.
- now apply Perm_R_skip.
- now apply Perm_R_swap.
- now apply Perm_R_trans with l'.
Defined.

Lemma Perm_R_to_Permutation_Type {A} : forall (l1 l2 : list A),
  l1 ~~ l2 -> Permutation_Type l1 l2.
Proof.
intros l1 l2 Hperm.
apply Perm_R_rect_transpo; (try now (intros; constructor)); [ | assumption ].
clear; intros l l' l'' _ Hperm1 _ Hperm2.
now transitivity l'.
Qed.


(* Canonicity *)

Lemma Perm_R_eq_as_perm {A} (HdecA : forall x y : A, {x = y} + {x <> y}) :
  forall (l1 l2 : list A) (HP1 HP2: Perm_R l1 l2),
    projT1 (sigT_of_sigT2 HP1) = projT1 (sigT_of_sigT2 HP2) -> HP1 = HP2.
Proof.
intros l1 l2 [p1 Hp1 [Heql1 Heqp1]] [p2 Hp2 [Heql2 Heqp2]] Heq; simpl in Heq; subst; repeat f_equal.
- apply UIP_bool.
- apply UIP_nat.
- now apply Eqdep_dec.UIP_dec, list_eq_dec.
Qed.

