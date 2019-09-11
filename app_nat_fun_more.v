(* ll library for yalla *)

Require Import CMorphisms.
Require Import Lia.
Require Import PeanoNat.
Require Import EqNat.
Require Import Injective.

Require Import Bool_more.
Require Import List_Type_more.
Require Import List_more2.
Require Import List_nat.
Require Import Fun_nat.
Require Import misc.

Lemma app_nat_fun_vs_elt_inv {A} :
  forall (a : A) f l l1 l2,
    app_nat_fun f l = l1 ++ a :: l2 ->
    {' (la, lb) : _ & l = la ++ a :: lb }.
Proof with try reflexivity; try assumption.
  intros a f l l1 l2 Heq.
  destruct l.
  { exfalso.
    simpl in Heq.
    destruct l1; inversion Heq. }
  unfold app_nat_fun in Heq.
  case_eq (nth (length l1) f 0 <? length (a0 :: l)); [intro Hlt; apply Nat.ltb_lt in Hlt | intro Hnlt; apply Nat.ltb_nlt in Hnlt].
  - destruct (nth_split_Type (nth (length l1) f 0) (a0 :: l) a0) as [(la,lb) Heql Hlen]...
    split with (la , lb).
    rewrite Heql.
    replace a with (nth (nth (length l1) f 0) (a0 :: l) a0)...
    rewrite nth_nth.
    + rewrite Heq.
      apply nth_middle.
    + rewrite<- (map_length (fun x => nth x (a0 :: l) a0)).
      rewrite Heq.
      length_lia.
  - split with (nil , l).
    simpl.
    replace a with a0...
    transitivity (nth (nth (length l1) f 0) (a0 :: l) a0).
    + rewrite nth_overflow...
      length_lia.
    + rewrite nth_nth.
      * rewrite Heq.
        apply nth_middle.
      * rewrite<- (map_length (fun x => nth x (a0 :: l) a0)).
        rewrite Heq.
        length_lia.
Qed.

Lemma app_nat_fun_vs_cons_inv {A} :
  forall (a : A) f l l1,
    app_nat_fun f l = a :: l1 ->
    {' (la, lb) : _ & l = la ++ a :: lb }.
Proof with try assumption.
  intros a f l l1 Heq.
  rewrite<- (app_nil_l (a :: l1)) in Heq.
  apply app_nat_fun_vs_elt_inv with f nil l1...
Qed.

Lemma app_nat_fun_map_inv_inj {A B} :
  forall (f : A -> B),
    injective f ->
    forall g l1 l2,
      app_nat_fun g (map f l1) = map f l2 ->
      app_nat_fun g l1 = l2.
Proof with try reflexivity; try assumption.
  intros f Hinj g l1 l2 Heq.
  assert (forall A B (f : A -> B) g l, app_nat_fun g (map f l) = map f (app_nat_fun g l)) as app_nat_fun_map.
  { clear.
    intros.
    destruct l...
    change (map f (a :: l)) with (f a :: map f l).
    unfold app_nat_fun.
    rewrite map_map.
    change (f a :: map f l) with (map f (a :: l)).
    apply map_ext.
    intros x.
    rewrite map_nth... }
  rewrite app_nat_fun_map in Heq.
  apply (map_inj _ Hinj)...
Qed.

Lemma app_nat_fun_elt_map_inv {A B} : forall (f : A -> B) g a l1 l2 l3 l4,
  app_nat_fun g (l3 ++ map f l4) = l1 ++ a :: l2 ->
  (forall b, a <> f b) -> { pl | l3 = fst pl ++ a :: snd pl }.
Proof.
intros f g a l1 l2 l3 l4 HP Hf.
apply app_nat_fun_vs_elt_inv in HP.
destruct HP as ((l' & l'') & Heq).
dichot_Type_elt_app_exec Heq.
- subst.
  exists (l', l) ; reflexivity.
- exfalso.
  decomp_map_Type Heq1.
  apply Hf in Heq1.
  inversion Heq1.
Qed.