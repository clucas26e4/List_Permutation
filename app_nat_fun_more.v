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

Lemma app_antecedent_dflt {A} : forall (d a : A) f l l1 l2,
    app_nat_fun_dflt f l d = l1 ++ a :: l2 ->
    nth (nth (length l1) f 0) l d = a.
Proof.
  intros d a f l l1.
  revert d a f l.
  induction l1; intros d b f l l2 Heq.
  - simpl in *.
    destruct f; destruct l; try now inversion Heq.
  - destruct f; [ destruct l; inversion Heq | ].
    simpl.
    apply IHl1 with l2; try assumption.
    destruct l; try now inversion Heq.
Qed.

Lemma app_antecedent {A} : forall (a : A) f l l1 l2,
    app_nat_fun f l = l1 ++ a :: l2 ->
    nth (nth (length l1) f 0) l (hd a l) = a.
Proof.
  intros a f l l1 l2 Heq.
  apply app_antecedent_dflt with l2; try assumption.
  destruct l; [ destruct l1; inversion Heq | ].
  apply Heq.
Qed.

Lemma app_nat_fun_vs_elt_inv {A} :
  forall (a : A) f l l1 l2,
    app_nat_fun f l = l1 ++ a :: l2 ->
    {' (la, lb) : _ & l = la ++ a :: lb }.
Proof with try reflexivity; try assumption.
  intros a f l l1 l2 Heq.
  case_eq (nth (length l1) f 0 <? length l); intro H ; [apply Nat.ltb_lt in H | apply Nat.ltb_nlt in H].
  - destruct (nth_split_Type (nth (length l1) f 0) l (hd a l)) as [[la lb] Heql Hlen]; [ apply H | ].
    split with (la, lb).
    rewrite app_antecedent with _ _ _ _ l2 in Heql...
  - destruct l; [destruct l1; inversion Heq | ].
    split with (nil, l).
    rewrite<- app_antecedent with a f (a0 :: l) l1 l2...
    rewrite nth_overflow...
    lia.
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
    unfold app_nat_fun_dflt; rewrite map_map.
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

