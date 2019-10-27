(* Action of List nat over a list of arbitary elements. 
   Identity function and cfun functions (circular shifts). *)

Require Import Lia.
Require Import PeanoNat.

Require Import Injective.
Require Import Bool_more.
Require Import List_more.
Require Import List_Type_more.

Require Import List_nat.



(* APP_NAT_FUN *)
Definition app_nat_fun_dflt {A} p (l : list A) a := map (fun x => nth x l a) p.

Lemma app_nat_fun_dflt_indep {A} :
 forall p l (d d' : A), all_lt p (length l) = true -> app_nat_fun_dflt p l d = app_nat_fun_dflt p l d'.
Proof.
induction p; intros l d d' Hlt; simpl; f_equal; simpl in Hlt; apply andb_true_iff in Hlt.
- apply nth_indep, Nat.ltb_lt, Hlt.
- apply IHp, Hlt.
Qed.

Lemma app_nat_fun_dflt_nil {A} : forall p (d : A),
  app_nat_fun_dflt p nil d = map (fun _ => d) p.
Proof.
  intros p d; induction p; [ reflexivity | ].
  simpl; rewrite IHp.
  f_equal; destruct a; reflexivity.
Qed.

Definition app_nat_fun {A} (p : list nat) (l : list A) :=
  match l with
  | nil => nil
  | a :: l => app_nat_fun_dflt p (a :: l) a
  end.

Infix "∘" := app_nat_fun (at level 65).

Ltac app_nat_fun_dflt_unfold l1 l2 n a d :=
  change (app_nat_fun_dflt (n :: l1) (a :: l2) d)
  with (nth n (a :: l2) a :: app_nat_fun_dflt l1 (a :: l2) d) in *.
Ltac app_nat_fun_unfold l1 l2 n a :=
  change (app_nat_fun (n :: l1) (a :: l2)) with (nth n (a :: l2) a :: app_nat_fun l1 (a :: l2)) in *.

Lemma app_nat_fun_nil {A} : forall (l : list A), nil ∘ l = nil.
Proof. destruct l; reflexivity. Qed.

Lemma app_nat_fun_not_nil {A} : forall p (l : list A) a,
  l <> nil -> p ∘ l = app_nat_fun_dflt p l (hd a l).
Proof. intros p l a Hnil; destruct l; [ contradiction Hnil | ]; reflexivity. Qed.

Lemma app_nat_fun_cons {A} : forall n (a : A) p l,
  n :: p ∘ a :: l = nth n (a :: l) a :: (p ∘ a :: l).
Proof. intros n a p l; unfold app_nat_fun; app_nat_fun_dflt_unfold p l n a a; reflexivity. Qed.

Lemma app_nat_fun_app_nat_fun_dflt {A} : forall p (l : list A) d,
  all_lt p (length l) = true -> p ∘ l = app_nat_fun_dflt p l d.
Proof.
intros p l d Hlen.
destruct l.
- destruct p.
  + reflexivity.
  + exfalso.
    apply andb_true_iff in Hlen as [Hlen _].
    apply Nat.ltb_lt in Hlen; simpl in Hlen; lia.
- now apply app_nat_fun_dflt_indep.
Qed.

Lemma app_nat_fun_middle {A} : forall l1 l2 (a : A) p,
  length l1 :: p ∘ l1 ++ a :: l2 = a :: (p ∘ l1 ++ a :: l2).
Proof.
  intros l1 l2 a0 p.
  destruct l1; [ reflexivity | ].
  change (length (a :: l1) :: p ∘ (a :: l1) ++ a0 :: l2)
    with (nth (length (a :: l1)) ((a :: l1) ++ a0 :: l2) a :: (p ∘ (a :: l1) ++ a0 :: l2)).
  replace a0 with (nth (length (a :: l1)) ((a :: l1) ++ a0 :: l2) a);
    f_equal; apply nth_middle.
Qed.

Lemma app_nat_fun_length_cons {A} : forall f (l : list A), l <> nil -> length (f ∘ l) = length f.
Proof. intros f l Hnnil; destruct l; [ exfalso; apply Hnnil; reflexivity | apply map_length ]. Qed.

Lemma app_nat_fun_length {A} : forall f (l : list A), length f = length l -> length (f ∘ l) = length f.
Proof.
intros f l Heq; destruct l.
- rewrite Heq; reflexivity.
- apply app_nat_fun_length_cons; intros Heq2; inversion Heq2.
Qed.

Lemma all_lt_app_nat_fun : forall p l n, all_lt p (length l) = true ->
  all_lt l n = true -> all_lt (p ∘ l) n = true.
Proof.
induction p; intros l n Hl Halt.
- rewrite app_nat_fun_nil; reflexivity.
- simpl in Hl; apply andb_true_iff in Hl as [Hl1 Hl2].
  destruct l; [ apply Nat.ltb_lt in Hl1; simpl in Hl1; lia | ].
  simpl in Halt; apply andb_true_iff in Halt as [Halt1 Halt2].
  simpl; apply andb_true_iff; split.
  + destruct a; [ assumption | ].
    apply Nat.ltb_lt.
    apply cond_all_lt_inv; [ | assumption ].
    apply Nat.ltb_lt in Hl1; simpl in Hl1; lia.
  + fold (p ∘ (n0 :: l)).
    apply IHp; [ | apply andb_true_iff; split ]; assumption.
Qed.

Lemma app_nat_fun_dflt_shift {A} : forall (la lb lc : list A) p d, length (la ++ lc) <> 0 ->
  app_nat_fun_dflt (shift p (length la) (length lb)) (la ++ lb ++ lc) d = app_nat_fun_dflt p (la ++ lc) d.
Proof.
  intros la lb lc p d Hlen.
  induction p; simpl; [ reflexivity | ].
  rewrite <- IHp.
  case_eq (a <? length la); intros Ha0; subst; list_simpl; f_equal.
  - now rewrite 2 app_nth1; try (apply Nat.ltb_lt; assumption).
  - apply Nat.ltb_ge in Ha0.
    rewrite app_nth2; try lia.
    replace (length lb + a - length la) with (length lb + (a - length la)) by lia.
    rewrite nth_plus.
    now rewrite <- app_nth2; try lia.
Qed.

Lemma app_nat_fun_shift {A} : forall (la lb lc :list A) p,
  length (la ++ lc) <> 0 -> all_lt p (length (la ++ lc)) = true ->
    shift p (length la) (length lb) ∘ la ++ lb ++ lc = p ∘ la ++ lc.
Proof.
  intros la lb lc p Hlen Hlt.
  destruct la; [ destruct lc | ].
  - exfalso.
    now apply Hlen.
  - rewrite 2 app_nat_fun_not_nil with _ _ a.
    + replace (app_nat_fun_dflt p (nil ++ a :: lc) (hd a (nil ++ a :: lc)))
        with (app_nat_fun_dflt p (nil ++ a :: lc) (hd a (nil ++ lb ++ a :: lc))).
      * apply app_nat_fun_dflt_shift; assumption.
      * apply app_nat_fun_dflt_indep; assumption.
    + intro Heq; inversion Heq.
    + intros Heq; destruct lb; inversion Heq.
  - simpl app_nat_fun.
    change (S (length la)) with (length (a :: la)).
    change (a :: la ++ lb ++ lc) with ((a :: la) ++ lb ++ lc).
    change (a :: la ++ lc) with ((a :: la) ++ lc).
    now apply app_nat_fun_dflt_shift.
Qed.

Lemma app_nat_fun_dflt_downshift {A} : forall la lb (a : A) p d, In_nat_bool (length la) p = false ->
  app_nat_fun_dflt p (la ++ a :: lb) d = app_nat_fun_dflt (downshift p (length la)) (la ++ lb) d.
Proof.
  intros la lb a p d Hlen.
  induction p; simpl; [ reflexivity | ].
  simpl in Hlen; apply orb_false_iff in Hlen as [Hl Hr].
  rewrite Nat.eqb_sym in Hl; rewrite Hl.
  rewrite IHp; [ | apply Hr ].
  case_eq (a0 <? length la); intros Ha0; subst; list_simpl; f_equal.
  - rewrite 2 app_nth1; try (apply Nat.ltb_lt; assumption).
    reflexivity.
  - apply Nat.ltb_ge in Ha0.
    rewrite app_nth2 by lia.
    apply Nat.eqb_neq in Hl.
    rewrite app_nth2 by lia.
    simpl; f_equal.
    replace (Init.Nat.pred a0 - length la) with (Init.Nat.pred (a0 - length la)) by lia.
    assert (a0 - length la > 0) as Hnz by lia.
    remember (a0 - length la) as n; clear - Hnz.
    destruct n; [ inversion Hnz | reflexivity ].
Qed.

Lemma app_nat_fun_downshift {A} : forall la lb (a : A) p,
  In_nat_bool (length la) p = false -> all_lt p (S (length (la ++ lb))) = true ->
    p ∘ la ++ a :: lb = downshift p (length la) ∘ la ++ lb.
Proof.
intros la lb a p Hlen Hlt.
case_eq p.
- intros Hp; subst.
  rewrite 2 app_nat_fun_nil; reflexivity.
- intros x l Hl; rewrite <- Hl in *.
  rewrite 2 app_nat_fun_not_nil with _ _ a.
  + replace (app_nat_fun_dflt p (la ++ a :: lb) (hd a (la ++ a :: lb)))
       with (app_nat_fun_dflt p (la ++ a :: lb) (hd a (la ++ lb))).
    * apply app_nat_fun_dflt_downshift; assumption.
    * apply app_nat_fun_dflt_indep.
      rewrite app_length in *; simpl.
      rewrite <- Hlt; f_equal; lia.
  + intros Heq; subst.
    rewrite Heq in Hlt; simpl in Hlt.
    apply app_eq_nil in Heq.
    destruct Heq as [Heq _]; subst; simpl in Hlen.
    apply andb_true_iff in Hlt.
    apply orb_false_iff in Hlen.
    destruct Hlt as [Hlt _]; destruct Hlen as [Hlen _].
    destruct x; [ inversion Hlen | inversion Hlt].
  + intros Heq; destruct la; inversion Heq.
Qed.

Lemma app_nat_fun_dflt_downshift_commu : forall l f k d,
  all_lt f (length l) = true ->
  In_nat_bool k l = false ->
  app_nat_fun_dflt f (downshift l k) d = downshift (app_nat_fun_dflt f l d) k.
Proof.
intros l f; revert l.
induction f; intros l k d Hlt Hnin; [ reflexivity | ].
simpl in Hlt; apply andb_true_iff in Hlt; destruct Hlt as [Hlt Hlt'].
simpl app_nat_fun_dflt; simpl downshift.
replace (beq_nat (nth a l d) k) with false.
- case_eq (nth a l d <? k); intros Hlt2.
  + rewrite IHf; [ f_equal | assumption | assumption ].
    apply Nat.ltb_lt in Hlt2.
    apply nth_downshift_lt; assumption.
  + rewrite IHf; [ f_equal | assumption | assumption ].
    apply Nat.ltb_ge in Hlt2.
    rewrite nth_indep with _ _ _ _ (pred d) by (now apply Nat.ltb_lt in Hlt; rewrite downshift_length; try lia).
    now apply nth_downshift_ge.
- apply Nat.ltb_lt in Hlt.
  clear - Hlt Hnin; revert a Hlt; induction l; intros b Hlt.
  + exfalso; simpl in Hlt; inversion Hlt.
  + simpl in Hnin; apply orb_false_iff in Hnin; destruct Hnin as [Hnin1 Hnin2].
    destruct b; simpl.
    * symmetry; apply Nat.eqb_neq; intros H; subst; apply Nat.eqb_neq in Hnin1; auto.
    * simpl in Hlt; apply IHl; [assumption | lia].
Qed.

Lemma app_nat_fun_downshift_commu : forall a l f k,
  In_nat_bool k (a :: l) = false -> all_lt f (length (a :: l)) = true ->
  f ∘ downshift (a :: l) k = downshift (f ∘ a :: l) k.
Proof.
intros a l f k Hlen Hnin.
rewrite 2 app_nat_fun_not_nil with _ _ 0.
- rewrite app_nat_fun_dflt_downshift_commu; auto.
  f_equal; apply app_nat_fun_dflt_indep; assumption.
- intros H; inversion H.
- intros H; simpl in H.
  simpl in Hlen; apply orb_false_iff in Hlen; destruct Hlen as [Hlen _].
  rewrite Nat.eqb_sym in Hlen; rewrite Hlen in H.
  inversion H.
Qed.

Lemma asso_app_nat_fun_dflt {A} : forall l1 l2 (l3 : list A) n d,
   app_nat_fun_dflt (app_nat_fun_dflt l1 l2 n) l3 d
 = app_nat_fun_dflt l1 (app_nat_fun_dflt l2 l3 d) (nth n l3 d).
Proof.
intros l1 l2 l3 n d; unfold app_nat_fun_dflt.
rewrite map_map.
apply map_ext; intros x.
revert l2; induction x; intros l2; destruct l2; simpl; try reflexivity.
rewrite IHx; reflexivity.
Qed.

Lemma asso_app_nat_fun {A} : forall l1 l2 (l3 : list A), (l1 ∘ l2) ∘ l3 = l1 ∘ (l2 ∘ l3).
Proof.
intros l1 l2 l3.
destruct l3; [ reflexivity | ].
destruct l2; [ reflexivity | ].
unfold app_nat_fun.
remember (app_nat_fun_dflt (n :: l2) (a :: l3) a) as l.
destruct l.
- exfalso.
  destruct n; simpl in Heql; inversion Heql.
- rewrite Heql.
  replace a0 with (nth n (a :: l3) a) by (destruct n; simpl in Heql; simpl; now inversion Heql).
  apply asso_app_nat_fun_dflt.
Qed.

Lemma app_nat_fun_dflt_right {A} : forall (l1 l2 : list A) f d,
  app_nat_fun_dflt (incr_all f (length l1)) (l1 ++ l2) d = app_nat_fun_dflt f l2 d.
Proof.
intros l1 l2 f; revert l1 l2; induction f; intros l1 l2 d; [ reflexivity | ].
simpl; rewrite IHf.
f_equal.
rewrite app_nth2; f_equal; lia.
Qed.

Lemma app_nat_fun_right {A} : forall k (l1 l2 : list A) f, k = length l1 -> all_lt f (length l2) = true ->
  incr_all f k ∘ l1 ++ l2 = f ∘ l2.
Proof.
intros k l1 l2 f Heq Hlen; subst.
induction l1; simpl.
- now rewrite shift_0.
- change (S (length l1)) with (length (a :: l1)).
  rewrite app_comm_cons.
  rewrite app_nat_fun_dflt_right.
  now symmetry; apply app_nat_fun_app_nat_fun_dflt.
Qed.

Lemma app_nat_fun_dflt_left {A} : forall (l1 l2 : list A) f d1 d2, all_lt f (length l1) = true ->
   app_nat_fun_dflt f (l1 ++ l2) d1 = app_nat_fun_dflt f l1 d2.
Proof.
intros l1 l2 f d1 d2 Hlen.
unfold app_nat_fun_dflt.
apply map_ext_in; intros x Hin.
assert (x < length l1) as Hx.
{ revert Hlen Hin; induction f; intros Hlen Hin; inversion Hin; subst.
  - apply andb_true_iff in Hlen as [Hlen _].
    now apply Nat.ltb_lt.
  - apply IHf; try assumption.
    now apply andb_true_iff in Hlen as [_ Hlen]. }
rewrite app_nth1; [ | apply Hx ].
apply nth_indep, Hx.
Qed.

Lemma app_nat_fun_left {A} : forall (l1 l2 : list A) f, all_lt f (length l1) = true ->
  f ∘ l1 ++ l2 = f ∘ l1.
Proof.
intros l1 l2 f Hlen.
destruct l2; [ list_simpl; reflexivity | ].
rewrite 2 app_nat_fun_app_nat_fun_dflt with _ _ a.
- now apply app_nat_fun_dflt_left.
- assumption.
- apply all_lt_leq with (length l1); [ assumption | rewrite app_length; lia ].
Qed.

Lemma app_nat_fun_dflt_app {A} : forall (l : list A) f1 f2 d,
  app_nat_fun_dflt (f1 ++ f2) l d = app_nat_fun_dflt f1 l d ++ app_nat_fun_dflt f2 l d.
Proof. intros l f1 f2 d; apply map_app. Qed.

Lemma app_nat_fun_app {A} : forall (l : list A) f1 f2, f1 ++ f2 ∘ l = (f1 ∘ l) ++ (f2 ∘ l).
Proof. intros l f1 f2; destruct l; [ reflexivity | apply app_nat_fun_dflt_app ]. Qed.

Lemma append_fun_eq {A} : forall (l1 l2 : list A) f1 f2,
  all_lt f1 (length l1) = true -> all_lt f2 (length l2) = true ->
  f1 ++ incr_all f2 (length l1) ∘ l1 ++ l2 = (f1 ∘ l1) ++ (f2 ∘ l2).
Proof. intros; now rewrite app_nat_fun_app; f_equal; [ apply app_nat_fun_left | apply app_nat_fun_right ]. Qed.

Lemma pappend_fun_eq {A} : forall (l1 l2 : list A) f1 f2, length f1 = length l1 ->
  all_lt f1 (length f1) = true -> all_lt f2 (length l2) = true ->
  f1 +++ f2 ∘ l1 ++ l2 = (f1 ∘ l1) ++ (f2 ∘ l2).
Proof. intros l1 l2 f1 f2 Hlen Hlt1 Hlt2; now rewrite <- append_fun_eq; rewrite_all Hlen. Qed.

Lemma app_nat_fun_downshift_shift : forall l f n0 n,
  all_distinct l = true -> all_distinct f = true ->
  all_lt f (pred (length l)) = true -> n < length l ->
  f ∘ downshift l (nth n l n0) = downshift (shift f n 1 ∘ l) (nth n l n0).
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
      change (shift (a :: f) 0 1) with (S a :: (shift f 0 1)).
      unfold app_nat_fun at 2.
      app_nat_fun_dflt_unfold (shift f 0 1) (@nil nat) (S a) (nth 0 l n0) (nth 0 l n0).
      replace (nth (S a) (nth 0 l n0 :: nil) (nth 0 l n0)) with (nth 0 l n0) by now destruct a.
      rewrite downshift_eq... }
    rewrite <- Hlenla.
    change (nil ++ nth (length nil) l n0 :: n1 :: lb) with
        (nil ++ (nth (@length nat nil) l n0 :: nil) ++ (n1 :: lb)).
    change 1 with (length (nth (@length nat nil) l n0 :: nil)).
    rewrite app_nat_fun_shift by now try (intros H; inversion H).
    rewrite 2 app_nil_l; simpl app.
    rewrite downshift_eq.
    apply app_nat_fun_downshift_commu...
    apply all_distinct_right with (@nil nat).
    rewrite Hlenla.
    rewrite <- Heql...
  - simpl in Hal.
    rewrite <- Hlenla.
    change 1 with (length (nth (length (n1 :: la)) l n0 :: nil)).
    change ((n1 :: la) ++ nth (length (n1 :: la)) l n0 :: lb)
      with ((n1 :: la) ++ (nth (length (n1 :: la)) l n0 :: nil) ++ lb).
    rewrite app_nat_fun_shift.
    + rewrite downshift_app.
      change ((nth (length (n1 :: la)) l n0 :: nil) ++ lb) with (nth (length (n1 :: la)) l n0 :: lb).
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
        rewrite app_length in Hal |- *; simpl in Hal.
        rewrite Nat.add_succ_r in Hal...
    + intros H; inversion H.
    + simpl.
      rewrite app_length in Hal |- * ; simpl in Hal.
      rewrite Nat.add_succ_r in Hal...
Qed.

Lemma app_nat_fun_incr_all : forall n l p, p ∘ incr_all l n = incr_all (p ∘ l) n.
Proof with try reflexivity.
  intros n l p.
  destruct l...
  induction p...
  change (shift (n0 :: l) 0 n) with (n + n0 :: shift l 0 n).
  unfold app_nat_fun.
  app_nat_fun_dflt_unfold p (shift l 0 n) a (n + n0) (n + n0).
  app_nat_fun_dflt_unfold p l a n0 n0.
  simpl in IHp.
  rewrite IHp.
  change (n + n0 :: shift l 0 n) with (shift (n0 :: l) 0 n).
  rewrite nth_incr_all...
Qed.

Lemma In_nat_bool_shift_false : forall l f n0 n,
    all_lt f (pred (length l)) = true ->
    n < length l ->
    all_distinct l = true ->
    In_nat_bool (nth n l n0) (shift f n 1 ∘ l) = false.
Proof with try reflexivity; try assumption.
  intros l f n0 n Hal Hlen Had.
  destruct l; try now inversion Hlen.
  induction f...
  simpl shift.
  simpl in Hal.
  apply andb_prop in Hal as (Hlt & Hal).
  case_eq (a <? n); intros Hlt'.
  - apply orb_false_iff.
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
  - apply orb_false_iff.
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

Lemma app_nat_fun_map {A B} : forall (f : A -> B) l p, p ∘ map f l = map f (p ∘ l).
Proof with try reflexivity.
  intros f l p.
  destruct l...
  induction p...
  rewrite map_cons.
  unfold app_nat_fun; app_nat_fun_dflt_unfold p (map f l) a0 (f a) (f a).
  rewrite<- ? map_cons.
  simpl in IHp.
  simpl map at 2.
  rewrite IHp.
  app_nat_fun_dflt_unfold p l a0 a a.
  rewrite map_nth...
Qed.


(* ID *)
Notation Id := (seq 0).

Lemma incr_all_seq : forall s l k, incr_all (seq s l) k = seq (s + k) l.
Proof.
intros s l k.
revert s; induction l; intros s; simpl; [ reflexivity | ].
f_equal; [ lia | apply IHl ].
Qed.

Lemma all_lt_seq : forall s l k, s + l <= k -> all_lt (seq s l) k = true.
Proof.
intros s l k Hle.
apply all_lt_Forall, Forall_forall.
intros x Hin.
apply in_seq in Hin; lia.
Qed.

Lemma all_distinct_seq : forall s l, all_distinct (seq s l) = true.
Proof. intros; apply all_distinct_NoDup, seq_NoDup. Qed.

Lemma app_nat_fun_seq_seq : forall i j k n, k + n <= j -> seq k n ∘ seq i j = seq (i + k) n.
Proof.
intros i j k n; revert i k; induction n; intros i k Hlt; simpl.
- apply app_nat_fun_nil.
- replace j with (S (j - 1)) by lia.
  simpl seq.
  rewrite app_nat_fun_cons; f_equal.
  + rewrite seq_cons, seq_nth; lia.
  + replace (S (i + k)) with (i + S k) by lia.
    rewrite <- IHn; [ | lia ].
    f_equal; rewrite seq_cons; f_equal; lia.
Qed.

Lemma app_Id {A} : forall (l : list A), Id (length l) ∘ l = l.
Proof.
  induction l; [ reflexivity | ].
  simpl; unfold app_nat_fun_dflt; f_equal.
  rewrite <- seq_shift.
  rewrite map_map.
  etransitivity; [ | apply IHl ].
  unfold app_nat_fun; destruct l; [ reflexivity | ].
  apply map_ext_in; intros x Hin.
  simpl; destruct x; [reflexivity | apply nth_indep].
  apply in_seq in Hin; simpl in Hin; lia.
Qed.

Lemma app_Id_ext {A} : forall k (l1 l2 : list A), length l1 = k -> Id k ∘ l1 ++ l2 = l1.
Proof.
intros k l1 l2 Heq.
rewrite <- Heq.
rewrite app_nat_fun_left; [ apply app_Id | apply all_lt_seq; lia ].
Qed.

Lemma app_nat_fun_Id_r : forall f k, all_lt f k = true -> f ∘ Id k = f.
Proof.
induction f; intros k Hlen.
- apply app_nat_fun_nil.
- simpl in Hlen; apply andb_true_iff in Hlen as [Hlen1 Hlen2]; apply Nat.ltb_lt in Hlen1.
  destruct k; [ lia | ].
  apply IHf in Hlen2; simpl in Hlen2.
  simpl; destruct a; f_equal; try assumption.
  rewrite seq_nth; lia.
Qed.


(* CFUN *)
Definition cfun n m := seq n m ++ seq 0 n.

Lemma cfun_length : forall n m, length (cfun n m) = n + m.
Proof. intros; unfold cfun; rewrite app_length; rewrite 2 seq_length; lia. Qed.

Lemma all_lt_cfun : forall n m, all_lt (cfun n m) (n + m) = true.
Proof.
intros n m.
unfold cfun; rewrite all_lt_app.
apply andb_true_iff; split; apply all_lt_seq; lia.
Qed.

Lemma all_distinct_cfun : forall n m, all_distinct (cfun n m) = true.
Proof.
  intros n m.
  unfold cfun.
  rewrite all_distinct_app_commu.
  rewrite <- seq_app.
  apply all_distinct_seq.
Qed.

Lemma app_cfun_eq {A} : forall (l1 : list A) l2, cfun (length l1) (length l2) ∘ l1 ++ l2 = l2 ++ l1.
Proof.
intros l1 l2.
unfold cfun.
rewrite app_nat_fun_app; f_equal.
- change (length l1) with (0 + length l1).
  rewrite <- incr_all_seq.
  rewrite app_nat_fun_right; try lia.
  + apply app_Id.
  + apply all_lt_seq; lia.
- rewrite app_nat_fun_left.
  + apply app_Id.
  + apply all_lt_seq; lia.
Qed.

Lemma cfun_c1n : forall i j,
    cfun 1 (i + j) ∘ cfun i (S j) = cfun (S i) j.
Proof.
  intros i j.
  unfold cfun at 2 3.
  rewrite <- seq_cons; simpl app; rewrite cons_is_app.
  replace (i + j) with (length (seq (S i) j ++ Id i)) by (rewrite app_length; rewrite ? seq_length; lia).
  change 1 with (length (i :: nil)).
  rewrite app_cfun_eq; rewrite<- app_assoc.
  unfold Id; now rewrite<- seq_S.
Qed.

Lemma cfun_generated_by_c1n : forall i j,
    cfun i j = Nat.iter i (app_nat_fun (cfun 1 (pred (i+j)))) (Id (i + j)).
Proof.
  induction i; intros j; [ unfold cfun; now rewrite app_nil_r | ].
  specialize (IHi (S j)); replace (i + S j) with (S i + j) in IHi by lia.
  simpl in *; rewrite<- IHi; now rewrite cfun_c1n.
Qed.

Lemma cfun_inv : forall n m, cfun n m ∘ cfun m n = Id (m + n).
Proof.
intros n m.
change (cfun m n) with (seq m n ++ Id m).
replace (cfun n m) with (cfun (length (seq m n)) (length (Id m))).
- rewrite app_cfun_eq.
  symmetry; apply seq_app.
- rewrite 2 seq_length; reflexivity.
Qed.

Lemma cfun_cfun_le : forall i j k l, i + j = k + l -> k <= j ->
  cfun k l ∘ cfun i j = cfun (i + k) (j - k).
Proof.
intros i j k l Hlen Hlt; unfold cfun.
rewrite app_nat_fun_app.
replace j with (k + (j - k)) at 2 by lia.
rewrite 2 seq_app; rewrite <- app_assoc.
rewrite app_Id_ext by apply seq_length.
rewrite app_assoc; f_equal.
replace l with (j - k + i) by lia; rewrite seq_app.
replace (k + (j - k)) with (j - k + k) by lia; rewrite app_nat_fun_app; f_equal.
- rewrite app_nat_fun_left by (apply all_lt_seq; rewrite seq_length; lia).
  apply app_nat_fun_seq_seq; lia.
- replace (j - k + k) with j by lia.
  change j with (0 + j) at 1; rewrite <- incr_all_seq.
  rewrite app_nat_fun_right; rewrite ? seq_length; try lia.
  + replace i with (length (Id i)) at 1 by apply seq_length.
    now rewrite app_Id.
  + apply all_lt_seq; lia.
Defined.

Lemma cfun_cfun_ge : forall i j k l, i + j = k + l -> k >= j ->
  cfun k l ∘ cfun i j = cfun (k - j) (j + l).
Proof.
intros i j k l Hlen Hgt.
rewrite <- (app_Id (cfun (k - j) (j + l))), cfun_length.
replace (k - j + (j + l)) with (l + k) by lia.
rewrite <- cfun_inv, asso_app_nat_fun; f_equal.
rewrite cfun_cfun_le; [ f_equal | | ]; lia.
Defined.

Lemma cfun_cfun : forall i j k l, i + j = k + l -> {'(n, m) : _ & cfun k l ∘ cfun i j = cfun n m}.
Proof.
intros i j k l Hlen.
destruct (Compare_dec.le_lt_dec j k) as [Hle | Hgt].
- exists (k - j, j + l); now apply cfun_cfun_ge.
- exists (i + k, j - k); now apply cfun_cfun_le; try lia.
Defined.

Lemma cfun_0_n : forall n, cfun 0 n = Id n.
Proof. intros n; now unfold cfun; rewrite app_nil_r. Qed.

Lemma cfun_n_0 : forall n, cfun n 0 = Id n.
Proof. intros n; now unfold cfun. Qed.

Lemma cfun_arg_inj_S : forall n1 n2 m1 m2, cfun (S n1) (S m1) = cfun (S n2) (S m2) -> n1 = n2 /\ m1 = m2.
Proof.
intros n1 n2 m1 m2 Heq.
enough (n1 = n2 /\ n1 + m1 = n2 + m2) as [Hn Hp] by (split; lia).
unfold cfun in Heq; simpl in Heq.
split.
- now inversion Heq.
- apply (f_equal (@length _)) in Heq.
  simpl in Heq; rewrite ? app_length in Heq; simpl in Heq; rewrite ? seq_length in Heq; lia.
Qed.

Lemma cfun_arg_inj : forall n1 n2 m1 m2, (m1 = 0 -> n1 = 0) -> (m2 = 0 -> n2 = 0) ->
  cfun n1 m1 = cfun n2 m2 -> n1 = n2 /\ m1 = m2.
Proof.
intros n1 n2 m1 m2 Hz1 Hz2 Heq.
assert (n1 + m1 = n2 + m2) as Hplus by now rewrite <- 2 cfun_length; rewrite Heq.
destruct m1; [ | destruct m2 ]; try lia.
destruct n1; destruct n2; try lia.
- exfalso; unfold cfun in Heq; inversion Heq.
- exfalso; unfold cfun in Heq; inversion Heq.
- apply cfun_arg_inj_S in Heq; lia.
Qed.

Lemma nat_cfun_arg : forall n i, 0 <= i < max 1 n <-> (n = i -> i = 0) /\ i <= n.
Proof. intros; lia. Qed.
Lemma nat_cfun_args : forall i j, 0 <= i < max 1 (i + j) <-> (j = 0 -> i = 0).
Proof. intros; lia. Qed.


(* Extensionality *)

Lemma app_nat_fun_ext : forall f1 f2,
  (forall {A} (l : list A), f1 ∘ l = f2 ∘ l) -> f1 = f2.
Proof.
  intros f1 f2 H.
  specialize (H nat (Id (max (S (fold_left max f1 0)) (S (fold_left max f2 0))))).
  rewrite 2 app_nat_fun_Id_r in H; [apply H | | ];
    try eapply all_lt_leq; try apply all_lt_max; try lia.
Qed.


(* Additional properties of app_nat_fun *)

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

Lemma app_antecedent {A} : forall (a : A) f l l1 l2, f ∘ l = l1 ++ a :: l2 ->
  nth (nth (length l1) f 0) l (hd a l) = a.
Proof.
  intros a f l l1 l2 Heq.
  apply app_antecedent_dflt with l2; try assumption.
  destruct l; [ destruct l1; inversion Heq | ].
  apply Heq.
Qed.

Lemma app_nat_fun_vs_elt_inv {A} : forall (a : A) f l l1 l2,
  f ∘ l = l1 ++ a :: l2 -> {' (la, lb) : _ & l = la ++ a :: lb }.
Proof with try reflexivity; try assumption.
  intros a f l l1 l2 Heq.
  case_eq (nth (length l1) f 0 <? length l); intro H ;
    [apply Nat.ltb_lt in H | apply Nat.ltb_nlt in H].
  - destruct (nth_split_Type (nth (length l1) f 0) l (hd a l)) as [[la lb] Heql Hlen];
      [ apply H | ].
    split with (la, lb).
    rewrite app_antecedent with _ _ _ _ l2 in Heql...
  - destruct l; [destruct l1; inversion Heq | ].
    split with (nil, l).
    rewrite<- app_antecedent with a f (a0 :: l) l1 l2...
    rewrite nth_overflow...
    lia.
Qed.

Lemma app_nat_fun_vs_cons_inv {A} : forall (a : A) f l l1,
  f ∘ l = a :: l1 ->  {' (la, lb) : _ & l = la ++ a :: lb }.
Proof.
intros a f l l1 Heq; rewrite<- (app_nil_l (a :: l1)) in Heq; now apply app_nat_fun_vs_elt_inv with f nil l1.
Qed.

Lemma app_nat_fun_map_inv_inj {A B} : forall (f : A -> B), injective f -> forall g l1 l2,
  g ∘ map f l1 = map f l2 -> g ∘ l1 = l2.
Proof with try reflexivity; try assumption.
  intros f Hinj g l1 l2 Heq.
  assert (forall A B (f : A -> B) g l, app_nat_fun g (map f l) = map f (app_nat_fun g l))
    as app_nat_fun_map.
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
  g ∘ l3 ++ map f l4 = l1 ++ a :: l2 ->
  (forall b, a <> f b) -> { '(l5,l6) | l3 = l5 ++ a :: l6 }.
Proof.
intros f g a l1 l2 l3 l4 HP Hf.
apply app_nat_fun_vs_elt_inv in HP.
destruct HP as [(l',l'') Heq].
dichot_Type_elt_app_exec Heq.
- subst; exists (l', l) ; reflexivity.
- exfalso.
  decomp_map_Type Heq1.
  apply Hf in Heq1.
  inversion Heq1.
Qed.

