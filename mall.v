(* Multiplicative-additive fragment of Linear Logic, using Perm_R for the exchange rule. Cut-elimination theorem. *)

From Stdlib Require Import CMorphisms PeanoNat Wf_nat Lia.
From OLlibs Require Import List_more.
Require Import Perm_R_more.


Inductive formulas : Set :=
| var : nat -> formulas
| covar : nat -> formulas
| tens : formulas -> formulas -> formulas
| parr : formulas -> formulas -> formulas
| aplus : formulas -> formulas -> formulas
| awith : formulas -> formulas -> formulas.

Fixpoint fsize A :=
  match A with
  | var X => 1
  | covar X => 1
  | tens A B => S (fsize A + fsize B)
  | parr A B => S (fsize A + fsize B)
  | aplus A B => S (fsize A + fsize B)
  | awith A B => S (fsize A + fsize B)
  end.

Fixpoint dual A :=
  match A with
  | var X => covar X
  | covar X => var X
  | tens A B => parr (dual B) (dual A)
  | parr A B => tens (dual B) (dual A)
  | aplus A B => awith (dual A) (dual B)
  | awith A B => aplus (dual A) (dual B)
  end.

Lemma bidual : forall A, dual (dual A) = A.
Proof. now induction A; simpl; try rewrite IHA1; try rewrite IHA2. Qed.

Lemma fsize_dual : forall A, fsize (dual A) = fsize A.
Proof. now induction A; simpl; try rewrite IHA1; try rewrite IHA2; try lia. Qed.

Ltac fsize_lia := simpl; rewrite ? fsize_dual; lia.

Inductive mall : list formulas -> Type :=
| ax_r : forall X, mall (covar X :: var X :: nil)
| ex_r : forall l1 l2, mall l1 -> l1 ~~ l2 -> mall l2
| tens_r : forall A B l1 l2, mall (A :: l1) -> mall (B :: l2) -> mall (tens A B :: l2 ++ l1)
| parr_r : forall A B l, mall (A :: B :: l) -> mall (parr A B :: l)
| plus_r1 : forall A B l, mall (A :: l) -> mall (aplus A B :: l)
| plus_r2 : forall A B l, mall (B :: l) -> mall (aplus A B :: l)
| with_r : forall A B l, mall (A :: l) -> mall (B :: l) ->  mall (awith A B :: l).

Global Instance Perm_R_mall : Proper (@Perm_R formulas ==> arrow) mall.
Proof. now intros l1 l2 Hp pi; apply ex_r with l1. Defined.

Fixpoint psize {l} (pi : mall l) :=
  match pi with
  | ax_r _ => 1
  | ex_r _ _ pi _ => S (psize pi)
  | tens_r _ _ _ _ pi1 pi2 => S (psize pi1 + psize pi2)
  | parr_r _ _ _ pi => S (psize pi)
  | plus_r1 _ _ _ pi1 => S (psize pi1)
  | plus_r2 _ _ _ pi2 => S (psize pi2)
  | with_r _ _ _ pi1 pi2 => S (psize pi1 + psize pi2)
  end.

Lemma cut_admissible : forall A l1 l2,
  mall (dual A :: l1) -> mall (A :: l2) -> mall (l1 ++ l2).
Proof with try assumption; try reflexivity; try fsize_lia.
  enough (forall c s A l0 l1 l2 (pi1 : mall (dual A :: l0)) (pi2 : mall (l1 ++ A :: l2)),
          s = psize pi1 + psize pi2 -> fsize A <= c -> mall (l1 ++ l0 ++ l2)) as IH
    by (now intros A l1 l2 pi1 pi2; rewrite <- (app_nil_l _) in pi2; refine (IH _ _ A _ _ _ pi1 pi2 _ _)).
  induction c as [c IHcut0] using lt_wf_rect.
  assert (forall A, fsize A < c -> forall l0 l1 l2,
                    mall (dual A :: l0) -> mall (l1 ++ A :: l2) -> mall (l1 ++ l0 ++ l2)) as IHcut
    by (now intros A Hs l0 l1 l2 pi1 pi2 ; refine (IHcut0 _ _ _ _ _ _ _ pi1 pi2 _ _); try eassumption);
    clear IHcut0.
  induction s as [s IHsize0] using lt_wf_rect.
  assert (forall A l0 l1 l2 (pi1 : mall (dual A :: l0)) (pi2 : mall (l1 ++ A :: l2)),
            psize pi1 + psize pi2 < s -> fsize A <= c -> mall (l1 ++ l0 ++ l2)) as IHsize
    by (now intros ; eapply IHsize0 ; try eassumption) ; clear IHsize0.
  intros A l0 l1 l2 pi1 pi2 Heqs Hc; rewrite_all Heqs; clear s Heqs.
  remember (l1 ++ A :: l2) as l ; destruct pi2.
  - (* ax_r *)
    destruct l1 ; inversion Heql ; subst.
    + simpl; clear - pi1; revert pi1; refine (Perm_R_mall _ _ (Perm_R_cons_append _ _)).
        (* could be a rewrite Perm_R_cons_append, but Coq bug *)
    + decomp_unit_eq_elt H1. list_simpl...
  - (* ex_r *)
    simpl in IHsize; rewrite Heql in p.
    destruct (Perm_R_vs_elt_inv _ _ _ _ p) as [[p1 p2] Heq]; simpl in Heq; subst.
    apply ex_r with (p1 ++ l0 ++ p2);
    [ | now apply Perm_R_app_inv in p; apply Perm_R_app_middle ].
    refine (IHsize _ _ _ _ pi1 pi2 _ _)...
  - (* tens_r *)
    destruct l1 ; inversion Heql ; subst ; simpl in Hc; list_simpl.
    + (* main case *)
      remember (dual (tens A0 B) :: l0) as l' ; destruct pi1; inversion Heql'.
      * (* ex_r *)
        remember (tens_r _ _ _ _ pi2_1 pi2_2) as Htens; clear HeqHtens.
        revert p IHsize; rewrite Heql'; rewrite <- (app_nil_l (dual (tens A0 B) :: _)); intros p IHsize.
        destruct (Perm_R_vs_cons_inv _ _ _ p) as [[p1 p2] Heq]; simpl in Heq; subst.
        apply ex_r with (p1 ++ (l4 ++ l3) ++ p2);
          [ | clear - p; apply Perm_R_app_inv in p; simpl in p; rewrite <- p; list_simpl;
              apply Perm_R_app_head; now rewrite (Perm_R_app_comm p2); list_simpl ].
        revert Htens IHsize ; simpl;
          replace (tens A0 B) with (dual (parr (dual B) (dual A0))) by (now simpl; rewrite 2 bidual);
          intros Htens IHsize.
        refine (IHsize _ _ _ _ Htens pi1 _ _)...
      * (* parr_r *)
        clear IHsize; subst.
        rewrite <- (bidual B) in pi2_2; refine (IHcut _ _ _ _ _ pi2_2 _)...
        apply ex_r with ((dual B :: nil) ++ l3 ++ l0); [ | now rewrite <- Perm_R_app_rot ].
          (* could be done with rewrite, but Coq bug *)
        rewrite <- (bidual A0) in pi2_1; refine (IHcut _ _ _ _ _ pi2_1 _)...
    + (* commutative case *)
      decomp_elt_eq_app H1; subst.
      * rewrite 2 app_assoc; apply tens_r...
        revert pi2_2 IHsize ; simpl ; rewrite (app_comm_cons _ _ B); intros pi2_2 IHsize; list_simpl.
        refine (IHsize _ _ _ _ pi1 pi2_2 _ _)...
      * list_simpl ; apply tens_r...
        revert pi2_1 IHsize; simpl; rewrite (app_comm_cons _ _ A0); intros pi2_1 IHsize.
        refine (IHsize _ _ _ _ pi1 pi2_1 _ _)...
  - (* parr_r *)
    destruct l1; inversion Heql; subst; simpl in Hc; list_simpl.
    + (* main case *)
      remember (dual (parr A0 B) :: l0) as l'; destruct pi1; inversion Heql'.
      * (* ex_r *)
        remember (parr_r _ _ _ pi2) as Hparr; clear HeqHparr.
        revert p IHsize; rewrite Heql'; rewrite <- (app_nil_l (dual (parr A0 B) :: _)); intros p IHsize.
        destruct (Perm_R_vs_cons_inv _ _ _ p) as [[p1 p2] Heq]; simpl in Heq; subst.
        apply ex_r with (p1 ++ l2 ++ p2);
        [ | clear - p; apply Perm_R_app_inv in p; simpl in p; rewrite <- p; list_simpl;
            apply Perm_R_app_head, Perm_R_app_comm ].
        revert Hparr IHsize; simpl;
          replace (parr A0 B) with (dual (tens (dual B) (dual A0))) by (now simpl; rewrite 2 bidual);
          intros Hparr IHsize.
        refine (IHsize _ _ _ _ Hparr pi1 _ _)...
      * (* tens_r *)
        clear IHsize; subst; list_simpl.
        rewrite <- (app_nil_l (A0 :: _)) in pi2; refine (IHcut _ _ _ _ _ pi1_1 _)...
        rewrite <- (app_nil_l _); refine (IHcut _ _ _ _ _ pi1_2 _)...
    + (* commutative case *)
      apply parr_r.
      revert pi2 IHsize; simpl; rewrite (app_comm_cons l1 _ B), (app_comm_cons _ _ A0); intros pi2 IHsize.
      refine (IHsize _ _ _ _ pi1 pi2 _ _)...
  - (* plus_r1 *)
    destruct l1; inversion Heql; subst; simpl in Hc; list_simpl.
    + (* main case *)
      remember (dual (aplus A0 B) :: l0) as l'; destruct pi1; inversion Heql'.
      * (* ex_r *)
        remember (plus_r1 _ _ _ pi2) as Hplus; clear HeqHplus.
        revert p IHsize; rewrite Heql'; rewrite <- (app_nil_l (dual (aplus A0 B) :: _)); intros p IHsize.
        destruct (Perm_R_vs_cons_inv _ _ _ p) as [[p1 p2] Heq]; simpl in Heq; subst.
        apply ex_r with (p1 ++ l2 ++ p2);
        [ | clear - p; apply Perm_R_app_inv in p; simpl in p; rewrite <- p; list_simpl;
            apply Perm_R_app_head, Perm_R_app_comm ].
        revert Hplus IHsize; simpl;
          replace (aplus A0 B) with (dual (awith (dual A0) (dual B))) by (now simpl; rewrite 2 bidual);
          intros Hplus IHsize.
        refine (IHsize _ _ _ _ Hplus pi1 _ _)...
      * (* with_r *)
        clear IHsize; subst.
        rewrite <- (app_nil_l (A0 :: _)) in pi2; refine (IHcut _ _ _ _ _ pi1_1 pi2)...
    + (* commutative case *)
      apply plus_r1.
      revert pi2 IHsize; simpl; rewrite (app_comm_cons l1 _ A0); intros pi2 IHsize.
      refine (IHsize _ _ _ _ pi1 pi2 _ _)...
  - (* plus_r2 *)
    destruct l1; inversion Heql; subst; simpl in Hc; list_simpl.
    + (* main case *)
      remember (dual (aplus A0 B) :: l0) as l'; destruct pi1; inversion Heql'.
      * (* ex_r *)
        remember (plus_r2 _ _ _ pi2) as Hplus; clear HeqHplus.
        revert p IHsize; rewrite Heql'; rewrite <- (app_nil_l (dual (aplus A0 B) :: l0)); intros p IHsize.
        destruct (Perm_R_vs_cons_inv _ _ _ p) as [[p1 p2] Heq]; simpl in Heq; subst.
        apply ex_r with (p1 ++ l2 ++ p2);
        [ | clear - p; apply Perm_R_app_inv in p; simpl in p; rewrite <- p; list_simpl;
            apply Perm_R_app_head, Perm_R_app_comm ].
        revert Hplus IHsize; simpl;
          replace (aplus A0 B) with (dual (awith (dual A0) (dual B))) by (now simpl; rewrite 2 bidual);
          intros Hplus IHsize.
        refine (IHsize _ _ _ _ Hplus pi1 _ _)...
      * (* with_r *)
        clear IHsize; subst.
        rewrite <- (app_nil_l (B :: _)) in pi2; refine (IHcut _ _ _ _ _ pi1_2 pi2)...
    + (* commutative case *)
      apply plus_r2.
      revert pi2 IHsize; simpl; rewrite (app_comm_cons l1 _ B); intros pi2 IHsize.
      refine (IHsize _ _ _ _ pi1 pi2 _ _)...
  - (* with_r *)
    destruct l1; inversion Heql; subst; simpl in Hc; list_simpl.
    + (* main case *)
      remember (dual (awith A0 B) :: l0) as l'; destruct pi1; inversion Heql'.
      * (* ex_r *)
        remember (with_r _ _ _ pi2_1 pi2_2) as Hwith; clear HeqHwith.
        revert p IHsize; rewrite Heql'; rewrite <- (app_nil_l (dual (awith A0 B) :: _)); intros p IHsize.
        destruct (Perm_R_vs_cons_inv _ _ _ p) as [[p1 p2] Heq]; simpl in Heq; subst.
        apply ex_r with (p1 ++ l2 ++ p2);
        [ | clear - p; apply Perm_R_app_inv in p; simpl in p; rewrite <- p; list_simpl;
            apply Perm_R_app_head, Perm_R_app_comm ].
        revert Hwith IHsize ; simpl ;
          replace (awith A0 B) with (dual (aplus (dual A0) (dual B))) by (now simpl; rewrite 2 bidual);
          intros Hwith IHsize.
        refine (IHsize _ _ _ _ Hwith pi1 _ _)...
      * (* plus_r1 *)
        clear IHsize; subst.
        rewrite <- (app_nil_l (A0 :: _)) in pi2_1; refine (IHcut _ _ _ _ _ pi1 pi2_1)...
      * (* plus_r2 *)
        clear IHsize; subst.
        rewrite <- (app_nil_l (B :: _)) in pi2_2 ; refine (IHcut _ _ _ _ _ pi1 pi2_2)...
    + (* commutative case *)
      apply with_r.
      * revert pi2_1 IHsize; simpl; rewrite (app_comm_cons l1 _ A0); intros pi2_1 IHsize.
        refine (IHsize _ _ _ _ pi1 pi2_1 _ _)...
      * revert pi2_2 IHsize; simpl; rewrite (app_comm_cons l1 _ B); intros pi2_2 IHsize.
        refine (IHsize _ _ _ _ pi1 pi2_2 _ _)...
Qed.


Inductive mall_cut : list formulas -> Type :=
| ax_cut_r : forall X, mall_cut (covar X :: var X :: nil)
| ex_cut_r : forall l1 l2, mall_cut l1 -> l1 ~~ l2 -> mall_cut l2
| tens_cut_r : forall A B l1 l2, mall_cut (A :: l1) -> mall_cut (B :: l2) -> mall_cut (tens A B :: l2 ++ l1)
| parr_cut_r : forall A B l, mall_cut (A :: B :: l) -> mall_cut (parr A B :: l)
| plus_cut_r1 : forall A B l, mall_cut (A :: l) -> mall_cut (aplus A B :: l)
| plus_cut_r2 : forall A B l, mall_cut (B :: l) -> mall_cut (aplus A B :: l)
| with_cut_r : forall A B l, mall_cut (A :: l) -> mall_cut (B :: l) -> mall_cut (awith A B :: l)
| cut_r : forall A l1 l2, mall_cut (dual A :: l1) -> mall_cut (A :: l2) ->  mall_cut (l1 ++ l2).

Global Instance Perm_R_mall_cut : Proper (@Perm_R formulas ==> arrow) mall_cut.
Proof. now intros l1 l2 Hp pi; apply ex_cut_r with l1. Defined.

Theorem cut_elim : forall l, mall_cut l -> mall l.
Proof.
  intros l pi; induction pi; try now constructor.
  - now apply ex_r with l1.
  - now apply cut_admissible with A.
Qed.
