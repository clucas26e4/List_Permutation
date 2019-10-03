Require Import Lia.
Require Import PeanoNat.

Require Import List_more.
Require Import List_Type_more.
Require Import wf_nat_more.

Require Import List_more2.

Require Import List_nat.
Require Import Fun_nat.
Require Import misc.
Require Import Perm.
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
  | var X => 0
  | covar X => 0
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

Inductive mll_cut : list formulas -> Type :=
| ax_cut_r : forall X, mll_cut (covar X :: var X :: nil)
| ex_cut_r : forall l1 l2, mll_cut l1 -> Perm_R l1 l2 ->
                             mll_cut l2
| tens_cut_r : forall A B l1 l2, mll_cut (A :: l1) -> mll_cut (B :: l2) ->
                                 mll_cut (tens A B :: l2 ++ l1)
| parr_cut_r : forall A B l, mll_cut (A :: B :: l) -> mll_cut (parr A B :: l)
| plus_cut_r1 : forall A B l, mll_cut (A :: l) -> mll_cut (aplus A B :: l)
| plus_cut_r2 : forall A B l, mll_cut (B :: l) -> mll_cut (aplus A B :: l)
| with_cut_r : forall A B l, mll_cut (A :: l) -> mll_cut (B :: l) ->
                             mll_cut (awith A B :: l)
| cut_r : forall A l1 l2, mll_cut (dual A :: l1) -> mll_cut (A :: l2) ->
                          mll_cut (l2 ++ l1).

Inductive mll : list formulas -> Type :=
| ax_r : forall X, mll (covar X :: var X :: nil)
| ex_r : forall l1 l2, mll l1 -> Perm_R l1 l2 ->
                     mll l2
| tens_r : forall A B l1 l2, mll (A :: l1) -> mll (B :: l2) ->
                             mll (tens A B :: l2 ++ l1)
| plus_r1 : forall A B l, mll (A :: l) -> mll (aplus A B :: l)
| plus_r2 : forall A B l, mll (B :: l) -> mll (aplus A B :: l)
| with_r : forall A B l, mll (A :: l) -> mll (B :: l) ->
                             mll (awith A B :: l)
| parr_r : forall A B l, mll (A :: B :: l) -> mll (parr A B :: l).

Fixpoint psize {l} (pi : mll l) :=
  match pi with
  | ax_r _ => 0
  | ex_r _ _ pi _ => S (psize pi)
  | tens_r _ _ _ _ pi1 pi2 => S (psize pi1 + psize pi2)
  | parr_r _ _ _ pi => S (psize pi)
  | plus_r1 _ _ _ pi1 => S (psize pi1)
  | plus_r2 _ _ _ pi2 => S (psize pi2)
  | with_r _ _ _ pi1 pi2 => S (psize pi1 + psize pi2)
  end.

Lemma cut_admissible : forall A l1 l2,
  mll (dual A :: l1) -> mll (A :: l2) ->
    mll (l2 ++ l1).
Proof with try assumption; try reflexivity.
  enough (forall c s A l0 l1 l2 (pi1 : mll (dual A :: l0)) (pi2 : mll (l1 ++ A :: l2)),
          s = psize pi1 + psize pi2 -> fsize A <= c -> mll (l1 ++ l0 ++ l2)) as IH.
  { intros A l1 l2 pi1 pi2.
    rewrite <- (app_nil_l _) in pi2.
    apply ex_r with (l1 ++ l2); [ | apply Perm_R_app_comm].
    refine (IH _ _ A _ _ _ pi1 pi2 _ _)... }
  induction c as [c IHcut0] using lt_wf_rect.
  assert (forall A, fsize A < c -> forall l0 l1 l2,
               mll (dual A :: l0) -> mll (l1 ++ A :: l2) -> mll (l1 ++ l0 ++ l2)) as IHcut
    by (now intros A Hs l0 l1 l2 pi1 pi2 ; refine (IHcut0 _ _ _ _ _ _ _ pi1 pi2 _ _); try eassumption);
    clear IHcut0.
  induction s as [s IHsize0] using lt_wf_rect.
  assert (forall A l0 l1 l2 (pi1 : mll (dual A :: l0)) (pi2 : mll (l1 ++ A :: l2)),
            psize pi1 + psize pi2 < s -> fsize A <= c -> mll (l1 ++ l0 ++ l2))
    as IHsize by (now intros ; eapply IHsize0 ; try eassumption) ; clear IHsize0.
  intros A l0 l1 l2 pi1 pi2 Heqs Hc.
  rewrite_all Heqs; clear s Heqs.
  remember (l1 ++ A :: l2) as l ; destruct pi2.
  - (* ax_r *)
    destruct l1 ; inversion Heql ; subst.
    + apply ex_r with (var X :: l0); [ | rewrite (Perm_R_app_comm l0)]...
    + unit_vs_elt_inv H1 ; list_simpl...
  - (* ex_r *)
    simpl in IHsize; rewrite Heql in p.
    destruct (Perm_R_vs_elt_inv _ _ _ _ p) as [[p1 p2] Heq] ; simpl in Heq ; subst.
    eapply ex_r ; [ refine (IHsize _ _ _ _ pi1 pi2 _ _) | ]; try lia.
    apply Perm_R_app_middle; apply Perm_R_app_inv with A...
  - (* tens_r *)
    destruct l1 ; inversion Heql ; subst ; list_simpl.
    + (* main case *)
      remember (dual (tens A0 B) :: l0) as l' ; destruct pi1; try inversion Heql'.
      * (* ex_r *)
        remember (tens_r _ _ _ _ pi2_1 pi2_2) as Htens ; clear HeqHtens.
        revert p IHsize; rewrite Heql'; change (dual (tens A0 B) :: l0) with (nil ++ (dual (tens A0 B) :: l0)); intros p IHsize.
        destruct (Perm_R_vs_cons_inv _ _ _ p) as [[p1 p2] Heq] ; simpl in Heq ; subst.
        apply ex_r with (p1 ++ l4 ++ l3 ++ p2).
        2:{ rewrite <- (app_nil_r (l4 ++ l3)); replace (p1 ++ l4 ++ l3 ++ p2) with (p1 ++ (l4 ++ l3) ++ p2) by (now rewrite<- ? app_assoc).
            apply Perm_R_app_middle; apply Perm_R_app_inv with (parr (dual B) (dual A0)).
            rewrite (Perm_R_app_comm l0)... }
        revert Htens IHsize ; simpl ;
          replace (tens A0 B) with (dual (parr (dual B) (dual A0)))
          by (simpl ; rewrite 2 bidual ; reflexivity) ;
          intros Htens IHsize.
        replace (p1 ++ l4 ++ l3 ++ p2) with (p1 ++ (l4 ++ l3) ++ p2) by (now rewrite<- ? app_assoc).
        refine (IHsize _ _ _ _ Htens pi1 _ _); simpl; simpl in Hc; [ | rewrite 2 fsize_dual]; try lia.
      * (* parr_r *)
        clear IHsize ; subst.
        rewrite <- (app_nil_l (A0 :: _)) in pi2_1 ; simpl in Hc ; list_simpl.
        rewrite <- (bidual B) in pi2_2.
        refine (IHcut _ _ _ _ _ pi2_2 _)...
        -- rewrite fsize_dual; lia.
        -- eapply ex_r ; [ | apply Perm_R_app_comm ].
           list_simpl in pi2_1 ; rewrite <- (bidual A0) in pi2_1.
           change ((dual B :: l3) ++ l0) with ((dual B :: nil) ++ l3 ++ l0).
           refine (IHcut _ _ _ _ _ pi2_1 _)...
           rewrite fsize_dual; lia.
    + (* commutative case *)
      dichot_Type_elt_app_exec H1 ; subst.
      * rewrite 2 app_assoc ; apply tens_r...
        revert pi2_2 IHsize ; simpl ; rewrite (app_comm_cons _ _ B) ; intros pi2_2 IHsize.
        rewrite <- app_assoc ; refine (IHsize _ _ _ _ pi1 pi2_2 _ _) ; simpl; lia.
      * list_simpl ; apply tens_r...
        revert pi2_1 IHsize ; simpl ; rewrite (app_comm_cons _ _ A0) ; intros pi2_1 IHsize.
        refine (IHsize _ _ _ _ pi1 pi2_1 _ _) ; simpl; lia.
  - (* plus_r1 *)
    destruct l1 ; inversion Heql ; subst ; list_simpl.
    + (* main case *)
      remember (dual (aplus A0 B) :: l0) as l' ; destruct pi1; try inversion Heql'.
      * (* ex_r *)
        remember (plus_r1 _ _ _ pi2) as Hplus ; clear HeqHplus.
        revert p IHsize; rewrite Heql'; change (dual (aplus A0 B) :: l0) with (nil ++ (dual (aplus A0 B)) :: l0); intros p IHsize.
        destruct (Perm_R_vs_cons_inv _ _ _ p) as [[p1 p2] Heq] ; simpl in Heq ; subst.
        apply ex_r with (p1 ++ l2 ++ p2).
        2:{ rewrite<- (app_nil_r l2) at 2.
            apply Perm_R_app_middle.
            apply Perm_R_app_inv with (awith (dual A0) (dual B)).
            rewrite (Perm_R_app_comm l0)... }
        revert Hplus IHsize ; simpl ;
          replace (aplus A0 B) with (dual (awith (dual A0) (dual B)))
          by (simpl ; rewrite 2 bidual ; reflexivity) ;
          intros Hplus IHsize.
        refine (IHsize _ _ _ _ Hplus pi1 _ _); [ | simpl; rewrite 2 fsize_dual]...
        lia.
      * (* with_r *)
        clear IHsize ; subst.
        rewrite <- (app_nil_l (A0 :: _)) in pi2 ; simpl in Hc ; refine (IHcut _ _ _ _ _ pi1_1 pi2); lia.
    + (* commutative case *)
      apply plus_r1.
      revert pi2 IHsize ; simpl ; rewrite (app_comm_cons l1 _ A0) ; intros pi2 IHsize.
      refine (IHsize _ _ _ _ pi1 pi2 _ _) ; simpl; lia.
  - (* plus_r2 *)
    destruct l1 ; inversion Heql ; subst ; list_simpl.
    + (* main case *)
      remember (dual (aplus A0 B) :: l0) as l' ; destruct pi1; try inversion Heql'.
      * (* ex_r *)
        remember (plus_r2 _ _ _ pi2) as Hplus ; clear HeqHplus.
        revert p IHsize; rewrite Heql'; rewrite<- (app_nil_l (dual (aplus A0 B) :: l0)); intros p IHsize.
        destruct (Perm_R_vs_cons_inv _ _ _ p) as [[p1 p2] Heq] ; simpl in Heq; subst.
        apply ex_r with (p1 ++ l2 ++ p2).
        2:{ rewrite<- (app_nil_r l2) at 2.
            apply Perm_R_app_middle.
            apply Perm_R_app_inv with (awith (dual A0) (dual B)).
            rewrite (Perm_R_app_comm l0)... }
        revert Hplus IHsize ; simpl ;
          replace (aplus A0 B) with (dual (awith (dual A0) (dual B)))
          by (simpl ; rewrite 2 bidual ; reflexivity) ;
          intros Hplus IHsize.
        refine (IHsize _ _ _ _ Hplus pi1 _ _); [ | simpl ; rewrite 2 fsize_dual]...
        lia.
      * (* with_r *)
        clear IHsize ; subst.
        rewrite <- (app_nil_l (B :: _)) in pi2 ; simpl in Hc ; refine (IHcut _ _ _ _ _ pi1_2 pi2); lia.
    + (* commutative case *)
      apply plus_r2.
      revert pi2 IHsize ; simpl ; rewrite (app_comm_cons l1 _ B) ; intros pi2 IHsize.
      refine (IHsize _ _ _ _ pi1 pi2 _ _) ; lia.
  - (* with_r *)
    destruct l1 ; inversion Heql ; subst ; list_simpl.
    + (* main case *)
      remember (dual (awith A0 B) :: l0) as l' ; destruct pi1 ; try inversion Heql'.
      * (* ex_r *)
        remember (with_r _ _ _ pi2_1 pi2_2) as Hwith ; clear HeqHwith.
        revert p IHsize; rewrite Heql'; change (dual (awith A0 B) :: l0) with (nil ++ dual (awith A0 B) :: l0); intros p IHsize.
        destruct (Perm_R_vs_cons_inv _ _ _ p) as [[p1 p2] Heq] ; simpl in Heq ; subst.
        apply ex_r with (p1 ++ l2 ++ p2).
        2:{ rewrite<- (app_nil_r l2) at 2.
            apply Perm_R_app_middle.
            apply Perm_R_app_inv with (aplus (dual A0) (dual B)).
            rewrite (Perm_R_app_comm l0)... }
        revert Hwith IHsize ; simpl ;
          replace (awith A0 B) with (dual (aplus (dual A0) (dual B)))
          by (simpl ; rewrite 2 bidual ; reflexivity) ;
          intros Hwith IHsize.
        refine (IHsize _ _ _ _ Hwith pi1 _ _); [ | simpl ; rewrite 2 fsize_dual]...
        lia.
      * (* plus_r1 *)
        clear IHsize ; subst.
        rewrite <- (app_nil_l (A0 :: _)) in pi2_1 ; simpl in Hc ; refine (IHcut _ _ _ _ _ pi1 pi2_1); lia.
      * (* plus_r2 *)
        clear IHsize ; subst.
        rewrite <- (app_nil_l (B :: _)) in pi2_2 ; simpl in Hc ; refine (IHcut _ _ _ _ _ pi1 pi2_2); lia.
    + (* commutative case *)
      apply with_r.
      * revert pi2_1 IHsize ; simpl ; rewrite (app_comm_cons l1 _ A0) ; intros pi2_1 IHsize.
        refine (IHsize _ _ _ _ pi1 pi2_1 _ _) ; lia.
      * revert pi2_2 IHsize ; simpl ; rewrite (app_comm_cons l1 _ B) ; intros pi2_2 IHsize.
        refine (IHsize _ _ _ _ pi1 pi2_2 _ _) ; lia.
  - (* parr_r *)
    destruct l1 ; inversion Heql ; subst ; list_simpl.
    + (* main case *)
      remember (dual (parr A0 B) :: l0) as l' ; destruct pi1; try inversion Heql'.
      * (* ex_r *)
        remember (parr_r _ _ _ pi2) as Hparr ; clear HeqHparr.
        revert p IHsize; rewrite Heql'; change (dual (parr A0 B) :: l0) with (nil ++ dual (parr A0 B) :: l0); intros p IHsize.
        destruct (Perm_R_vs_cons_inv _ _ _ p) as [[p1 p2] Heq] ; simpl in Heq ; subst.
        apply ex_r with (p1 ++ l2 ++ p2).
        2:{ rewrite<- (app_nil_r l2) at 2.
            apply Perm_R_app_middle; apply Perm_R_app_inv with (tens (dual B) (dual A0)).
            rewrite (Perm_R_app_comm l0)... }
        revert Hparr IHsize ; simpl ;
          replace (parr A0 B) with (dual (tens (dual B) (dual A0)))
          by (simpl ; rewrite 2 bidual ; reflexivity) ;
          intros Hparr IHsize.
        refine (IHsize _ _ _ _ Hparr pi1 _ _) ; [ | simpl in Hc ; simpl ; rewrite 2 fsize_dual]; lia.
      * (* tens_r *)
        clear IHsize ; subst.
        rewrite <- (app_nil_l (A0 :: _)) in pi2 ; simpl in Hc ; list_simpl.
        refine (IHcut _ _ _ _ _ pi1_1 _); [lia | ].
        rewrite <- (app_nil_l _) ; refine (IHcut _ _ _ _ _ pi1_2 _)...
        lia.
    + (* commutative case *)
      apply parr_r.
      revert pi2 IHsize ; simpl ; rewrite (app_comm_cons l1 _ B) ; rewrite (app_comm_cons _ _ A0) ;
        intros pi2 IHsize.
      refine (IHsize _ _ _ _ pi1 pi2 _ _); lia.
Qed.

Lemma cut_elim : forall l, mll_cut l -> mll l.
Proof with try assumption.
  intros l pi.
  induction pi; try (now constructor); try (eapply ex_r; eassumption).
  apply cut_admissible with A...
Qed.

