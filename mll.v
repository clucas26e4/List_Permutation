Require Import Lia.

Require Import List_more.
Require Import List_Type_more.
Require Import wf_nat_more.
Require Import PeanoNat.

Require Import List_more2.
Require Import List_nat.
Require Import Fun_nat.
Require Import Perm.
Require Import Perm_R.
Require Import misc.
Require Import Perm_solve.

Inductive formulas : Set :=
| var : nat -> formulas
| covar : nat -> formulas
| tens : formulas -> formulas -> formulas
| parr : formulas -> formulas -> formulas.

Fixpoint fsize A :=
  match A with
  | var X => 0
  | covar X => 0
  | tens A B => S (fsize A + fsize B)
  | parr A B => S (fsize A + fsize B)
  end.

Fixpoint dual A :=
  match A with
  | var X => covar X
  | covar X => var X
  | tens A B => parr (dual B) (dual A)
  | parr A B => tens (dual B) (dual A)
  end.

Lemma bidual : forall A, dual (dual A) = A.
Proof with try reflexivity.
  induction A; simpl; try rewrite IHA1; try rewrite IHA2...
Qed.

Lemma fsize_dual : forall A, fsize (dual A) = fsize A.
Proof with try reflexivity.
  induction A; simpl; try rewrite IHA1; try rewrite IHA2; try rewrite Nat.add_comm...
Qed.

Inductive mll_cut : list formulas -> Type :=
| ax_cut_r : forall X, mll_cut (covar X :: var X :: nil)
| ex_cut_r : forall l f, mll_cut l -> is_perm f = true -> length f = length l ->
                     mll_cut (app_nat_fun f l)
| tens_cut_r : forall A B l1 l2, mll_cut (A :: l1) -> mll_cut (B :: l2) ->
                             mll_cut (tens A B :: l2 ++ l1)
| parr_cut_r : forall A B l, mll_cut (A :: B :: l) -> mll_cut (parr A B :: l)
| cut_r : forall A l1 l2, mll_cut (dual A :: l1) -> mll_cut (A :: l2) ->
                          mll_cut (l2 ++ l1).

Inductive mll : list formulas -> Type :=
| ax_r : forall X, mll (covar X :: var X :: nil)
| ex_r : forall l f, mll l -> is_perm f = true -> length f = length l ->
                     mll (app_nat_fun f l)
| tens_r : forall A B l1 l2, mll (A :: l1) -> mll (B :: l2) ->
                             mll (tens A B :: l2 ++ l1)
| parr_r : forall A B l, mll (A :: B :: l) -> mll (parr A B :: l).

Fixpoint psize {l} (pi : mll l) :=
  match pi with
  | ax_r _ => 0
  | ex_r _ _ pi _ _ => S (psize pi)
  | tens_r _ _ _ _ pi1 pi2 => S (psize pi1 + psize pi2)
  | parr_r _ _ _ pi => S (psize pi)
  end.

(* TODO: NEED MOVING *)
Lemma app_antecedent_dflt {A} : forall (d a : A) f l l1 l2,
    all_lt f (length l) = true ->
    app_nat_fun_dflt f l d = l1 ++ a :: l2 ->
    nth (nth (length l1) f 0) l d = a.
Proof.
  intros d a f l l1.
  revert d a f l.
  induction l1; intros d b f l l2 Hal Heq.
  - simpl in *.
    destruct f; destruct l; try now inversion Heq.
  - destruct f; [ destruct l; inversion Heq | ].
    simpl.
    simpl in Hal; apply andb_prop in Hal as [_ Hal].
    apply IHl1 with l2; try assumption.
    destruct l; try now inversion Heq.
Qed.

Lemma app_antecedent {A} : forall (d a : A) f l l1 l2,
    all_lt f (length l) = true ->
    app_nat_fun f l = l1 ++ a :: l2 ->
    nth (nth (length l1) f 0) l d = a.
Proof.
  intros d a f l l1 l2 Hal Heq.
  apply app_antecedent_dflt with l2; try assumption.
  destruct l; [ destruct l1; inversion Heq | ].
  unfold app_nat_fun in Heq.
  rewrite app_nat_fun_dflt_indep with _ _ _ a0; try assumption.
Qed.

Lemma cut_admissible : forall A l1 l2,
    mll (dual A :: l1) ->
    mll (A :: l2) ->
    mll (l2 ++ l1).
Proof with try assumption; try reflexivity.
  enough (forall c s A l0 l1 l2 (pi1 : mll (dual A :: l0)) (pi2 : mll (l1 ++ A :: l2)),
          s = psize pi1 + psize pi2 -> fsize A <= c -> mll (l1 ++ l0 ++ l2)) as IH.
  { intros A l1 l2 pi1 pi2.
    rewrite <- (app_nil_l _) in pi2.
    replace (l2 ++ l1) with (app_nat_fun (cfun (length l1) (length l2)) (nil ++ l1 ++ l2)) by (simpl; apply app_cfun_eq).
    apply ex_r; [ | apply cfun_is_perm | length_lia].
    refine (IH _ _ A _ _ _ pi1 pi2 _ _)... }
  induction c as [c IHcut0] using lt_wf_rect.
  assert (forall A, fsize A < c -> forall l0 l1 l2,
               mll (dual A :: l0) -> mll (l1 ++ A :: l2) -> mll (l1 ++ l0 ++ l2)) as IHcut by (intros A Hs l0 l1 l2 pi1 pi2 ; refine (IHcut0 _ _ _ _ _ _ _ pi1 pi2 _ _) ; try eassumption; try reflexivity) ;
    clear IHcut0.
  induction s as [s IHsize0] using lt_wf_rect.
  assert (forall A l0 l1 l2 (pi1 : mll (dual A :: l0)) (pi2 : mll (l1 ++ A :: l2)), psize pi1 + psize pi2 < s -> fsize A <= c -> mll (l1 ++ l0 ++ l2))
    as IHsize by (intros ; eapply IHsize0 ; try eassumption; try reflexivity) ; clear IHsize0.
  intros A l0 l1 l2 pi1 pi2 Heqs Hc.
  rewrite_all Heqs ; clear s Heqs.
  remember (l1 ++ A :: l2) as l ; destruct pi2.
  - (* ax_r *)
    destruct l1 ; inversion Heql ; subst.
    + replace (nil ++ l0 ++ var X :: nil) with (app_nat_fun (cfun 1 (length l0)) (var X :: l0)) by (change (var X :: l0) with ((var X :: nil) ++ l0); change 1 with (length (var X :: nil)); now rewrite app_cfun_eq).
      apply ex_r ; [ | apply cfun_is_perm | length_lia] ...
    + unit_vs_elt_inv H1 ; list_simpl...
  - (* ex_r *)
    simpl in IHsize.
    destruct (nth_split_Type (nth (length l1) f 0) l A) as [[la lb] Heq Hlen].
    + apply andb_prop in e as [Hal _]; rewrite e0 in Hal; apply cond_all_lt_inv...
      rewrite<- app_nat_fun_length with _ l ; [ | destruct l; [destruct l1; inversion Heql | intros H; inversion H ]].
      rewrite Heql; length_lia.
    + rewrite app_antecedent with _ A _ _ _ l2 in Heq ; [ | rewrite<- e0; apply andb_prop in e as [Hal _] | ]...
      revert pi2 IHsize; rewrite Heq; intros pi2 IHsize.
      enough (Perm_R (la ++ l0 ++ lb) (l1 ++ l0 ++ l2)) as [p [Hperm [Hlen' Heq']]].
      { rewrite Heq'; apply ex_r...
        apply IHsize with A pi1 pi2...
        lia. }
      transitivity (l0 ++ l2 ++ l1); [ | rewrite (app_assoc _ _ l1); apply Perm_R_app_comm ].
      transitivity (l0 ++ lb ++ la); [ rewrite (app_assoc _ _ la); apply Perm_R_app_comm | ]. 
      apply Perm_R_app_head.
      transitivity (la ++ lb) ; [ apply Perm_R_app_comm | ].
      transitivity (l1 ++ l2) ; [ | apply Perm_R_app_comm ].
      apply Perm_R_app_inv with A.
      split with f.
      rewrite<- Heq; repeat split; [ | | symmetry]...
  - (* tens_r *)
    destruct l1 ; inversion Heql ; subst ; list_simpl.
    + (* main case *)
      remember (dual (tens A0 B) :: l0) as l' ; destruct pi1; try inversion Heql'.
      * (* ex_r *)
        remember (tens_r _ _ _ _ pi2_1 pi2_2) as pi2; clear pi2_1 pi2_2 Heqpi2 IHcut.
        simpl in IHsize.
        destruct f; [destruct l; inversion H0 | ].
        destruct (andb_prop _ _ e) as [Hal _]; rewrite e0 in Hal; simpl in Hal; apply andb_prop in Hal as [Hlt Hal]; apply Nat.ltb_lt in Hlt.
        destruct (nth_split_Type n l A0) as [[la lb] Heq Hlen]...
        replace (nth n l A0) with (parr (dual B) (dual A0)) in Heq by (destruct l; [ | app_nat_fun_unfold f l n f0; rewrite nth_indep with _ _ _ _ f0; try assumption]; now inversion H0).
        revert pi1 pi2 IHsize; rewrite Heq; replace (tens A0 B) with (dual (parr (dual B) (dual A0))) by (simpl; now rewrite 2 bidual) ; intros pi1 pi2 IHsize.
        enough (Perm_R (la ++ (l4 ++ l3) ++ lb) (l0  ++ (l4 ++ l3))) as [p [Hperm [Hlen' Heq']]].
        { rewrite Heq'; apply ex_r...
          apply IHsize with  (parr (dual B) (dual A0)) pi2 pi1; [ lia | ].
          simpl in *; rewrite 2 fsize_dual; lia. }
        transitivity ((l4 ++ l3) ++ l0); [ | apply Perm_R_app_comm ].
        transitivity ((l4 ++ l3) ++ lb ++ la); [ rewrite (app_assoc _ _ la); apply Perm_R_app_comm | ]. 
        apply Perm_R_app_head.
        transitivity (la ++ lb) ; [ apply Perm_R_app_comm | ].
        change l0 with (nil ++ l0).
        apply Perm_R_app_inv with (parr (dual B) (dual A0)).
        split with (n :: f).
        rewrite<- Heq; repeat split ; [ | | symmetry]...
      * (* parr_r *)
        clear IHsize ; subst.
        rewrite <- (app_nil_l (A0 :: _)) in pi2_1 ; simpl in Hc ; list_simpl.
        rewrite <- (bidual B) in pi2_2.
        refine (IHcut _ _ _ _ _ pi2_2 _)...
        -- rewrite fsize_dual; lia.
        -- replace (l0 ++ dual B :: l3) with (app_nat_fun (cfun (length (dual B :: l3)) (length l0)) ((dual B :: l3) ++ l0)) by apply app_cfun_eq.
           apply ex_r ; [ | apply cfun_is_perm | length_lia ].
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
  - (* parr_r *)
    destruct l1 ; inversion Heql ; subst ; list_simpl.
    + (* main case *)
      remember (dual (parr A0 B) :: l0) as l' ; destruct pi1; try inversion Heql'.
      * (* ex_r *)
        remember (parr_r _ _ _ pi2) as pi2'; clear pi2 Heqpi2' IHcut; rename pi2' into pi2.
        simpl in IHsize.
        destruct f; [destruct l; inversion H0 | ].
        destruct (andb_prop _ _ e) as [Hal _]; rewrite e0 in Hal; simpl in Hal; apply andb_prop in Hal as [Hlt Hal]; apply Nat.ltb_lt in Hlt.
        destruct (nth_split_Type n l A0) as [[la lb] Heq Hlen]...
        replace (nth n l A0) with (tens (dual B) (dual A0)) in Heq by (destruct l; [ | app_nat_fun_unfold f l n f0; rewrite nth_indep with _ _ _ _ f0; try assumption]; now inversion H0).
        revert pi1 pi2 IHsize; rewrite Heq; replace (parr A0 B) with (dual (tens (dual B) (dual A0))) by (simpl; now rewrite 2 bidual) ; intros pi1 pi2 IHsize.
        enough (Perm_R (la ++ l2 ++ lb) (l0  ++ l2)) as [p [Hperm [Hlen' Heq']]].
        { rewrite Heq'; apply ex_r...
          apply IHsize with  (tens (dual B) (dual A0)) pi2 pi1; [ lia | ].
          simpl in *; rewrite 2 fsize_dual; lia. }
        transitivity (l2 ++ l0); [ | apply Perm_R_app_comm ].
        transitivity (l2 ++ lb ++ la); [ rewrite (app_assoc _ _ la); apply Perm_R_app_comm | ]. 
        apply Perm_R_app_head.
        transitivity (la ++ lb) ; [ apply Perm_R_app_comm | ].
        change l0 with (nil ++ l0); apply Perm_R_app_inv with (tens (dual B) (dual A0)).
        split with (n :: f);rewrite<- Heq; repeat split ; [ | | symmetry]...
      * (* tens_r *)
        clear IHsize ; subst.
        rewrite <- (app_nil_l (dual B :: _)) in pi1_1 ; simpl in Hc ; list_simpl.
        refine (IHcut _ _ _ _ _ pi1_1 _); try lia.
        rewrite <- (app_nil_l _) ; refine (IHcut _ _ _ _ _ pi1_2 _); try lia...
    + (* commutative case *)
      apply parr_r.
      revert pi2 IHsize ; simpl ; rewrite (app_comm_cons l1 _ B) ; rewrite (app_comm_cons _ _ A0) ;
        intros pi2 IHsize.
      refine (IHsize _ _ _ _ pi1 pi2 _ _) ; simpl; lia.
Qed.

Lemma cut_elim : forall l,
    mll_cut l ->
    mll l.
Proof with try assumption.
  intros l pi.
  induction pi; try constructor...
  apply cut_admissible with A...
Qed.