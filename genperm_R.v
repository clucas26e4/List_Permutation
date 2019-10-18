(** * Factorized statements for different notions of permutation *)

Require Import CMorphisms.
Require Import List.

Require Import Injective.
Require Import List_Type.

Require Import Fun_nat.
Require Import Perm.
Require Import Perm_R_more.
Require Import Perm_R_solve.
Require Import CyclicPerm_R.
Require Import CyclicPerm_R_solve.
Require Import misc.


(** ** Definitions
 parametrized by a boolean. *)
Definition cond_PCperm (b : bool) l : Type :=
  if b then is_perm l = true else cond_cyclicPerm l.

Lemma PCperm_Perm : forall b l, cond_PCperm b l -> is_perm l = true.
Proof with try reflexivity; try assumption.
  intros b; case b; simpl; intros l Hperm...
  destruct Hperm as [((n , m) & Heq) | Heq].
  - rewrite Heq; apply cfun_is_perm.
  - rewrite Heq; apply Id_is_perm.
Qed.

Definition cond_PEperm (b : bool) l : Type :=
  if b then is_perm l = true else (l = Id (length l)).

Lemma PEperm_Perm : forall b l, cond_PEperm b l -> is_perm l = true.
Proof. now intros b l Hperm; destruct b; [ | rewrite Hperm; apply Id_is_perm ]. Qed.


(** Permutation or cyclic permutation *)

Definition PCperm_R {A} (b : bool) (l1 l2 : list A) : Type :=
  { p : _ & cond_PCperm b p & prod (length p = length l1) (l2 = p ∘ l1)}.

(** Permutation or equality *)
Definition PEperm_R {A} (b : bool) (l1 l2 : list A) : Type :=
  { p : _ & cond_PEperm b p & prod (length p = length l1) (l2 = p ∘ l1)}.

(** ** Permutation or cyclic permutation *)

(** unfolding into [Permutation] or [CPermutation] *)
Ltac hyps_PCperm_R_unfold :=
  match goal with
  | H : PCperm_R _ _ _ |- _ => unfold PCperm_R in H ; hyps_PCperm_R_unfold
  | _ => idtac
  end.

(** automatic solving *)
Ltac PCperm_R_solve :=
  hyps_PCperm_R_unfold; simpl;
  match goal with
  | |- PCperm_R ?b _ _ => unfold PCperm_R ; destruct b ;
                        simpl ; PCperm_R_solve
  | |- Perm_R _ _  => Perm_R_solve
  | |- CyclicPerm_R _ _  => CyclicPerm_R_solve
  end.

(** *** Properties *)

Instance PCperm_Perm_R {A} b : Proper (PCperm_R b ==> (@Perm_R A)) (fun a => a).
Proof. now destruct b; intros; [ | apply CyclicPerm_Perm_R ]. Defined.

Instance CylicPerm_PCperm_R {A} b : Proper (CyclicPerm_R ==> PCperm_R b) (fun a : (list A) => a).
Proof. now destruct b; intros; [ apply CyclicPerm_Perm_R | ]. Defined.

Instance PCperm_R_refl {A} b : Reflexive (@PCperm_R A b).
Proof. destruct b; intros ?; reflexivity. Defined.

Instance PCperm_R_sym {A} b : Symmetric (@PCperm_R A b).
Proof. now destruct b; intros ? ? ?; symmetry. Defined.

Instance PCperm_R_trans {A} b : Transitive (@PCperm_R A b).
Proof. now destruct b; intros l l' l'' H1 H2; transitivity l'. Defined.

Instance PCperm_R_equiv {A} b : Equivalence (@PCperm_R A b).
Proof. split; [ apply PCperm_R_refl | apply PCperm_R_sym | apply PCperm_R_trans ]. Qed.

Lemma PCperm_R_swap {A} b : forall a1 a2 : A, PCperm_R b (a1 :: a2 :: nil) (a2 :: a1 :: nil).
Proof. destruct b; [ apply Perm_R_swap | apply CyclicPerm_R_swap ]. Defined.

Lemma PCperm_R_last {A} b : forall (a : A) l, PCperm_R b (a :: l) (l ++ a :: nil).
Proof. destruct b; intros; [ apply Perm_R_cons_append | apply CyclicPerm_R_last ]. Defined.

Lemma PCperm_R_app_comm {A} b : forall l l' : list A, PCperm_R b (l ++ l') (l' ++ l).
Proof. destruct b; [ apply Perm_R_app_comm | apply CyclicPerm_R_commu ]. Defined.

Lemma PCperm_R_app_rot {A} b : forall l1 l2 l3 : list A, PCperm_R b  (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
Proof. destruct b ; [ apply Perm_R_app_rot | apply CyclicPerm_R_app_rot ]. Defined.

Lemma PCperm_R_nil {A} b : forall l : list A, PCperm_R b nil l -> l = nil.
Proof. destruct b; [ apply Perm_R_nil | apply CyclicPerm_R_nil ]. Qed.

Lemma PCperm_R_nil_cons {A} b : forall l (a : A), PCperm_R b nil (a :: l) -> False.
Proof. destruct b; [ apply Perm_R_nil_cons | apply CyclicPerm_R_nil_cons ]. Qed.

Lemma PCperm_R_length_1_inv {A} b : forall (a : A) l, PCperm_R b (a :: nil) l -> l = a :: nil.
Proof. now destruct b; intros; [ apply Perm_R_length_1_inv | apply CyclicPerm_R_one_inv ]. Qed.

Lemma PCperm_length_1_inv b : forall p, cond_PCperm b p -> length p = 1 -> p = Id 1.
Proof.
  intros p Hperm Hlen.
  destruct p; [ | destruct p]; try now inversion Hlen.
  destruct n; [ reflexivity | ].
  exfalso.
  apply PCperm_Perm in Hperm; apply andb_prop in Hperm as [Hal _]; inversion Hal.
Qed.

Lemma PCperm_R_length_2_inv {A} b : forall (a1 : A) a2 l,
  PCperm_R b (a1 :: a2 :: nil) l -> { l = a1 :: a2 :: nil } + { l = a2 :: a1 :: nil }.
Proof. destruct b; [ apply Perm_R_length_2_inv | apply CyclicPerm_R_two_inv ]. Qed.

Lemma PCperm_R_vs_elt_inv {A} b : forall (a : A) l l1 l2,
  PCperm_R b l (l1 ++ a :: l2) ->
  {'(l1', l2') : _ & l = l1' ++ a :: l2' & PEperm_R b (l2 ++ l1) (l2' ++ l1') }.
Proof with try reflexivity.
destruct b ; intros a l l1 l2 HC.
- destruct (Perm_R_vs_elt_inv _ _ _ _ HC) as ((l' & l'') & Heq) ; subst.
  exists (l',l'')...
  simpl in HC ; simpl.
  apply Perm_R_app_inv, Perm_R_sym in HC.
  eapply Perm_R_trans ; [ apply Perm_R_app_comm | ].
  eapply Perm_R_trans ; [ eassumption | ].
  apply Perm_R_app_comm.
- apply CyclicPerm_R_vs_elt_inv in HC.
  destruct HC as [(l' & l'') Heq1 Heq2] ; subst.
  exists (l',l'')...
  split with (Id (length (l'' ++ l'))); repeat split.
  + simpl; rewrite seq_length...
  + rewrite Heq1; length_lia.
  + rewrite Heq1; rewrite app_Id...
Qed.

Lemma PCperm_R_vs_cons_inv {A} b : forall (a : A) l l1,
  PCperm_R b l (a :: l1) ->
  {'(l1', l2') : _ & l = l1' ++ a :: l2' & PEperm_R b l1 (l2' ++ l1') }.
Proof with try reflexivity.
intros a l l1 HP.
rewrite <- app_nil_l in HP.
apply PCperm_R_vs_elt_inv in HP.
destruct HP as [(l' & l'') HP Heq] ; subst.
exists (l',l'')...
now rewrite app_nil_r in Heq.
Defined.

Instance PCperm_R_map {A B} (f : A -> B) b : Proper (PCperm_R b ==> PCperm_R b) (map f).
Proof. now destruct b; intros ? ? ?; [ apply Perm_R_map | apply CyclicPerm_R_map ]. Defined.

Lemma PCperm_R_map_inv {A B} b : forall (f : A -> B) l1 l2,
  PCperm_R b l1 (map f l2) ->
  { l : _ & l1 = map f l & (PCperm_R b l2 l) }.
Proof. destruct b ; [ apply Perm_R_map_inv | apply CyclicPerm_R_map_inv ]. Defined.

Instance PCperm_R_in {A} b (a : A) : Proper (PCperm_R b ==> Basics.impl) (In a).
Proof. now destruct b; intros l ? ? ?; [ apply Perm_R_in with l | apply CyclicPerm_R_in with l ]. Qed.

Instance PCperm_R_Forall {A} b (P : A -> Prop) : Proper (PCperm_R b ==> Basics.impl) (Forall P).
Proof. now destruct b ; intros l ? ? ?; [ apply Perm_R_Forall with l | apply CyclicPerm_R_Forall with l ]. Qed.

Instance PCperm_R_Exists {A} b (P : A -> Prop) : Proper (PCperm_R b ==> Basics.impl) (Exists P).
Proof. now destruct b ; intros l ? ? ?; [ apply Perm_R_Exists with l | apply CyclicPerm_R_Exists with l ]. Qed.

Lemma PCperm_R_Forall2 {A B} b (P : A -> B -> Type) : forall l1 l1' l2,
  PCperm_R b l1 l1' -> Forall2_Type P l1 l2 -> 
    { l2' : _ & PCperm_R b l2 l2' & Forall2_Type P l1' l2' }.
Proof. destruct b; [ apply Perm_R_Forall2 | apply CyclicPerm_R_Forall2 ]. Qed.

Lemma PCperm_R_image {A B} b : forall (f : A -> B) a l l', PCperm_R b (a :: l) (map f l') -> { a' | a = f a' }.
Proof. destruct b; [ apply Perm_R_image | apply CyclicPerm_R_image ]. Qed.

Instance PCperm_R_Forall_R {A} b (P : A -> Type) : Proper (PCperm_R b ==> Basics.arrow) (Forall_Type P).
Proof. now destruct b ; intros l ? ? ?; [ apply Perm_R_Forall_Type with l
                                        | apply CyclicPerm_R_Forall_Type with l ]. Qed.

Instance PCperm_R_Exists_R {A} b (P : A -> Type) : Proper (PCperm_R b ==> Basics.arrow) (Exists_Type P).
Proof. now destruct b ; intros l ? ? ?; [ apply Perm_R_Exists_Type with l
                                        | apply CyclicPerm_R_Exists_Type with l ]. Qed.


(** ** Permutation or equality *)

(** unfolding into [Permutation] or [eq] and automatic solving *)
Ltac hyps_PEperm_R_unfold :=
  match goal with
  | H : PEperm_R _ _ _ |- _ => unfold PEperm_R in H ; hyps_PEperm_R_unfold
  | _ => idtac
  end.

(** automatic solving *)
Ltac PEperm_R_solve :=
  hyps_PEperm_R_unfold; simpl ;
  match goal with
  | |- PEperm_R ?b _ _ => unfold PEperm_R ; destruct b ;
                        simpl ; PEperm_R_solve
  | |- Perm_R _ _  => Perm_R_solve
  | |- eq _ _  => reflexivity
  end.

(** *** Properties *)

Instance PEperm_R_eq {A} : Proper (PEperm_R false ==> (@eq (list A))) id.
Proof.
  intros l l' [p Hp [Hlen Heq]]; simpl in Hp.
  now rewrite Hp in Heq; rewrite Hlen in Heq; rewrite app_Id in Heq; rewrite Heq.
Defined.

Lemma PEperm_R_false {A} : forall (l1 l2 : list A), PEperm_R false l1 l2 -> l1 = l2.
Proof. apply PEperm_R_eq. Qed.

Lemma eq_PEperm_R_false {A} : forall (l1 l2 : list A), l1 = l2 -> PEperm_R false l1 l2.
Proof.
intros l1 l2 Heq; subst.
now split with (Id (length l2)); repeat split; simpl; rewrite ? seq_length; [ | | rewrite app_Id ].
Defined.

Instance PEperm_perm_R {A} b : Proper (PEperm_R b ==> (@Perm_R A)) id.
Proof. destruct b ; intros l l' HP ; simpl in HP; now rewrite HP. Defined.

Instance PEperm_R_refl {A} b : Reflexive (@PEperm_R A b).
Proof. destruct b ; intros l; [ apply Perm_R_refl | now apply eq_PEperm_R_false ]. Defined.

Instance PEperm_R_sym {A} b : Symmetric (@PEperm_R A b).
Proof. now destruct b; intros l l' Hp; [ symmetry
                                       | apply PEperm_R_false in Hp; apply eq_PEperm_R_false ]. Defined.

Instance PEperm_R_trans {A} b : Transitive (@PEperm_R A b).
Proof. now destruct b ; intros l l' l'' HP1 HP2; [ transitivity l' | rewrite PEperm_R_false with l l' ]. Defined.

Instance PEperm_R_equiv {A} b : Equivalence (@PEperm_R A b).
Proof. split; [ apply PEperm_R_refl | apply PEperm_R_sym | apply PEperm_R_trans ]. Qed.

Instance eq_PEperm_R {A} b : Proper (eq ==> PEperm_R b) (@id (list A)).
Proof. destruct b; intros l l' Heq; subst; reflexivity. Defined.

Instance PEperm_R_cons {A} b : Proper (eq ==> PEperm_R b ==> PEperm_R b) (@cons A).
Proof. now destruct b; intros x y Heq l1 l2 HP; subst; [ apply Perm_R_cons
                                                       | rewrite (PEperm_R_false _ _ HP) ]. Defined.

Instance PEperm_R_app {A} b : Proper (PEperm_R b ==> PEperm_R b ==> PEperm_R b) (@app A).
Proof.
now destruct b; simpl; intros l m HP1 l' m' HP2; [ apply Perm_R_app
                                                 | rewrite (PEperm_R_false _ _ HP1), (PEperm_R_false _ _ HP2) ].
Defined.

Lemma PEperm_R_app_tail {A} b : forall l l' tl : list A, PEperm_R b l l' -> PEperm_R b (l ++ tl) (l' ++ tl).
Proof. now destruct b; simpl; intros l l' tl HP; [ apply Perm_R_app_tail
                                                 | rewrite (PEperm_R_false _ _ HP) ]. Defined.

Lemma PEperm_R_app_head {A} b : forall l tl tl' : list A, PEperm_R b tl tl' -> PEperm_R b (l ++ tl) (l ++ tl').
Proof. now destruct b; simpl; intros l tl tl' HP; [ apply Perm_R_app_head
                                                  | rewrite (PEperm_R_false _ _ HP) ]. Defined.

Lemma PEperm_R_add_inside {A} b : forall (a : A) l l' tl tl',
  PEperm_R b l l' -> PEperm_R b tl tl' -> PEperm_R b (l ++ a :: tl) (l' ++ a :: tl').
Proof.
now destruct b ; simpl ; intros a l l' tl tl' HP1 HP2;
  [ apply Perm_R_add_inside
  | rewrite (PEperm_R_false _ _ HP1),  (PEperm_R_false _ _ HP2) ].
Defined.

Lemma PEperm_R_nil {A} b : forall l, @PEperm_R A b nil l -> l = nil.
Proof. now destruct b ; intros l H; [ apply Perm_R_nil | rewrite (PEperm_R_false _ _ H) ]. Qed.

Lemma PEperm_nil_cons {A} b : forall l (a : A), PEperm_R b nil (a :: l) -> False.
Proof. now destruct b ; intros l a H; [ apply Perm_R_nil_cons with l a
                                      | apply PEperm_R_false in H; inversion H ]. Qed.

Lemma PEperm_R_length_1_inv {A} b : forall (a : A) l, PEperm_R b (a :: nil) l -> l = a :: nil.
Proof. now destruct b ; intros a l H; [ apply Perm_R_length_1_inv | rewrite (PEperm_R_false _ _ H) ]. Qed.

Lemma PEperm_R_length_2_inv {A} b : forall (a1 : A) a2 l,
  PEperm_R b (a1 :: a2 :: nil) l -> { l = a1 :: a2 :: nil } + { l = a2 :: a1 :: nil }.
Proof. now destruct b ; intros a1 a2 l H; [ apply Perm_R_length_2_inv
                                          | left; rewrite (PEperm_R_false _ _ H) ]. Qed.

Lemma PEperm_R_vs_elt_inv {A} b : forall (a : A) l l1 l2,
  PEperm_R b l (l1 ++ a :: l2) ->
    {'(l1',l2') : _ & l = l1' ++ a :: l2' & PEperm_R b (l1 ++ l2) (l1' ++ l2') }.
Proof.
destruct b ; simpl ; intros a l l1 l2 HP.
- destruct (Perm_R_vs_elt_inv _ _ _ _ HP) as [(l',l'') Heq]; subst.
  apply Perm_R_app_inv in HP.
  apply Perm_R_sym in HP.
  now exists (l',l'').
- rewrite (PEperm_R_false _ _ HP); now exists (l1,l2).
Defined.

Lemma PEperm_R_vs_cons_inv {A} b : forall (a : A) l l1,
  PEperm_R b l (a :: l1) ->
    {'(l1',l2') : _ & l = l1' ++ a :: l2' & PEperm_R b l1 (l1' ++ l2') }.
Proof. intros a l l1 HP; rewrite <- (app_nil_l l1); now apply PEperm_R_vs_elt_inv. Defined.

Instance PEperm_R_in {A} b (a : A) : Proper (PEperm_R b ==> Basics.impl) (In a).
Proof. now destruct b ; simpl ; intros l l' HP HIn; [ apply Perm_R_in with l
                                                    | rewrite <- (PEperm_R_false _ _ HP) ]. Qed.

Instance PEperm_R_Forall {A} b (P : A -> Prop) : Proper (PEperm_R b ==> Basics.impl) (Forall P).
Proof. now destruct b ; simpl ; intros l1 l2 HP HF; [ apply Perm_R_Forall with l1
                                                    | rewrite<- (PEperm_R_false _ _ HP) ]. Qed.

Instance PEperm_R_Exists {A} b (P : A -> Prop) : Proper (PEperm_R b ==> Basics.impl) (Exists P).
Proof. now destruct b ; simpl ; intros l1 l2 HP HF; [ apply Perm_R_Exists with l1
                                                    | rewrite<- (PEperm_R_false _ _ HP) ]. Qed.

Lemma PEperm_R_Forall2 {A B} b (P : A -> B -> Prop) : forall l1 l1' l2,
  PEperm_R b l1 l1' -> Forall2_Type P l1 l2 -> 
    { l2' : _ & PEperm_R b l2 l2' & Forall2_Type P l1' l2' }.
Proof.
destruct b ; [ apply Perm_R_Forall2 | ].
intros l1 l1' l2 HE HF ; simpl in HE ; subst.
rewrite (PEperm_R_false _ _ HE) in HF; now exists l2.
Defined.

Instance PEperm_R_map {A B} (f : A -> B) b : Proper (PEperm_R b ==> PEperm_R b) (map f).
Proof. now destruct b ; intros l l' HP; [ apply Perm_R_map | rewrite (PEperm_R_false _ _ HP) ]. Defined.

Instance PEperm_R_Forall_R {A} b (P : A -> Type) : Proper (PEperm_R b ==> Basics.arrow) (Forall_Type P).
Proof. now destruct b ; simpl ; intros l1 l2 HP HF; [ apply Perm_R_Forall_Type with l1
                                                    | rewrite<- (PEperm_R_false _ _ HP) ]. Qed.

Instance PEperm_R_Exists_R {A} b (P : A -> Type) : Proper (PEperm_R b ==> Basics.arrow) (Exists_Type P).
Proof. now destruct b ; simpl ; intros l1 l2 HP HF; [ apply Perm_R_Exists_Type with l1
                                                    | rewrite<- (PEperm_R_false _ _ HP) ]. Qed.

Lemma PEperm_R_map_inv {A B} b : forall (f : A -> B) l1 l2,
  PEperm_R b l1 (map f l2) -> { l : _ & l1 = map f l & PEperm_R b l2 l }.
Proof. now destruct b ; simpl ; intros f l1 l2 HP; [ apply Perm_R_map_inv
                                                   | rewrite (PEperm_R_false _ _ HP); exists l2 ]. Defined.

Instance PEperm_R_rev {A} b : Proper (PEperm_R b ==> PEperm_R b) (@rev A).
Proof. now destruct b ; intros l1 l2 HP; [ apply Perm_R_rev' | rewrite (PEperm_R_false _ _ HP) ]. Defined.

Lemma PEperm_R_map_inv_inj {A B} b : forall f : A -> B, injective f -> forall l1 l2,
  PEperm_R b (map f l1) (map f l2) -> PEperm_R b l1 l2.
Proof. now destruct b ; intros f Hi l1 l2 HP; [ apply Perm_R_map_inv_inj with f
                                              | apply PEperm_R_false, map_inj in HP; subst ]. Defined.

Lemma PEperm_R_image {A B} b : forall (f : A -> B) a l l', PEperm_R b (a :: l) (map f l') -> { a' | a = f a' }.
Proof.
destruct b ; intros f a l l' H.
- now apply Perm_R_image with l l'.
- apply PEperm_R_false in H; destruct l'; inversion H; subst; now eexists.
Qed.


(** ** From PEperm to PCperm *)

Instance PEperm_PCperm_R {A} b : Proper (PEperm_R b ==> PCperm_R b) (@id (list A)).
Proof. now destruct b ; simpl ; intros l l' HP; [ | rewrite (PEperm_R_false _ _ HP); reflexivity ]. Defined.

Instance PEperm_PCperm_R_cons {A} b : Proper (eq ==> PEperm_R b ==> PCperm_R b) (@cons A).
Proof. now intros x y Heq l1 l2 HP ; subst; apply PEperm_PCperm_R, PEperm_R_cons. Defined.

Instance PEperm_PCperm_R_app {A} b : Proper (PEperm_R b ==> PEperm_R b ==> PCperm_R b) (@app A).
Proof. now intros l1 l1' HPhd l2 l2' HPtl; apply PEperm_PCperm_R; rewrite HPhd, HPtl. Defined.

