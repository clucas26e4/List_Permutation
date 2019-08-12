(* genperm Library *)

(* with output in Type *)

(** * Factorized statements for different notions of permutation *)

Require Import CMorphisms.
Require Import List.

Require Import Injective.
Require Import List_Type.
Require Import List_nat.
Require Import List_more2.
Require Import Fun_nat.
Require Import Perm.
Require Import Perm_R_more.
Require Import Perm_R_solve.
Require Import CyclicPerm_R.
Require Import CyclicPerm_R_solve.



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
Proof with try assumption.
  intro b; case b; simpl; intros l Hperm...
  rewrite Hperm; apply Id_is_perm.
Qed.
  
(** Permutation or cyclic permutation *)

Definition PCperm_R {A} (b : bool) :=
  if b then @Perm_R A else @CyclicPerm_R A.

(** Permutation or equality *)
Definition PEperm_R {A} (b : bool) :=
  if b then @Perm_R A else @eq (list A).


(** ** Permutation or cyclic permutation *)

(** unfolding into [Permutation] or [CPermutation] *)
Ltac hyps_PCperm_R_unfold :=
  match goal with
  | H : PCperm_R _ _ _ |- _ => unfold PCperm_R in H ; hyps_PCperm_R_unfold
  | _ => idtac
  end.

(** automatic solving *)
Ltac PCperm_R_solve :=
  hyps_PCperm_R_unfold ;
  simpl ;
  match goal with
  | |- PCperm_R ?b _ _ => unfold PCperm_R ; destruct b ;
                        simpl ; PCperm_R_solve
  | |- Perm_R _ _  => Perm_R_solve
  | |- CyclicPerm_R _ _  => CyclicPerm_R_solve
  end.

(** *** Properties *)
(*
Lemma properties_PCperm_R_PCperm {A} b :
  forall (P : list A -> list A ->  Type),
    (forall l1 l2, PCperm_R b l1 l2 -> P l1 l2) ->
    forall p l1,
      cond_PCperm b p ->
      length p = length l1 ->
      P l1 (app_nat_fun p l1).
Proof with try reflexivity; try assumption.
  intros P H p l1 Hperm Hlen.
  apply H.
  revert Hperm; destruct b; simpl; intros Hperm.
  - split with (existT _ p Hperm).
    unfold app_perm.
    simpl.
    split...
  - split with (existT _ p Hperm).
    simpl; split...
Qed.

Lemma properties_PEperm_R_PEperm {A} b :
  forall (P : list A -> list A ->  Type),
    (forall l1 l2, PEperm_R b l1 l2 -> P l1 l2) ->
    forall p l1,
      cond_PEperm b p ->
      length p = length l1 ->
      P l1 (app_nat_fun p l1).
Proof with try reflexivity; try assumption.
  intros P H p l1 Hperm Hlen.
  apply H.
  revert Hperm; destruct b; simpl; intros Hperm.
  - split with (existT _ p Hperm).
    unfold app_perm.
    simpl.
    split...
  - rewrite Hperm.
    rewrite Hlen.
    symmetry;apply app_Id.
Qed.*)

Instance PCperm_Perm_R {A} b : Proper (PCperm_R b ==> (@Perm_R A)) (fun a => a).
Proof with try assumption.
  destruct b ; intros l l' HP...
  apply CyclicPerm_Perm_R...
Defined.

Instance CylicPerm_PCperm_R {A} b : Proper (CyclicPerm_R ==> PCperm_R b) (fun a : (list A) => a).
Proof with try assumption.
  destruct b ; intros l l' HC...
  apply CyclicPerm_Perm_R...
Defined.

Instance PCperm_R_refl {A} b : Reflexive (@PCperm_R A b).
Proof.
destruct b ; intros l.
- apply Perm_R_refl.
- apply CyclicPerm_R_refl.
Defined.

Instance PCperm_R_sym {A} b : Symmetric (@PCperm_R A b).
Proof with try assumption.
destruct b ; intros l l' H.
- apply Perm_R_sym...
- apply CyclicPerm_R_sym...
Defined.

Instance PCperm_R_trans {A} b : Transitive (@PCperm_R A b).
Proof with try eassumption.
destruct b ; intros l l' l'' H1 H2.
- eapply Perm_R_trans...
- eapply CyclicPerm_R_trans...
Defined.

Instance PCperm_R_equiv {A} b : Equivalence (@PCperm_R A b).
Proof.
split.
- apply PCperm_R_refl.
- apply PCperm_R_sym.
- apply PCperm_R_trans.
Qed.

Lemma PCperm_R_swap {A} b : forall a1 a2 : A,
  PCperm_R b (a1 :: a2 :: nil) (a2 :: a1 :: nil).
Proof.
destruct b ; intros.
- apply Perm_R_swap.
- apply CyclicPerm_R_swap.
Defined.

Lemma PCperm_R_last {A} b : forall (a : A) l,
  PCperm_R b (a :: l) (l ++ a :: nil).
Proof.
destruct b ; intros ;
  rewrite <- (app_nil_l l) ; rewrite app_comm_cons.
- apply Perm_R_cons_append.
- apply CyclicPerm_R_last.
Defined.

Lemma PCperm_R_app_comm {A} b : forall l l',
  @PCperm_R A b (l ++ l') (l' ++ l).
Proof.
destruct b ; intros.
- apply Perm_R_app_comm.
- apply CyclicPerm_R_commu.
Defined.

Lemma PCperm_R_app_rot {A} b : forall l1 l2 l3,
  @PCperm_R A b  (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
Proof.
destruct b ; intros.
- apply Perm_R_app_rot.
- apply CyclicPerm_R_app_rot.
Defined.

Lemma PCperm_R_nil {A} b : forall l,
  @PCperm_R A b nil l -> l = nil.
Proof with try assumption.
destruct b ; intros.
- apply Perm_R_nil...
- apply CyclicPerm_R_nil...
Qed.

Lemma PCperm_R_nil_cons {A} b : forall l (a : A),
  PCperm_R b nil (a :: l) -> False.
Proof with try eassumption.
destruct b ; intros.
- eapply Perm_R_nil_cons...
- eapply CyclicPerm_R_nil_cons...
Qed.

Lemma PCperm_R_length_1_inv {A} b : forall (a : A) l,
  PCperm_R b (a :: nil) l -> l = a :: nil.
Proof with try assumption.
destruct b ; intros.
- apply Perm_R_length_1_inv...
- apply CyclicPerm_R_one_inv...
Qed.

Lemma PCperm_length_1_inv b : forall p,
    cond_PCperm b p ->
    length p = 1 ->
    p = Id 1.
Proof with try reflexivity.
  intros p Hperm Hlen.
  destruct p; [ | destruct p]; try now inversion Hlen.
  destruct n...
  exfalso.
  apply PCperm_Perm in Hperm; apply andb_prop in Hperm as [Hal _]; inversion Hal.
Qed.


Lemma PCperm_R_length_2_inv {A} b : forall (a1 : A) a2 l,
  PCperm_R b (a1 :: a2 :: nil) l -> { l = a1 :: a2 :: nil } + { l = a2 :: a1 :: nil }.
Proof with try assumption.
destruct b ; intros.
- apply Perm_R_length_2_inv...
- apply CyclicPerm_R_two_inv...
Qed.

Lemma PCperm_R_vs_elt_inv {A} b : forall (a : A) l l1 l2,
  PCperm_R b l (l1 ++ a :: l2) ->
  { pl : _ & l = fst pl ++ a :: snd pl & PEperm_R b (l2 ++ l1) (snd pl ++ fst pl) }.
Proof with try reflexivity.
destruct b ; intros a l l1 l2 HC.
- assert (Heq := HC).
  apply Perm_R_vs_elt_inv in Heq.
  destruct Heq as ((l' & l'') & Heq) ; subst.
  exists (l',l'')...
  simpl in HC ; simpl.
  apply Perm_R_app_inv in HC.
  apply Perm_R_sym in HC.
  eapply Perm_R_trans ; [ eapply Perm_R_app_comm | ].
  eapply Perm_R_trans ; [ eassumption | ].
  apply Perm_R_app_comm.
- apply CyclicPerm_R_vs_elt_inv in HC.
  destruct HC as [(l' & l'') Heq1 Heq2] ; subst.
  exists (l',l'')...
  assumption.
Qed.

Lemma PCperm_R_vs_cons_inv {A} b : forall (a : A) l l1,
  PCperm_R b l (a :: l1) ->
  { pl : _ & l = fst pl ++ a :: snd pl & PEperm_R b l1 (snd pl ++ fst pl) }.
Proof with try reflexivity.
intros a l l1 HP.
rewrite <- app_nil_l in HP.
apply PCperm_R_vs_elt_inv in HP.
destruct HP as [(l' & l'') HP Heq] ; subst.
exists (l',l'')...
rewrite app_nil_r in Heq.
assumption.
Defined.

Instance PCperm_R_map {A B} (f : A -> B) b :
  Proper (PCperm_R b ==> PCperm_R b) (map f).
Proof with try assumption.
destruct b ; intros l1 l2 HC.
- apply Perm_R_map...
- apply CyclicPerm_R_map...
Defined.

Lemma PCperm_R_map_inv {A B} b : forall (f : A -> B) l1 l2,
  PCperm_R b l1 (map f l2) ->
  { l : _ & l1 = map f l & (PCperm_R b l2 l) }.
Proof.
destruct b ; intros.
- eapply Perm_R_map_inv ; eassumption.
- eapply CyclicPerm_R_map_inv ; eassumption.
Defined.

Instance PCperm_R_in {A} b (a : A) : Proper (PCperm_R b ==> Basics.impl) (In a).
Proof with try eassumption.
destruct b ; intros l l' HP HIn.
- eapply Perm_R_in...
- eapply CyclicPerm_R_in...
Qed.

Instance PCperm_R_Forall {A} b (P : A -> Prop) :
  Proper (PCperm_R b ==> Basics.impl) (Forall P).
Proof with try eassumption.
destruct b ; intros l1 l2 HP HF.
- eapply Perm_R_Forall...
- eapply CyclicPerm_R_Forall...
Qed.

Instance PCperm_R_Exists {A} b (P : A -> Prop) :
  Proper (PCperm_R b ==> Basics.impl) (Exists P).
Proof with try eassumption.
destruct b ; intros l1 l2 HP HE.
- eapply Perm_R_Exists...
- eapply CyclicPerm_R_Exists...
Qed.

Lemma PCperm_R_Forall2 {A B} b (P : A -> B -> Type) :
  forall l1 l1' l2, PCperm_R b l1 l1' -> Forall2_Type P l1 l2 -> 
    { l2' : _ & PCperm_R b l2 l2' & Forall2_Type P l1' l2' }.
Proof.
destruct b ; [ apply Perm_R_Forall2 | apply CyclicPerm_R_Forall2 ].
Qed.

Lemma PCperm_R_image {A B} b : forall (f : A -> B) a l l',
  PCperm_R b (a :: l) (map f l') -> { a' | a = f a' }.
Proof with try eassumption.
destruct b ; intros.
- eapply Perm_R_image...
- eapply CyclicPerm_R_image...
Qed.

Instance PCperm_R_Forall_R {A} b (P : A -> Type) :
  Proper (PCperm_R b ==> Basics.arrow) (Forall_Type P).
Proof with try eassumption.
destruct b ; intros l1 l2 HP HF.
- eapply Perm_R_Forall_Type...
- eapply CyclicPerm_R_Forall_Type...
Qed.

Instance PCperm_R_Exists_R {A} b (P : A -> Type) :
  Proper (PCperm_R b ==> Basics.arrow) (Exists_Type P).
Proof with try eassumption.
destruct b ; intros l1 l2 HP HE.
- eapply Perm_R_Exists_Type...
- eapply CyclicPerm_R_Exists_Type...
Qed.


(** ** Permutation or equality *)

(** unfolding into [Permutation] or [eq] and automatic solving *)
Ltac hyps_PEperm_R_unfold :=
  match goal with
  | H : PEperm_R _ _ _ |- _ => unfold PEperm_R in H ; hyps_PEperm_R_unfold
  | _ => idtac
  end.

(** automatic solving *)
Ltac PEperm_R_solve :=
  hyps_PEperm_R_unfold ;
  simpl ;
  match goal with
  | |- PEperm_R ?b _ _ => unfold PEperm_R ; destruct b ;
                        simpl ; PEperm_R_solve
  | |- Perm_R _ _  => Perm_R_solve
  | |- eq _ _  => reflexivity
  end.

(** *** Properties *)

Instance PEperm_perm_R {A} b : Proper (PEperm_R b ==> (@Perm_R A)) id.
Proof.
destruct b ; intros l l' HP ; simpl in HP ; now subst.
Defined.

Instance PEperm_R_refl {A} b : Reflexive (@PEperm_R A b).
Proof.
destruct b ; intros l.
- apply Perm_R_refl.
- reflexivity.
Defined.

Instance PEperm_R_sym {A} b : Symmetric (@PEperm_R A b).
Proof with try assumption.
destruct b ; intros l l' HP.
- apply Perm_R_sym...
- symmetry...
Defined.

Instance PEperm_R_trans {A} b : Transitive (@PEperm_R A b).
Proof with try eassumption.
destruct b ; intros l l' l'' HP1 HP2.
- eapply Perm_R_trans...
- etransitivity...
Defined.

Instance PEperm_R_equiv {A} b : Equivalence (@PEperm_R A b).
Proof.
split.
- apply PEperm_R_refl.
- apply PEperm_R_sym.
- apply PEperm_R_trans.
Qed.

Instance eq_PEperm_R {A} b : Proper (eq ==> PEperm_R b) (@id (list A)).
Proof.
destruct b ; intros l l' Heq ; subst.
- apply Perm_R_refl.
- reflexivity.
Defined.

Instance PEperm_R_cons {A} b :
  Proper (eq ==> PEperm_R b ==> PEperm_R b) (@cons A).
Proof.
destruct b ; intros x y Heq l1 l2 HP ; subst.
- now apply Perm_R_cons.
- now rewrite HP.
Defined.

Instance PEperm_R_app {A} b : Proper (PEperm_R b ==> PEperm_R b ==> PEperm_R b) (@app A).
Proof.
destruct b ; simpl ; intros l m HP1 l' m' HP2.
- now apply Perm_R_app.
- now subst.
Defined.

Lemma PEperm_R_app_tail {A} b : forall l l' tl : list A,
  PEperm_R b l l' -> PEperm_R b (l ++ tl) (l' ++ tl).
Proof.
destruct b ; simpl ; intros l l' tl HP.
- now apply Perm_R_app_tail.
- now subst.
Defined.

Lemma PEperm_R_app_head {A} b : forall l tl tl' : list A,
  PEperm_R b tl tl' -> PEperm_R b (l ++ tl) (l ++ tl').
Proof.
destruct b ; simpl ; intros l tl tl' HP.
- now apply Perm_R_app_head.
- now subst.
Defined.

Lemma PEperm_R_add_inside {A} b : forall (a : A) l l' tl tl',
  PEperm_R b l l' -> PEperm_R b tl tl' -> PEperm_R b (l ++ a :: tl) (l' ++ a :: tl').
Proof.
destruct b ; simpl ; intros a l l' tl tl' HP1 HP2.
- now apply Perm_R_add_inside.
- now subst.
Defined.

Lemma PEperm_R_nil {A} b : forall l, @PEperm_R A b nil l -> l = nil.
Proof with try assumption.
destruct b ; intros.
- apply Perm_R_nil...
- symmetry...
Qed.

Lemma PEperm_nil_cons {A} b : forall l (a : A),
  PEperm_R b nil (a :: l) -> False.
Proof with try eassumption.
destruct b ; intros l a H.
- eapply Perm_R_nil_cons...
- inversion H.
Qed.

Lemma PEperm_R_length_1_inv {A} b : forall (a : A) l,
  PEperm_R b (a :: nil) l -> l = a :: nil.
Proof with try assumption.
destruct b ; intros.
- apply Perm_R_length_1_inv...
- symmetry...
Qed.

Lemma PEperm_R_length_2_inv {A} b : forall (a1 : A) a2 l,
  PEperm_R b (a1 :: a2 :: nil) l -> { l = a1 :: a2 :: nil } + { l = a2 :: a1 :: nil }.
Proof with try assumption.
destruct b ; intros.
- apply Perm_R_length_2_inv...
- left ; symmetry...
Qed.

Lemma PEperm_R_vs_elt_inv {A} b : forall (a : A) l l1 l2,
  PEperm_R b l (l1 ++ a :: l2) ->
  { pl : _ & l = fst pl ++ a :: snd pl & PEperm_R b (l1 ++ l2) (fst pl ++ snd pl) }.
Proof with try reflexivity.
destruct b ; simpl ; intros a l l1 l2 HP.
- assert (HP' := HP).
  apply Perm_R_vs_elt_inv in HP'.
  destruct HP' as ((l' & l'') & Heq) ; subst.
  apply Perm_R_app_inv in HP.
  apply Perm_R_sym in HP.
  exists (l',l'')...
  assumption.
- subst.
  exists (l1,l2)...
Defined.

Lemma PEperm_R_vs_cons_inv {A} b : forall (a : A) l l1,
  PEperm_R b l (a :: l1) ->
  { pl : _ & l = fst pl ++ a :: snd pl & PEperm_R b l1 (fst pl ++ snd pl) }.
Proof.
intros a l l1 HP.
rewrite <- (app_nil_l l1).
eapply PEperm_R_vs_elt_inv.
assumption.
Defined.

Instance PEperm_R_in {A} b (a : A) : Proper (PEperm_R b ==> Basics.impl) (In a).
Proof with try eassumption.
destruct b ; simpl ; intros l l' HP HIn.
- eapply Perm_R_in...
- subst...
Qed.

Instance PEperm_R_Forall {A} b (P : A -> Prop) :
  Proper (PEperm_R b ==> Basics.impl) (Forall P).
Proof with try eassumption.
destruct b ; simpl ; intros l1 l2 HP HF.
- eapply Perm_R_Forall...
- subst...
Qed.

Instance PEperm_R_Exists {A} b (P : A -> Prop) :
  Proper (PEperm_R b ==> Basics.impl) (Exists P).
Proof with try eassumption.
destruct b ; simpl ; intros l1 l2 HP HF.
- eapply Perm_R_Exists...
- subst...
Qed.

Lemma PEperm_R_Forall2 {A B} b (P : A -> B -> Prop) :
  forall l1 l1' l2, PEperm_R b l1 l1' -> Forall2_Type P l1 l2 -> 
    { l2' : _ & PEperm_R b l2 l2' & Forall2_Type P l1' l2' }.
Proof.
destruct b ; [ apply Perm_R_Forall2 | ].
intros l1 l1' l2 HE HF ; simpl in HE ; subst.
exists l2 ; [ reflexivity | assumption ].
Defined.

Instance PEperm_R_map {A B} (f : A -> B) b :
  Proper (PEperm_R b ==> PEperm_R b) (map f).
Proof.
destruct b ; intros l l' HP.
- apply Perm_R_map.
  assumption.
- simpl in HP ; subst.
  reflexivity.
Defined.

Instance PEperm_R_Forall_R {A} b (P : A -> Type) :
  Proper (PEperm_R b ==> Basics.arrow) (Forall_Type P).
Proof with try eassumption.
destruct b ; simpl ; intros l1 l2 HP HF.
- eapply Perm_R_Forall_Type...
- subst...
Qed.

Instance PEperm_R_Exists_R {A} b (P : A -> Type) :
  Proper (PEperm_R b ==> Basics.arrow) (Exists_Type P).
Proof with try eassumption.
destruct b ; simpl ; intros l1 l2 HP HF.
- eapply Perm_R_Exists_Type...
- subst...
Qed.

Lemma PEperm_R_map_inv {A B} b : forall (f : A -> B) l1 l2,
  PEperm_R b l1 (map f l2) ->
  { l : _ & l1 = map f l & (PEperm_R b l2 l) }.
Proof.
destruct b ; simpl ; intros f l1 l2 HP.
- eapply Perm_R_map_inv ; eassumption.
- subst.
  exists l2 ; reflexivity.
Defined.

Instance PEperm_R_rev {A} b : Proper (PEperm_R b ==> PEperm_R b) (@rev A).
Proof.
destruct b ; intros l1 l2 HP.
- now apply Perm_R_rev'.
- now (simpl in HP ; subst).
Defined.

Lemma PEperm_R_map_inv_inj {A B} b : forall f : A -> B, injective f ->
  forall l1 l2, PEperm_R b (map f l1) (map f l2) -> PEperm_R b l1 l2.
Proof with try assumption.
destruct b ; intros f Hi l1 l2 HP.
- apply Perm_R_map_inv_inj in HP...
- apply map_inj in HP...
Defined.

Lemma PEperm_R_image {A B} b : forall (f : A -> B) a l l',
  PEperm_R b (a :: l) (map f l') -> { a' | a = f a' }.
Proof.
destruct b ; intros f a l l' H.
- eapply Perm_R_image ; eassumption.
- destruct l' ; inversion H ; subst.
  exists a0 ; reflexivity.
Qed.


(** ** From PEperm to PCperm *)

Instance PEperm_PCperm_R {A} b : Proper (PEperm_R b ==> PCperm_R b) (@id (list A)).
Proof.
destruct b ; simpl ; intros l l' HP.
- assumption.
- subst ; apply CyclicPerm_R_refl.
Defined.

Instance PEperm_PCperm_R_cons {A} b :
  Proper (eq ==> PEperm_R b ==> PCperm_R b) (@cons A).
Proof.
intros x y Heq l1 l2 HP ; subst.
apply PEperm_PCperm_R.
now apply PEperm_R_cons.
Defined.

Instance PEperm_PCperm_R_app {A} b :
  Proper (PEperm_R b ==> PEperm_R b ==> PCperm_R b) (@app A).
Proof.
intros l1 l1' HPhd l2 l2' HPtl.
apply PEperm_PCperm_R.
rewrite HPhd.
rewrite HPtl.
reflexivity.
Defined.