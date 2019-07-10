(** * Some tactics for tentative automatic solving of [CyclicPerm_R] goals
The main tactic is [cperm_solve] which fails is the goal is not solved. *)

Require Import List_more.
Require Import CyclicPerm_R.


Ltac CyclicPerm_R_rot :=
  cons2app ;
  rewrite <- ? app_assoc ;
  eapply CyclicPerm_R_trans ;
    [ apply CyclicPerm_R_app_rot
    | instantiate ].

(** The parameter [20] below is an arbitrary
 the higher, the longer, the more powerful *)
Ltac CyclicPerm_R_solve :=
  match goal with
  | |- CyclicPerm_R _ _ =>
    list_simpl ;
    cons2app_all ;
    first [
      try CyclicPerm_R_run ;
      apply CyclicPerm_R_sym ;
      CyclicPerm_R_run ; fail 
    | match goal with
      | H:CyclicPerm_R _ _ |- CyclicPerm_R _ _ =>
           list_simpl in H ;
           try (apply (CyclicPerm_R_trans H) ; CyclicPerm_R_run ; fail) ;
           try (apply CyclicPerm_R_sym ;
                apply (CyclicPerm_R_trans H) ; CyclicPerm_R_run ; fail) ;
           try (apply CyclicPerm_R_sym in H ;
                apply (CyclicPerm_R_trans H) ; CyclicPerm_R_run ; fail) ;
           try (apply CyclicPerm_R_sym ; apply CyclicPerm_R_sym in H ;
                apply (CyclicPerm_R_trans H) ; CyclicPerm_R_run ; fail) ; fail
      end ]
  end
with CyclicPerm_R_run :=
  do 20 (
  cons2app ;
  rewrite <- ? app_assoc ;
  match goal with
  | |- CyclicPerm_R _ _ => apply CyclicPerm_R_refl
  | |- CyclicPerm_R (_ ++ _) _ => apply CyclicPerm_R_commu
  | H:CyclicPerm_R _ _ |- CyclicPerm_R _ _ => list_simpl in H ; apply H
  | |- CyclicPerm_R (_ ++ _ ++ _) _ => CyclicPerm_R_rot
  | |- CyclicPerm_R (_ ++ _ ) _ => eapply CyclicPerm_R_trans ;
                                  [ apply CyclicPerm_R_commu
                                  | instantiate ]
  | H:CyclicPerm_R ?l1 _ |- CyclicPerm_R ?l1 _
       => list_simpl in H ;
          eapply CyclicPerm_R_trans ; 
          [ apply H
          | instantiate ]
  | H:CyclicPerm_R _ ?l1 |- CyclicPerm_R ?l1 _
       => list_simpl in H ;
          apply CyclicPerm_R_sym in H ;
          eapply CyclicPerm_R_trans ; 
          [ apply H
          | instantiate ]
  | _ => idtac
  end ).


