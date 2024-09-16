(** * Some tactics for tentative automatic solving of [CyclicPerm_R] goals
The main tactic is [cperm_solve] which fails is the goal is not solved. *)

From OLlibs Require Import List_more.
Require Import CircularShift_R.


Ltac CircularShift_R_rot :=
  cons2app ;
  rewrite <- ? app_assoc ;
  eapply CircularShift_R_trans ;
    [ apply CircularShift_R_app_rot | ].

(** The parameter [20] below is an arbitrary
 the higher, the longer, the more powerful *)
Ltac CircularShift_R_solve :=
  match goal with
  | |- CircularShift_R _ _ =>
    list_simpl ;
    cons2app in * ;
    first [
      try CircularShift_R_run ;
      apply CircularShift_R_sym ;
      CircularShift_R_run ; fail 
    | match goal with
      | H:CircularShift_R _ _ |- CircularShift_R _ _ =>
           list_simpl in H ;
           try (apply (CircularShift_R_trans H) ; CircularShift_R_run ; fail) ;
           try (apply CircularShift_R_sym ;
                apply (CircularShift_R_trans H) ; CircularShift_R_run ; fail) ;
           try (apply CircularShift_R_sym in H ;
                apply (CircularShift_R_trans H) ; CircularShift_R_run ; fail) ;
           try (apply CircularShift_R_sym ; apply CircularShift_R_sym in H ;
                apply (CircularShift_R_trans H) ; CircularShift_R_run ; fail) ; fail
      end ]
  end
with CircularShift_R_run :=
  do 20 (
  cons2app ;
  rewrite <- ? app_assoc ;
  match goal with
  | |- CircularShift_R _ _ => apply CircularShift_R_refl
  | |- CircularShift_R (_ ++ _) _ => apply CircularShift_R_commu
  | H:CircularShift_R _ _ |- CircularShift_R _ _ => list_simpl in H ; apply H
  | |- CircularShift_R (_ ++ _ ++ _) _ => CircularShift_R_rot
  | |- CircularShift_R (_ ++ _ ) _ => eapply CircularShift_R_trans ;
                                  [ apply CircularShift_R_commu | ]
  | H:CircularShift_R ?l1 _ |- CircularShift_R ?l1 _
       => list_simpl in H ;
          eapply CircularShift_R_trans ; [ apply H | ]
  | H:CircularShift_R _ ?l1 |- CircularShift_R ?l1 _
       => list_simpl in H ;
          apply CircularShift_R_sym in H ;
          eapply CircularShift_R_trans ; [ apply H | ]
  | _ => idtac
  end ).
