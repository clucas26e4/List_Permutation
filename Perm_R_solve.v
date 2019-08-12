(* Permutation_solve library *)

(* output in Types *)

(** * Some tactics for tentative automatic solving of [Permutation] goals
The main tactic is [perm_solve] which fails is the goal is not solved. *)

Require Import List_more.
Require Import Perm_R_more.


Ltac pre_simpl_hyp_Perm_R H :=
  try apply Perm_R_cons_inv in H ;
  try apply Perm_R_app_inv in H ;
  try apply Perm_R_app_inv in H ;
  try apply Perm_R_app_middle_inv in H ;
  try apply Perm_R_cons_app_inv in H ;
  try (rewrite app_assoc in H ;
       apply Perm_R_cons_app_inv in H) ;
  try (rewrite app_comm_cons in H ;
       apply Perm_R_cons_app_inv in H) ;
  try (rewrite app_comm_cons in H ;
       rewrite app_assoc in H ;
       apply Perm_R_cons_app_inv in H).
Ltac simpl_hyp_Perm_R H :=
  list_simpl in H ;
  try pre_simpl_hyp_Perm_R H ;
  try (apply Perm_R_sym in H ;
       pre_simpl_hyp_Perm_R H ;
       apply Perm_R_sym in H).
Ltac simpl_hyp_perm_all_Type :=
  repeat (
    match goal with
    | H:Perm_R _ _ |- _ => simpl_hyp_Perm_R H
    end).

Ltac Perm_R_rot :=
  cons2app ;
  rewrite <- ? app_assoc ;
  eapply Perm_R_trans ;
    [ apply Perm_R_app_rot
    | instantiate ].

(** The parameter [20] below is an arbitrary
 the higher, the longer, the more powerful *)
Ltac Perm_R_solve :=
  match goal with
  | |- Perm_R _ _ =>
    list_simpl ;
    try simpl_hyp_perm_all_Type ;
    cons2app_all ;
    try simpl_hyp_perm_all_Type ;
    first [
      try apply Perm_R_app_tail ;
      try apply Perm_R_app_middle ;
      try Perm_R_run ;
      apply Perm_R_sym ;
      Perm_R_run ; fail 
    | match goal with
      | H:Perm_R _ _ |- Perm_R _ _ =>
            try (apply (Perm_R_trans H) ; Perm_R_run ; fail) ;
            try (apply Perm_R_sym ;
                 apply (Perm_R_trans H) ; Perm_R_run ; fail) ;
            try (apply Perm_R_sym in H ;
                 apply (Perm_R_trans H) ; Perm_R_run ; fail) ;
            try (apply Perm_R_sym ; apply Perm_R_sym in H ;
                 apply (Perm_R_trans H) ; Perm_R_run ; fail) ; fail
    end ]
  end
with Perm_R_run :=
  do 20 (
  cons2app ;
  rewrite <- ? app_assoc ;
  try apply Perm_R_app_head ;
  match goal with
  | |- Perm_R _ _ => apply Perm_R_refl
  | |- Perm_R (_ ++ _) _ => apply Perm_R_app_comm
  | H:Perm_R _ _ |- Perm_R _ _ => apply H
  | H:Perm_R ?l1 _ |- Perm_R (?l1 ++ _) _
       => eapply Perm_R_trans ; 
          [ apply Perm_R_app_tail ; apply H
          | instantiate ]
  | H:Perm_R _ ?l1 |- Perm_R (?l1 ++ _) _
       => apply Perm_R_sym in H ;
          eapply Perm_R_trans ; 
          [ apply Perm_R_app_tail ; apply H
          | instantiate ]
  | |- Perm_R (_ ++ _ ++ _) _ => Perm_R_rot
  | |- Perm_R (_ ++ _ ) _ => eapply Perm_R_trans ;
                                  [ apply Perm_R_app_comm
                                  | instantiate ]
  | H:Perm_R ?l1 _ |- Perm_R ?l1 _
       => eapply Perm_R_trans ; 
          [ apply H
          | instantiate ]
  | H:Perm_R _ ?l1 |- Perm_R ?l1 _
       => apply Perm_R_sym in H ;
          eapply Perm_R_trans ; 
          [ apply H
          | instantiate ]
  | _ => idtac
  end ).


