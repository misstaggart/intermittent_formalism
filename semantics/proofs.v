Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From TLC Require Import LibTactics.
Import ListNotations.
From Semantics Require Import programs semantics algorithms. (*shouldn't have to import both of these*)

Open Scope list_scope.
(*Lemma consRight: forall(A: Type) (L1 L2: list A) (a: A), incl L1 L2 -> incl L*)

Lemma onePointone: forall(N N' W W' R R': warvars) (l: instruction),
    DINO_ins N W R l N' W' R' -> incl N N'.
Proof. intros. induction H; try((try apply incl_tl); apply (incl_refl N)).
Qed.


Lemma onePointtwo: forall(N N' W R: warvars) (c c': command),
    DINO N W R c c' N' -> incl N N'.
Proof. intros. induction H; try(apply onePointone in H); try apply (incl_refl N); try assumption.
       -  apply (incl_tran H IHDINO).
       - apply (incl_appl N2 IHDINO1). (*why is coq too stupid to figure out these instantiations*)
 Qed.

Lemma Two: forall(N N' W W' R R' N1: warvars) (l: instruction),
    DINO_ins N W R l N' W' R' -> incl N' N1 -> WAR_ins N1 W R l W' R'.
  intros. induction H; try (constructor; assumption || (apply War_noRd; assumption));
            (apply WAR_Checkpointed || apply WAR_Checkpointed_Arr);
            (repeat assumption); apply H0; unfold In; left; reflexivity.
Qed.

Lemma incl_app_l: forall(A: Type) (L1 L2 L3: list A),
    incl (L1 ++ L2) L3 -> incl L1 L3.
Proof. intros. apply (incl_tran
                        (incl_appl L2 (incl_refl L1))
                        H).
Qed.

Lemma incl_app_r: forall(A: Type) (L1 L2 L3: list A),
    incl (L1 ++ L2) L3 -> incl L2 L3.
Proof. intros. apply (incl_tran
                        (incl_appr L1 (incl_refl L2))
                        H).
Qed.

Theorem DINO_WAR_correct: forall(N W R N': warvars) (c c': command),
    DINO N W R c c' N' -> (forall(N1: warvars), incl N' N1 -> WARok N1 W R c').
  intros N W R c c' N' H. induction H; intros N0 Hincl.
  - eapply WAR_I. applys Two H Hincl.
  - eapply WAR_Seq. applys Two H. apply onePointtwo in H0. eauto using incl_tran.
    apply (IHDINO N0 Hincl).
  - eapply WAR_If; (try eassumption);
      ((apply IHDINO1; apply incl_app_l in Hincl)
       || (apply IHDINO2; apply incl_app_r in Hincl)); assumption.
  - intros. apply WAR_CP. apply IHDINO. apply (incl_refl N').
Qed.
Check sub_disclude.
Lemma eight: forall(N0 N1 N2: nvmem) (V0: vmem) (c0: command),
              (subset_nvm N0 N1) ->
              (subset_nvm N0 N2) ->
              current_init_pt N0 V0 c0 N1 N2 ->
              same_pt N1 V0 c0 c0 N1 N2.
Proof. intros. inversion H1. subst.
       apply (same_mem (CTrace_Empty (N1, V0, c0))
                       T); (try assumption).
       - simpl. intros contra. contradiction.
       - intros. simpl. split.
         + assert (H6: not (In (loc_warvar l) (getdomain N0))) by
               apply (sub_disclude N0 N1 N2 l H H0 H5).
           apply H4 in H5. apply H6 in H5.
           Admitted.
(*ah i need that sweet nonconstructive logic*)
Close Scope list_scope.
