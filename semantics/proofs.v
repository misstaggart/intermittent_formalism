Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From TLC Require Import LibTactics.
Import ListNotations.
From Semantics Require Export algorithms.

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
  (* try (eapply WAR_I || eapply WAR_Seq);
      eapply (Two _ _ _ _ _ _ _ _ H Hincl).
  - intros N0 Hincl. try (eapply WAR_I || eapply WAR_Seq).
      eapply (Two _ _ _ _ _ _ _ _ H Hincl).
  - try (intros; (eapply WAR_I || eapply WAR_Seq); eapply Two in H; apply H); try (repeat assumption).
- intros.
  - intros. eapply WAR_Seq. eapply Two in H. apply H.
    apply onePointtwo in H0. apply (incl_tran H0 H1).*)
    apply (IHDINO N0 Hincl).
  - eapply WAR_If; (try eassumption);
      ((apply IHDINO1; apply incl_app_l in Hincl)
       || (apply IHDINO2; apply incl_app_r in Hincl)); assumption.
  - intros. apply WAR_CP. apply IHDINO. apply (incl_refl N').
  Qed.
  (*make ltac for first two bullets*)
Close Scope list_scope.
