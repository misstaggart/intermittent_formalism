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


(*make ltac for simpl. apply (incl_refl []).
*)

Lemma incl_add_both: forall{A: Type} (L1 L2: list A) (a: A),
    incl L1 L2 -> incl (a:: L1) (a :: L2).
Proof. intros. apply (incl_cons (in_eq a L2)
                     (incl_tl a H)). Qed.

Lemma incl_app_dbl: forall{A: Type} {L11 L12 L21 L22: list A},
    incl L11 L12 -> incl L21 L22 -> incl (L11 ++ L21) (L12 ++ L22).
Proof. intros. unfold incl. intros. apply (in_app_or L11 L21 a) in H1.
       destruct H1; [apply H in H1 | apply H0 in H1]; apply in_or_app; [left | right]; assumption.
Qed.


Lemma remove_subst: forall{A: Type} (in_A: A -> list A -> bool)
                     (L1 L2: list A),
    incl (remove in_A L1 L2) L2.
Proof. intros. induction L2.
       - simpl. apply (incl_refl []).
       - simpl. destruct (negb (in_A a L1)) eqn: beq.
         + apply incl_add_both. assumption.
         + apply incl_tl. assumption.
Qed.

Lemma wt_subst_fstwt: forall{C1 C2: context} {O: obseq} {W: the_write_stuff},
  trace_c C1 C2 O W ->
    incl (getfstwt W) (getwt W).
Proof. intros. induction H.
       + simpl. apply (incl_refl []).
       + induction H0;
           (try (simpl; apply (incl_refl [])));
           (try (unfold getfstwt; unfold getwt;
                 apply remove_subst)).
       - subst. simpl in H. contradiction.
       - simpl. apply (incl_app_dbl IHtrace_c1
                                    (incl_tran
                                    (remove_subst _ _ _)
                                    IHtrace_c2)).
Qed.

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
           apply H4 in H5. destruct H5. 
         + unfold Wt. apply ((wt_subst_fstwt T) l H5).
         + apply H6 in H5. contradiction.
       - split.
         + simpl.
           apply H6 in H5.
           Admitted.
(*ah i need that sweet nonconstructive logic*)
Close Scope list_scope.
