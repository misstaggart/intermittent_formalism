Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From TLC Require Import LibTactics.
Import ListNotations.
From Semantics Require Import programs semantics algorithms. (*shouldn't have to import both of these*)
Open Scope list_scope.

(*list facts*)
(*these are pretty fat proofs but my time is better spent
 on the real lemmas in proofs.v*)

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


Lemma filter_false: forall{A: Type} (L1: list A),
    filter (fun x => negb false) L1 = L1.
  induction L1.
  - reflexivity.
  - simpl. rewrite IHL1. reflexivity.
Qed.

Lemma in_app_l: forall{A: Type} {a: A} {L1 L2: list A},
    In a L1 -> In a (L1 ++ L2).
  Proof. intros. eapply or_introl in H.
         apply in_or_app in H. apply H.
  Qed.

Lemma in_app_r: forall{A: Type} {a: A} {L1 L2: list A},
    In a L2 -> In a (L1 ++ L2).
  Proof. intros. eapply or_intror in H.
         apply in_or_app in H. apply H.
  Qed.


  Lemma empty_sub: forall{A: Type} {L: list A},
      incl [] L.
   Proof. intros. unfold incl. intros. apply in_nil in H. contradiction. Qed.
Close Scope list_scope.
