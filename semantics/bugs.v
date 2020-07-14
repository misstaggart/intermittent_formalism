Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Arith.Arith Arith.EqNat
     Init.Datatypes Strings.String Program Logic.FunctionalExtensionality.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq fintype
ssrnat.
From TLC Require Import LibTactics LibLogic.
From Semantics Require Export programs semantics algorithms lemmas_1
     lemmas_0.

Definition a := Array "a" 6.

Lemma a5lemma: 5 < 6. auto. Qed.

Lemma a4lemma: 4 < 6. auto. Qed.

Definition a50 := El a (Ordinal a5lemma).

Definition a4 := El a (Ordinal a4lemma).

(*a[5] := 1 ;
 a[4] := a[5] ;
 a[5] := 1*)

Definition c := (asgn_arr a 5 1);; (asgn_arr a 4 (a[[5]]));; (asgn_arr a 5 1).

(*N := []
 W := []
 R := []*)
Lemma bug3: not (WARok [::] [::] [::] c).
  intros contra.
  inversion contra. subst.
  (*applying Seq constructor for first time*)
  inversion H4. subst. simpl in H4.
