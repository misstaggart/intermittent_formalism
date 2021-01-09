From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program.
Require Export Coq.Strings.String.
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool eqtype.
From TLC Require Import LibTactics.

Ltac destruct4r H L1 L2 L3 L4 := destruct H as [L1 rest];
         destruct rest as [L2 rest];
         destruct rest as [L3 L4].

(*p sure this can actually be handled with case from ssreflect*)
Ltac destruct3 Cmid nmid vmid cmid:=
           destruct Cmid as [Annoying cmid]; destruct Annoying as [nmid vmid].

Ltac ex_destruct3 H := destruct H as [var1 Annoying]; destruct Annoying as [var2 Annoying1];
                       destruct Annoying1 as [var3 H].

Ltac destruct_ms M T WT := destruct M as [WT neverseen]; destruct neverseen as [T].

Ltac generalize_5 N N' V V' O := generalize dependent N;
                               generalize dependent N';
                               generalize dependent V;
                               generalize dependent V';
                               generalize dependent O.
Ltac appldis applier appliee := apply applier in appliee; destruct appliee.

Lemma reflect_conj: forall{b0 b1: bool} {P0 P1: Prop},
                      reflect P0 b0 ->
                      reflect P1 b1 ->
                      reflect (P0 /\ P1) (b0 && b1).
Proof. intros. case (b0 && b1) eqn: beq; constructor.
       + appldis andb_true_iff beq. apply (elimT H) in H1.
         apply (elimT H0) in H2. split; assumption.
       + appldis andb_false_iff beq; case => contra1 contra2.
         applys (elimF H) H1 contra1.
         applys (elimF H0) H1 contra2.
Qed.
