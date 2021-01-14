From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program.
Require Export Coq.Strings.String.
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool eqtype seq.
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

Check eqP.
Lemma eqPn {T: eqType} {x: Equality.sort T}
      {y: Equality.sort T}: reflect (x <> y) (x != y).
  Admitted.


Lemma in_app_r: forall{A: eqType} {a: A} {L1 L2: seq A},
    a \in L2 -> a \in (L1 ++ L2).
  intros. rewrite mem_cat.
  apply (introT orP).
  by right.
  Qed.

Lemma in_app_l: forall{A: eqType} {a: A} {L1 L2: seq A},
    a \in L1 -> a \in (L1 ++ L2).
  intros. rewrite mem_cat.
  apply (introT orP).
  by left.
Qed.

Lemma subseq_app_rr: forall {A: eqType} {L1 L2 L3: seq A},
                          subseq L1 L2 ->
                          subseq L1 (L2 ++ L3).
Proof. intros. apply (subseq_trans H (prefix_subseq L2 L3)).
Qed.


Lemma in_subseq: forall {A: eqType} {L1 L2: seq A} {x: A},
    subseq L1 L2 ->
    x \in L1 ->
    x \in L2.
Proof. intros.
       move / subseqP : H.
       intros. destruct H as [m H H1].
       subst.
         by move / mem_mask : H0.
Qed.


Lemma subseq_undup {A: eqType} {L1 L2: seq A} {x: A}:
  subseq L1 (undup L2) -> subseq L1 (undup (x::L2)).
  intros Hsub.
   destruct (x \in L2) eqn: Hbool. simpl.
  induction L2.
  rewrite in_nil in Hbool. discriminate Hbool.
  rewrite ifT; try assumption.
  simpl. rewrite ifF; try assumption.
  apply (subseq_trans Hsub (suffix_subseq [::x] (undup L2))).
  Qed.

Definition intersect {A: eqType} (O1: seq A) (O2: seq A) :=
  exists(l: A), l \in O1 /\ l \in O2.
