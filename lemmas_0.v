From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program Logic.PropExtensionality.
Require Export Coq.Strings.String.
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool eqtype seq path.
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

Definition subseq_w {A: eqType} (L1: seq A) (L2: seq A) := forall(l: A), l \in L1 ->
                                                                          l \in L2.
Definition intersect {A: eqType} (O1: seq A) (O2: seq A) :=
  exists(l: A), l \in O1 /\ l \in O2.
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
  case (x != y) eqn: beq; constructor.
  by move/ eqP: beq. intros H.
  move/ negbT /negP : beq. apply.
  move/ eqP: H. by apply. Qed.


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


Lemma subw_undup {A: eqType} {L1 L2: seq A}:
  subseq_w L1 (undup L2) = subseq_w L1 L2.
  apply propositional_extensionality. split; intros Hsub i Hin; apply Hsub in Hin.
    by rewrite - mem_undup.
    by rewrite mem_undup.
Qed.


Lemma intersect_undup {A: eqType}: forall (L1 L2: seq A),
    intersect L1 (undup L2) = intersect L1 L2.
  intros. apply propositional_extensionality. split; move => [i [H1 H2] ]; exists i; split; try by []. by rewrite - mem_undup. by rewrite mem_undup. 
Qed.

Lemma intersect_cons{A: eqType} {L1 L2: seq A} {x: A}:
  intersect L1 (x::L2) -> x \notin L1 ->
  intersect L1 L2. move => [i [H1 H2] ] Hin. rewrite in_cons in H2.
 move/ orP : H2 => [contra | Hdone]. move/ eqP: contra => eq. subst.
rewrite H1 in Hin. discriminate Hin.
  exists i; split; try by []. Qed. 

Lemma subw_sort {A: eqType} {L1 L2: seq A} {R: rel A}:
  subseq_w L1 L2 = subseq_w L1 (sort R L2).
  apply propositional_extensionality. split; intros Hsub i Hin; apply Hsub in Hin.
    by rewrite mem_sort.
    by rewrite mem_sort in Hin.
Qed.

Lemma subw_cons {A: eqType} {L1 L2: seq A} {x: A}:
  subseq_w L1 L2 -> subseq_w L1 (x:: L2).
 move => H i Hi. apply H in Hi. rewrite in_cons. apply/orP. by right. Qed.

Lemma intersect_sort {A: eqType} {R: rel A}: forall {L1 L2: seq A},
    intersect L1 (sort R L2) = intersect L1 L2.
  intros. apply propositional_extensionality. split; move => [i [H1 H2] ]; exists i; split; try by []. by rewrite mem_sort in H2. by rewrite mem_sort. Qed. 

Lemma subw_prefix {A: eqType} {L1 L2 L3: seq A}:
  subseq_w L1 L2 -> subseq_w L1 (L2 ++ L3).
  move => Hsub i Hi. apply Hsub in Hi. rewrite mem_cat. apply/orP. by left. Qed.

Lemma subw_suffix {A: eqType} {L1 L2 L3: seq A}:
  subseq_w L1 L3 -> subseq_w L1 (L2 ++ L3). 
  move => Hsub i Hi. apply Hsub in Hi. rewrite mem_cat. apply/orP. by right. Qed.


Lemma subw_refl {A: eqType} {L1: seq A}:
  subseq_w L1 L1. move => i Hi. by []. Qed.

Lemma intersect_cat {A: eqType} : forall {L1 L2 L3: seq A},
    intersect L1 (L2 ++ L3) = (intersect L1 L2 \/ intersect L1 L3).
  intros.
  apply propositional_extensionality. split.
  move => [i [one two] ]. rewrite mem_cat in two. move/ orP : two => [two1 | two2]; [left | right]; by exists i.
                                                                                 move => [ [i [one two] ] | [i [one two] ] ]; exists i; split; try by [];
try (rewrite mem_cat; apply/ orP). by left. by right. Qed.
