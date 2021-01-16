Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Strings.String Program Logic.FunctionalExtensionality.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From TLC Require Import LibTactics.
From Semantics Require Import semantics algorithms lemmas_0.

(*semantics*)
Lemma undo_gets: forall(W: the_write_stuff),
      (getwt W, getrd W, getfstwt W) = W.
  Proof. intros. destruct W. destruct p. simpl. reflexivity.
  Qed.



Lemma readobs_app_wvs: forall(r1 r2: readobs),
    readobs_wvs (r1 ++ r2) = (readobs_wvs r1) ++ (readobs_wvs r2).
  intros.
  induction r1.
  + reflexivity.
  + simpl. rewrite IHr1. by rewrite catA.
  Qed.

Lemma stupid: forall (c: command) (l: instruction),
    c <> (l ;; c).
  move => c w contra.
  induction c; inversion contra.
    by apply IHc. Qed.

Lemma stupid1 {c1 c2 e}: 
    c1 <> TEST e THEN c1 ELSE c2.
  move => contra.
  induction c1; inversion contra.
    subst. by apply IHc1_1. Qed.

Lemma stupid2 {c1 c2 e}:
    c1 <> TEST e THEN c2 ELSE c1.
  move => contra.
  induction c1; inversion contra.
    subst. by apply IHc1_1. Qed.
(*lists*)

Lemma subseq_app_l: forall{A: eqType} {L1 L2 L3: seq A},
    subseq (L1 ++ L2) L3 -> subseq L1 L3.
Proof. intros. apply (subseq_trans
                        (prefix_subseq L1 L2)
                        H).
Qed.

Lemma subseq_app_r: forall{A: eqType} {L1 L2 L3: seq A},
    subseq (L1 ++ L2) L3 -> subseq L2 L3.
Proof. intros. apply (subseq_trans
                        (suffix_subseq L1 L2)
                        H).
Qed.



Lemma subseq_add_both: forall{A: eqType} (L1 L2: seq A) (a: A),
    subseq L1 L2 -> subseq (a:: L1) (a :: L2).
Proof. intros.
       apply (cat_subseq (subseq_refl [:: a]) H).
Qed.

Lemma subseq_tl: forall{A: eqType} (L1 L2: seq A) (a: A),
    subseq L1 L2 -> subseq L1 (a:: L2).
Proof. intros. apply (subseq_trans H (subseq_cons L2 a)).
Qed.


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

Lemma remove_app_r: forall {L1 L2 L3: warvars} {l : loc},
    l \notin remove L3 (L1 ++ L2)
    -> l \notin remove L3 L2.
  intros.
  rewrite mem_filter.
  rewrite mem_filter in H.
  apply (introT nandP).
  rewrite mem_cat in H.
  move / nandP : H => [H1 | H2].
  by left.
  move/ norP : H2 => [H21 H22].
    by right.
    Qed.

Lemma remove_to_app: forall (L1 L2 L3: warvars),

    filter (fun x => x \notin L2 ++ L3) L1 = filter (fun x => x \notin L3)
                                                 (filter
                                                 (fun x => x \notin L2)
                                                  L1).

  intros. rewrite - filter_predI.
  under eq_filter => x do rewrite mem_cat negb_or
                                 andb_comm.
                         reflexivity.
Qed.


Lemma remove_empty: forall(L1: warvars),
    remove [::] L1 = L1.
  intros. apply filter_predT. Qed.
(*Lemma remove_subst: forall(L1 L2: warvars),
    subseq (remove L1 L2) L2.
Proof. intros. apply filter_subseq.

Lemma filter_false: forall{A: Type} (L1: seq A),
    filter (fun x => negb false) L1 = L1.
  intros. apply filter_predT.*)

(*just use mem_cat
Lemma in_app_l: forall{A: Type} {a: A} {L1 L2: list A},
    In a L1 -> In a (L1 ++ L2).
  Proof. intros. eapply or_introl in H.
         apply in_or_app in H. apply H.
  Qed.

Lemma in_app_r: forall{A: Type} {a: A} {L1 L2: list A},
    In a L2 -> In a (L1 ++ L2).
  Proof. intros. eapply or_intror in H.
         apply in_or_app in H. apply H.
  Qed.*)

(*use subseq0
 Lemma empty_sub: forall{A: Type} {L: list A},
      incl nil L.
  Proof. intros. unfold incl. intros. apply List.in_nil in H. contradiction. Qed.*)





Lemma notin (o: obs) : o \notin [::].
Admitted.

Lemma append_writeA {W1 W2 W3}:
  append_write (append_write W1 W2) W3 =
  append_write W1 (append_write W2 W3).
destruct W1 as [ [w1 r1] fw1].
destruct W2 as [ [w2 r2] fw2].
destruct W3 as [ [w3 r3] fw3].
unfold append_write. simpl.
assert ((remove (r2 ++ r1) fw3 ++ remove r1 fw2) =
        (remove r1 (remove r2 fw3 ++ fw2))) as Heq1.
Admitted.
(*suffices: (1 = 1).


suffices: (fw3 = fw3). ++ remove r1 fw2 =
        remove r1 (remove r2 fw3 ++ fw2).*)
