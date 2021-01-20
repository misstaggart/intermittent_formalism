Set Warnings "-notation-overridden,-parsing".

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq fintype ssrnat ssrfun.
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Strings.String Program Logic.FunctionalExtensionality.
Require Export Coq.Strings.String.
From TLC Require Import LibTactics.
From Semantics Require Import semantics algorithms lemmas_0.


(*invariants*)

(*no interpretation for thing error means scopiing problem sometimes*)
Lemma agsv_war_h : forall(w1 w2: warvars) (x: smallvar),
            get_smallvars w2 = get_smallvars w1 ->
            inl x \notin w1 -> inl x \notin w2.
          intros. apply/ negP. intros contra. suffices: (inl x) \in (get_smallvars w2).
          intros contra1. rewrite H in contra1.
          rewrite mem_filter in contra1. move/ negP: H0.
          apply. by move/ andP : contra1 => [one two].
          rewrite mem_filter. by []. Qed. 

Lemma sv_add_sv: forall(w1 w2 :warvars) (x: smallvar),
            (get_smallvars w1) = (get_smallvars w2) ->
            (get_smallvars ((inl x) :: w1) = get_smallvars ((inl x) :: w2)).
          intros.
          rewrite - cat1s.
          rewrite - (cat1s (inl x) w2).
          unfold get_smallvars. 
          repeat rewrite filter_cat.
          unfold get_smallvars in H. rewrite H.
          by [].
Qed.


Lemma sv_add_el:forall(w1 w2 :warvars) (el: el_loc),
            (get_smallvars w1) = (get_smallvars w2) ->
            (get_smallvars ((inr el) :: w1) =
             get_smallvars w2).
          intros. rewrite - cat1s. unfold get_smallvars. rewrite filter_cat.
          unfold get_smallvars in H. by apply H. Qed.

Lemma sv_add_arr: forall(w1 w2 :warvars) (a: array),
            (get_smallvars w1) = (get_smallvars w2) ->
            (get_smallvars ((generate_locs a) ++ w1) =
             (get_smallvars w2)).
          intros. suffices: (get_smallvars (generate_locs a) = [::]).
          intros Hnil. unfold get_smallvars.
          unfold get_smallvars in Hnil.
          unfold get_smallvars in H.
          rewrite filter_cat Hnil H. by [].
          unfold get_smallvars. unfold generate_locs.
          rewrite filter_map.
          suffices: (preim
                       (index_loc a)
                       (fun v : smallvar + el_loc =>
          match v with
          | inl _ => true
          | inr _ => false
          end)
                    ) =1 pred0. intros contra.
          rewrite (eq_filter contra). rewrite filter_pred0. by [].
          intros l.
          by []. Qed. 


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

  Lemma append_write_empty: forall{W: the_write_stuff},
    append_write W emptysets = W.
Proof. intros. simpl. unfold append_write. simpl.
       repeat rewrite cats0.
       apply undo_gets.
Qed.


Lemma append_write_empty_l: forall{W: the_write_stuff},
    append_write emptysets W = W.
Proof. intros. simpl. unfold append_write. simpl.
       unfold remove. simpl.
       rewrite filter_predT. repeat rewrite cats0. 
       apply undo_gets.
Qed.

Lemma prefix_app {O1 O2 O3: obseq} :
  (O2 <=p O3) -> reboot \notin O1 -> checkpoint \notin O1 ->
  O1 ++ O2 <=p O1 ++ O3.
  intros. induction H.
  2:{
rewrite catA. apply P_Ind; try assumption.
  }
  apply P_Base; try (rewrite mem_cat; apply/norP; split; by []).
Qed.

Lemma cinds: forall (c: command) (l: instruction),
    c <> (l ;; c).
  move => c w contra.
  induction c; inversion contra.
    by apply IHc. Qed.

Lemma cindi1 {c1 c2 e}: 
    c1 <> TEST e THEN c1 ELSE c2.
  move => contra.
  induction c1; inversion contra.
    subst. by apply IHc1_1. Qed.

Lemma cindi2 {c1 c2 e}:
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

Lemma append_writeA {W1 W2 W3}:
  append_write (append_write W1 W2) W3 =
  append_write W1 (append_write W2 W3).
destruct W1 as [ [w1 r1] fw1].
destruct W2 as [ [w2 r2] fw2].
destruct W3 as [ [w3 r3] fw3].
unfold append_write. simpl.
assert (remove (r2 ++ r1) fw3 ++ remove r1 fw2 ++ fw1 =
        remove r1 (remove r2 fw3 ++ fw2) ++ fw1) as Heq1.
unfold remove. rewrite remove_to_app.
rewrite filter_cat.
by rewrite catA.
rewrite Heq1.
by repeat rewrite catA.
Qed.

Lemma notin (o: obs) : o \notin [::].
by rewrite in_nil. Qed.
