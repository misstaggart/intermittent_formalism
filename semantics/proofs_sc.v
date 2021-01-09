Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Strings.String Program Logic.FunctionalExtensionality.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq fintype ssrnat ssrfun.
From TLC Require Import LibTactics LibLogic.
From Semantics Require Export programs semantics algorithms lemmas_1
     lemmas_0 proofs_0. (*shouldn't have to import both of these*)

Inductive all_diff_in_fww: nvmem -> vmem -> command -> nvmem -> Prop :=
  Diff_in_FWw: forall{N1 V1 c1 N2 V2 c2 N1c O W} (T: trace_cs (N1, V1, c1) (N2, V2, c2) O W),
    checkpoint \notin O -> (*c2 is nearest checkpoint or termination*)
  (*  (getdomain N1) = (getdomain N1c) -> alternatively
                                       could check N2 domain as well instead of this
 not even clear why i need the domains                                    
   *)
( forall(l: loc ), ((getmap N1) l <> (getmap N1c) l) -> (l \in getfstwt W))
-> all_diff_in_fww N1 V1 c1 N1c.

 Lemma same_com_hcbc {N N1 Nend1 V V1 l crem O W c1} : all_diff_in_fww N V (l;;crem) N1 ->
                              cceval_w (N1, V, Ins l) O (Nend1, V1, c1) W ->
                              exists(Nend: nvmem), (cceval_w (N, V, Ins l) O (Nend, V1, c1) W).
   intros.
   Admitted.

 Lemma add_skip_ins {N1 V l N2}: all_diff_in_fww N1 V (Ins l) N2 ->
                                 all_diff_in_fww N1 V (l;; skip) N2.
   Admitted.

Lemma trace_converge_minus1w {N V l N' Nmid Vmid Nmid'
                            O W}:
  all_diff_in_fww N V l N' ->
  cceval_w (N, V, l) O (Nmid, Vmid, Ins skip) W ->
  cceval_w (N', V, l) O (Nmid', Vmid, Ins skip) W ->
  Nmid = Nmid'.
Admitted.

(*wellformedness condition about all the mems,
the maps are not error <-> in the domain
 and sorting for the domain*)

Lemma same_com_hc {N N1 V c Nend2 V1 c1 O W}:
  all_diff_in_fww N V c N1 ->
  cceval_w (N1, V, c) O (Nend2, V1, c1) W -> (*use that W2 must be a subset of W*)
  checkpoint \notin O ->
  exists (Nend1: nvmem), cceval_w (N, V, c) O (Nend1, V1, c1) W
                             /\ all_diff_in_fww Nend1 V1 c1 Nend2.
    intros Hdiff Hcceval1 Ho.
   induction c.
  - move: (same_com_hcbc (add_skip_ins Hdiff) Hcceval1). => [Nend Hcceval].
    exists Nend. split; try assumption.
    move: (cceval_skip Hcceval1) => Heq. subst.
    pose proof (trace_converge_minus1w Hdiff Hcceval Hcceval1). subst.
    econstructor; try reflexivity.
    apply (CsTrace_Empty (Nend2, V1, Ins skip)). 
      by rewrite in_nil.
      move => l0 contra. exfalso. by apply contra.


  Lemma same_com_help {N N1 V c Nend2 Vend cend O W}:
  all_diff_in_fww N V c N1 ->
  trace_cs (N1, V, c) (Nend2, Vend, cend) O W ->
  checkpoint \notin O ->
  exists (Nend1: nvmem), trace_cs (N, V, c) (Nend1, Vend, cend) O W
  .
    intros. move: N H.
    dependent induction H0; intros N Hdiff.
    + exists N. apply CsTrace_Empty.
    + move: (same_com_hc Hdiff H H1) => [Nend1 [done blah] ].
      exists Nend1. by apply CsTrace_Single.
    + destruct Cmid as [ [Nmid Vmid] cmid].
      rewrite mem_cat in H2. move/norP : H2 => [Ho1 Ho2].
      move: (same_com_hc Hdiff H1 Ho1) => [Nendm [Tm Hdiffm] ].
      suffices: exists Nend1,
               trace_cs (Nendm, Vmid, cmid)
                        (Nend1, Vend, cend) O2 W2.
      move => [Nend1 Tend].
      exists Nend1. eapply CsTrace_Cons; try apply Tend; try assumption.
      eapply IHtrace_cs; try reflexivity; try assumption.
Qed.
