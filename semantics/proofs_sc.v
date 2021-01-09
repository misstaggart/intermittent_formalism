Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Strings.String Program Logic.FunctionalExtensionality.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq fintype ssrnat ssrfun.
From TLC Require Import LibTactics LibLogic.
From Semantics Require Export programs semantics algorithms lemmas_1
     lemmas_0 proofs_0. (*shouldn't have to import both of these*)

Lemma hack {N1 N2} : (getmap N1) =1 (getmap N2) -> N1 = N2. Admitted.

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
 and sorting for the domain

 should suffice for
 map =1 map' ->
 N = N' *)

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
  - inversion Hcceval1; subst.
    + exfalso. move/negP : Ho. by apply.
    + exists N. split. apply Skip.
      inversion Hdiff; subst.
      destruct (O == [::]) eqn: Hbool.
       - move/ eqP : Hbool => Hbool. subst.
      apply empty_trace_cs1 in T. move: T =>
                                  [ [one two ] three four].
      subst.
      econstructor; try apply CsTrace_Empty; try assumption.
      auto.
       - move/ negbT / eqP : Hbool => Hneq.
         move: (single_step_alls_rev T Hneq). => [
                                                Cmid [W1
                                                [Wrest1 [O1
                                                     [Hcceval
                                                        [Hsubseq1 Hwrite1] ] ] ] ] ].
         inversion Hcceval; subst.
         move: (single_step_alls T Hneq Hcceval). =>
                                                  [Wrest [Orest [Trest [Hsubseq Hwrite] ] ] ].
         rewrite append_write_empty_l in H0.
         repeat rewrite append_write_empty_l in Hwrite. subst.
         econstructor; try apply Trest; try assumption.
       apply/negP. intros contra.
       apply/negP / negPn: H.
       apply (in_subseq Hsubseq contra).
       exfalso. by apply H9.
         + move: (same_com_hcbc Hdiff H10). => [Nend Hcceval].
           exists Nend. split.
       apply Seq; try assumption.
       inversion Hdiff; subst.
      destruct (O == [::]) eqn: Hbool.
       - move/ eqP : Hbool => Hbool. subst.
      apply empty_trace_cs1 in T. move: T =>
                                  [ [one two ] three four].
      subst.
      suffices: (getmap N2) =1 (getmap N1). move/hack => H500. subst.
      move: (determinism_c H10 Hcceval) => [ [one two] ]. subst.
      econstructor; try apply CsTrace_Empty; try assumption.
      intros l0 contra. exfalso. by apply contra.
      intros l0. apply/ eqP /negPn /negP. intros contra.
      move/ eqPn : contra.
      apply (H0 l0) in contra.
      apply/ negP : contra.
      rewrite - in_nil.
      apply/ negP in contra.
      
       move: (single_step_alls T Ho H0). => [Wrest [Orest
                                                     [Trest
                                [Hsubseq Hwrite] ] ] ].
       econstructor; try apply Trest; try assumption.
       apply/negP. intros contra.
       apply/negP / negPn: H2.
       apply (in_subseq Hsubseq contra).
       intros. destruct ((inr el) \in (getwt W)) eqn: Hbool.
         by apply Hdone in Hbool.
       move : (update_one_contra (inr el) H12) => Ho2ni.
       move : (update_one_contra (inr el) Hsmall) => Ho2nc.
       move/ negbT : Hbool => Hbooli.
       remember Hbooli as Hboolc. clear HeqHboolc.
       apply Ho2ni in Hbooli.
       apply Ho2nc in Hboolc.
       suffices: getmap Ni (inr el) = getmap Nc (inr el).
       intros Heq3. symmetry in Hbooli.
         by move: (trans_eq (trans_eq Hbooli Heq3) Hboolc).
         apply/eqP/ negPn/ negP. move/eqP => contra.
           by apply contra.
           intros l0 Hl0. remember Hl0 as Hneq.
           clear HeqHneq.
           suffices: getmap Ni1 l0 <> getmap Nc1 l0 -> l0 \notin getwt W.
           intros Hdonec. apply Hdonec in Hl0.
           suffices: (l0 \in getfstwt W0).
           intros Hfw.
           subst. move/ fw_split : Hfw => [one | two].
           apply (in_subseq (fw_subst_wt_c H12)) in one.
           exfalso. move/ negP : Hl0. by apply.
             by move: two => [whatever done].
             apply H4.
             move: (update_one_contra l0 H12 Hl0) => Heq1.
             move: (update_one_contra l0 Hsmall Hl0) => Heq2.
             by rewrite Heq1 Heq2.
             clear Hneq. intros Hneq. apply/negP. intros contra.
             apply Hneq. by apply Hdone.
       intros contra.
       move: (empty_trace_cs1 T contra) => [Eq1 Eq2].
       inversion Eq1. subst. inversion H1.
       inversion H5.
       move : H5 => [crem [w contra] ]. inversion contra.
       by apply (H10 w).


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
