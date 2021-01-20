Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Strings.String Program Logic.FunctionalExtensionality.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq fintype ssrnat ssrfun.
From TLC Require Import LibTactics LibLogic.
From Coq_intermittent Require Export programs semantics algorithms lemmas_1
     lemmas_0 proofs_0 proofs_w. 
Implicit Types N: nvmem. Implicit Types V: vmem.
Implicit Types O: obseq.
Implicit Types c: command.
Implicit Types W: the_write_stuff.
Implicit Types x: smallvar.

(*The exciting proofs are at the bottom. More important lemmas are briefly commented.*)

(*Invariants*)

(*My memory invariant. I like it because it is minimalistic, yet sufficient (along with its weaker version, which differs only in the ommision of the requirement that end_com c2) to prove the final correctness result. Further, it is preserved after arbitrary reboot, provided that the DINO checkpointing scheme is followed, which facillitates reasoning about intermittent execution.
 Also, it is an equivalence relation, as proved below.*)
Inductive all_diff_in_fw: nvmem -> vmem -> command -> nvmem -> Prop :=
  Diff_in_FW: forall{N1 V1 c1 N2 V2 c2 N1c O W} (T: trace_cs (N1, V1, c1) (N2, V2, c2) O W),
    end_com c2 -> checkpoint \notin O -> 
( forall(l: loc ), ((getmap N1) l <> (getmap N1c) l) -> (l \in getfstwt W))
-> all_diff_in_fw N1 V1 c1 N1c.

(*Definition 5 in Technical Appendix*)
Inductive current_init_pt: nvmem -> vmem -> command -> nvmem -> nvmem -> nvmem -> Prop:=
  valid_mem: forall {N Ni0 N1 Nc0 Nend: nvmem}
                  {V V1 Vend: vmem}
                  {c crem: command}
                  {W : the_write_stuff}
                  {O: obseq}
                  {w: warvars}
                  (T: trace_cs (Ni0, V, c) (Nend, Vend, crem) O W),
    crem = skip \/ (exists(w: warvars) (crem2: command), crem = ((incheckpoint w);;crem2)) ->
    subseq (getdomain Nc0) (getdomain N1)
    -> subset_nvm N Nc0
                  -> (checkpoint \notin O) 
                 -> (forall(l: loc),
                      not((getmap N1) l = (getmap Nc0) l)
                      -> (l \in (getfstwt W)) \/ (l \in (getdomain N)))
                 -> current_init_pt N V c Ni0 N1 Nc0.

(*Definition 4 in Technical Appendix*)
Inductive same_pt: nvmem -> vmem -> command -> command -> nvmem -> nvmem -> Prop :=
same_mem: forall {N0 N1 Ncomp N2: nvmem}
                  {V0 V1 V2: vmem}
                  {c0 c1 crem: command}
                  {W1 W2: the_write_stuff}
                  {O1 O2: obseq}
                  (T1: trace_cs (N0, V0, c0) (N1, V1, c1) O1 W1)
                  (T2: trace_cs (N1, V1, c1) (N2, V2, crem) O2 W2),
    crem = skip \/ (exists(w: warvars) (crem2: command), crem = ((incheckpoint w);;crem2)) ->
                  subseq (getdomain Ncomp) (getdomain Ncomp) 
                  -> (checkpoint \notin O1)
                  -> (checkpoint \notin O2) 
                 -> (forall(l: loc),
                      not((getmap N1) l = (getmap Ncomp) l)
                      -> ((l \in (getwt W2)) /\ (l \in (getfstwt (append_write W1 W2))) /\ not (l \in (getwt W1))))
                  -> same_pt N0 V0 c0 c1 N1 Ncomp.

(*Definition 6 in Technical Appendix*)
Inductive same_config: nvmem -> iconf -> context -> Prop :=
  SameConfig: forall(Nstart N0 N1 N2: nvmem)
                (V0 V: vmem)
                (c0 c: command),
    subset_nvm N0 Nstart ->
    same_pt Nstart V0 c0 c N1 N2 ->
    same_config Nstart ((N0, V0, c0), N1, V, c) (N2, V, c).

(*helper lemmas about all_diff_in_fw*)

  Lemma adifw_adif {N V c N1}:
    all_diff_in_fw N V c N1 ->
    all_diff_in_fww N V c N1.
    intros Hdiff. inversion Hdiff. subst.
    econstructor; try apply T; try assumption. Qed.


 Lemma agreeonread: forall{N Nend N2: nvmem} {V Vend: vmem}
                        {c c1: command}
                   {O : obseq} {W: the_write_stuff},
  all_diff_in_fw N V c N2 ->
             cceval_w (N, V, c) O (Nend, Vend, c1) W ->
             ( forall(z: loc), z \in (getrd W) -> (getmap N) z = (getmap N2) z).
   intros. apply adifw_adif in H. eapply agreeonread_w_l; try apply H; try apply H0; try assumption. Qed.

 Lemma add_skip_ins {N1 V l N2}: all_diff_in_fw N1 V (Ins l) N2 ->
                                 all_diff_in_fw N1 V (l;; skip) N2.
   intros Hdiff. inversion Hdiff; subst.
   inversion T; subst.
   - destruct H as [one | two]. inversion one. subst.
     econstructor.
     eapply CsTrace_Single. eapply Skip. by left. by []. assumption. destruct two as [crem [w contra] ]. discriminate contra.
     move: (cceval_skip H2) => one. subst.
     econstructor. eapply CsTrace_Single.
     eapply Seq. intros w contra. subst. inversion H2.
     intros contra. subst. inversion H2. apply H2. by left.
     assumption. assumption.
     destruct Cmid as [ [nm vm] cm].
     move: (cceval_skip H4) => eq. subst.
     econstructor. eapply CsTrace_Single.
     eapply Seq. intros w contra. subst. inversion H4.
     intros contra. subst. inversion H4.
     apply H4. by left.
     rewrite mem_cat in H0. move/ norP: H0 => [Ho1 Ho2].
     assumption.
     suffices: W2 = emptysets. move => eq. subst.
     rewrite append_write_empty in H1.
     assumption.
     move: (trace_skip H2) => Heq. subst. by move/empty_trace_cs1: H2 => [one two].
 Qed.

 Lemma adif_cceval {N1 N2 V c Nend Vend O1 W cend}:
  all_diff_in_fw N1 V c N2 ->
  cceval_w (N1, V, c) O1 (Nend, Vend, cend) W ->
  end_com cend ->
    forall(l: loc ), ((getmap N1) l <> (getmap N2) l) -> (l \in getfstwt W).
  intros. move: l H2. inversion H; subst.
  destruct (O == [::]) eqn: Hbool; move/ eqP: Hbool => Hnil. subst.
  apply empty_trace_cs1 in T. destruct T as [one two]. inversion one. subst.
  intros l contra. apply (H4 l) in contra.
  rewrite in_nil in contra. discriminate contra.
  move: (single_step_alls T Hnil H0). => [Wrest [Orest [ Trest [Hsub Hw] ] ] ].
  suffices: checkpoint \notin Orest. move => Hrest.
  move: (same_endcom_help Trest Hrest H1 H2) => one. subst.
  move/ empty_trace_cs: Trest => [one [two [three four] ] ]. subst.
 by rewrite append_write_empty in H4.
 apply/negP. intros contra.
 exfalso.
 rewrite Hsub in H3.
 move/ negP : H3. apply. rewrite mem_cat. apply/orP.
by right.
 Qed.


(*if adif holds at the end of a checkpointed segment, then the related memories
 must be equal*)
Lemma trace_converge {N V cend Nc} :
  all_diff_in_fw N V cend Nc ->
  end_com cend ->
  N = Nc.
  intros Hdiff Hend. apply nvmem_eq.
  inversion Hdiff. subst.
  suffices: O = [::]. move => Heq. subst.
  move/ empty_trace_cs1 : T => [one [two three] ]. subst.
  apply/ eqP /negPn /negP. intros contra.
  move/ eqP : contra => contra.
  apply (H1 three) in contra. rewrite in_nil in contra. discriminate contra.
  move: (same_endcom_help T H0 Hend H) => one. subst.
    by move/ empty_trace_cs : T => [one [two three] ].
    Qed.

Lemma trace_converge_minus1 {N V N' Nmid Vmid Nmid'
                            O W} {l: instruction}:
  all_diff_in_fw N V l N' ->
  cceval_w (N, V, Ins l) O (Nmid, Vmid, Ins skip) W ->
  cceval_w (N', V, Ins l) O (Nmid', Vmid, Ins skip) W ->
  Nmid = Nmid'.
   intros. apply adifw_adif in H.
   eapply trace_converge_minus1w; try apply H; try apply H0; try assumption. Qed.

  Lemma two_bc {Ni Ni1 V V1 l c1 crem Nc O W} : all_diff_in_fw Ni V (l;;crem) Nc ->
                              cceval_w (Ni, V, Ins l) O (Ni1, V1, c1) W ->
                              exists(Nc1: nvmem), (cceval_w (Nc, V, Ins l) O (Nc1, V1, c1) W /\
                                              forall(l: loc), l \in (getwt W) -> ((getmap Ni1) l = (getmap Nc1) l)).
      intros.
      apply adifw_adif in H.
      eapply two_bcw; try apply H; try assumption. Qed.

  (*all_diff_in_fw preserved under single step continuous evaluation*)
Lemma two {Ni Ni1 V V1 c c1 Nc O W} : all_diff_in_fw Ni V c Nc ->
                              cceval_w (Ni, V, c) O (Ni1, V1, c1) W ->
                              exists(Nc1: nvmem), (cceval_w (Nc, V, c) O (Nc1, V1, c1) W /\
                                              (forall(l: loc), l \in (getwt W) -> ((getmap Ni1) l = (getmap Nc1) l))

                                             /\
                                             (checkpoint \notin O -> all_diff_in_fw Ni1 V1 c1 Nc1)
                                             ).
  intros.
  induction c.
  - move: (two_bc (add_skip_ins H) H0). => [Nc1 [Hcceval Hl] ].
    exists Nc1. repeat (split; try assumption).
    move: (cceval_skip Hcceval) => Heq. subst.
    pose proof (trace_converge_minus1 H H0 Hcceval). subst. intros.
    econstructor; try reflexivity.
    apply (CsTrace_Empty (Nc1, V1, Ins skip)). by left.
      by rewrite in_nil.
      move => l0 contra. exfalso. by apply contra.
   - inversion H0; subst.
     +
       assert (end_com (incheckpoint w;; c1)) as Hcp.
       right. by exists c1 w.
       move: (trace_converge H Hcp) => one. subst.
       exists Nc. repeat split. apply CheckPoint; try assumption.
       move/ negP => contra. exfalso. by apply contra.
     + exists Nc. repeat split. apply Skip. move => l contra.
       rewrite in_nil in contra. by exfalso. intros.
       inversion H; subst.
       suffices: O <> [::]. intros Ho.
       move: (single_step_alls T Ho H0). => [Wrest [Orest
                                                     [Trest
                                [Hsubseq Hwrite] ] ] ].
       econstructor; try apply Trest; try assumption.
       apply/negP. intros contra.
       apply/negP / negPn: H3.
 rewrite Hsubseq.
rewrite mem_cat. apply/orP.
by right.
       rewrite append_write_empty_l in Hwrite. by rewrite - Hwrite.
       intros contra. subst.
       move: (empty_trace_cs1 T) => [Eq1 Eq2].
       inversion Eq1. subst. inversion H2.
       inversion H5.
       move : H5 => [crem [w contra] ]. inversion contra.
     + move: (two_bc H H12) => [Nc1 [Hsmall Hdone] ]. exists Nc1. repeat split; try assumption.
       apply Seq; try assumption.
       inversion H; subst.
       suffices: O0 <> [::]. intros Ho.
       move: (single_step_alls T Ho H0). => [Wrest [Orest
                                                     [Trest
                                [Hsubseq Hwrite] ] ] ].
       econstructor; try apply Trest; try assumption.
       apply/negP. intros contra.
       apply/negP / negPn: H2.
 rewrite Hsubseq.
rewrite mem_cat. apply/orP.
by right.
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
             apply H3.
             move: (update_one_contra l0 H12 Hl0) => Heq1.
             move: (update_one_contra l0 Hsmall Hl0) => Heq2.
             by rewrite Heq1 Heq2.
             clear Hneq. intros Hneq. apply/negP. intros contra.
             apply Hneq. by apply Hdone.
       intros contra. subst.
       move: (empty_trace_cs1 T) => [Eq1 Eq2].
       inversion Eq1. subst. inversion H1.
       inversion H4.
       move : H4 => [crem [w contra] ]. inversion contra.
       by apply (H10 w).
     + inversion H0; subst; exists Nc; repeat split. apply If_T.
       move: (agreeonread H H0) => agr.
       apply (agr_imp_age H11); try assumption.
       move => l contra.
       rewrite in_nil in contra. by exfalso.
       intros.
       inversion H. subst. suffices: O <> [::]. intros Ho.
       move: (single_step_alls T Ho H0). => [Wrest [Orest
                                                     [Trest
                                [Hsubseq Hwrite] ] ] ].
       econstructor; try apply Trest; try assumption.
       apply/negP.
       move => contra. rewrite Hsubseq mem_cat in H3.
       move/ norP : H3 => [one two].
       move/negP: two.
         by apply.
         destruct W as [ [w1 w2 ] w3].
         destruct Wrest as [ [wr1 wr2] wr3]. inversion Hwrite.
         rewrite cats0 in H8.
         intros l Hneq. apply H4 in Hneq. subst. simpl in Hneq.
         simpl. rewrite mem_filter in Hneq.
         by move/ andP : Hneq => [one two].
       intros contra. subst. move: (empty_trace_cs1 T) => [Eq1 Eq2].
       inversion Eq1. subst. inversion H2.
       inversion H5.
       move : H5 => [crem [w contra] ]. inversion contra.
       apply If_F.
       move: (agreeonread H H0) => agr.
       apply (agr_imp_age H11); try assumption. move => l contra.
       rewrite in_nil in contra. by exfalso.
       intros.
       inversion H. subst. suffices: O <> [::]. intros Ho.
       move: (single_step_alls T Ho H0). => [Wrest [Orest
                                                     [Trest
                                [Hsubseq Hwrite] ] ] ].
       econstructor; try apply Trest; try assumption.
       apply/negP.
       move => contra. rewrite Hsubseq mem_cat in H3.
       move/ norP : H3 => [one two].
       move/negP: two.
         by apply.
         destruct W as [ [w1 w2 ] w3].
         destruct Wrest as [ [wr1 wr2] wr3]. inversion Hwrite.
         rewrite cats0 in H8.
         intros l Hneq. apply H4 in Hneq. subst. simpl in Hneq.
         simpl. rewrite mem_filter in Hneq.
         by move/ andP : Hneq => [one two].
       intros contra. subst. move: (empty_trace_cs1 T) => [Eq1 Eq2].
       inversion Eq1. subst. inversion H2.
       inversion H5.
       move : H5 => [crem [w contra] ]. inversion contra.
Qed.

Lemma two_p_five {Ni Ni1 V V1 c c1 Nc O W} : all_diff_in_fw Ni V c Nc ->
                                             cceval_w (Ni, V, c) O (Ni1, V1, c1) W ->
                                             checkpoint \notin O ->
                              exists(Nc1: nvmem), (cceval_w (Nc, V, c) O (Nc1, V1, c1) W /\
                              all_diff_in_fw Ni1 V1 c1 Nc1).
  intros.
  move: (two H H0) => [Nc1 [Hcceval [Hl Hdone] ] ]. exists Nc1. split; try assumption. by apply Hdone.
Qed.

(*if two memories are related and there is a continuous trace starting from one and ending
at the end of a checkpointed segment, there is an identical continuous trace starting from the other *)
Lemma adif_works {N1 N2 V c Nend Vend O1 W1 cend}:
  all_diff_in_fw N1 V c N2 ->
  trace_cs (N1, V, c) (Nend, Vend, cend) O1 W1 ->
  end_com cend -> checkpoint \notin O1 ->
  trace_cs (N2, V, c) (Nend, Vend, cend) O1 W1.
  intros. move: N2 H.
  dependent induction H0; intros.
  + move: (trace_converge H H1) => Heq. subst.
    apply (CsTrace_Empty (N2, Vend, cend)).
  + move: (adif_cceval H0 H H1) => Hl.
    move: (two H0 H) => [Nend1 [Hcceval Hl2] ].
    suffices: Nend = Nend1.
    intros. subst. by apply CsTrace_Single.
    apply nvmem_eq.  intros l.
    destruct (l \in getwt(W)) eqn: Hbool.
       - apply Hl2. apply Hbool.
       -
         suffices: getmap N1 l = getmap N2 l.
         intros Heq.
         move: (update_one_c l H) => Himp1.
         apply contra in Himp1.
         move: (update_one_c l Hcceval) => Himp2.
         apply contra in Himp2.
         move /negPn/ eqP: Himp1.
         move /negPn/ eqP: Himp2.
         intros. rewrite - Himp1.
           by rewrite - Himp2.
           by move/ negbT: Hbool.
             by move/ negbT: Hbool.
          apply/ eqP.
          destruct (getmap N1 l == getmap N2 l) eqn: Hbool1.
          auto.
          move/ eqP : Hbool1.
          move/Hl => Hcontra.
          move: (fw_subst_wt_c H) => Hsub.
          apply (in_subseq Hsub) in Hcontra.
            by rewrite Hbool in Hcontra.
         + destruct Cmid as [ [Ni1 V1] c1].
           assert (checkpoint \notin O1) as Hcp1.
           apply/negP. intros contra.
           apply/negP/ negPn: H3.
           by apply in_app_l.
           move: (two_p_five H4 H1 Hcp1) => [Nmid [Hccevalmid Hdiff] ].
           eapply CsTrace_Cons.
           eapply IHtrace_cs; try reflexivity; 
             try assumption; try apply Hdiff.
           apply/negP. intros contra.
           apply/negP/ negPn: H3.
           by apply in_app_r. assumption. assumption.
Qed.

(*ramping up to the final proof*)
Lemma adif_refl {N V c c1 Nend Vend O W}:
  trace_cs (N, V, c) (Nend, Vend, c1) O W ->
  end_com c1 ->
  checkpoint \notin O ->
        all_diff_in_fw N V c N.
  intros. econstructor; try apply H; try assumption; try by [].
  Qed.

   Lemma adif_sym {N1 V1 c1 Nc1}:
  all_diff_in_fw N1 V1 c1 Nc1 ->
  all_diff_in_fw Nc1 V1 c1 N1.
  intros Hdiff. inversion Hdiff. subst.
  move: (adif_works Hdiff T H H0) => Tdone.
  econstructor; try apply Tdone; try assumption.
 intros z Hz. 
 apply not_eq_sym in Hz. by apply H1.
Qed.

Lemma adif_trans {Nc0 V1 c1 Nc1 Nc2}:
  all_diff_in_fw Nc0 V1 c1 Nc1 ->
  all_diff_in_fw Nc1 V1 c1 Nc2 ->
  all_diff_in_fw Nc0 V1 c1 Nc2.
  intros Hd1 Hd2. inversion Hd1. inversion Hd2. subst.
  move: (adif_works Hd1 T H H0) => Td1.
  move: (same_endcom Td1 T0 H H6 H0 H7) => Heq. subst.
  move: (determinism Td1 T0) => [one two]. subst.
  econstructor; try apply T; try assumption. 
  intros l Hneq.
  destruct (getmap Nc0 l == getmap Nc1 l) eqn:Hbool; move/ eqP : Hbool => Heq. rewrite Heq in Hneq. by apply H8 in Hneq.
  by apply H1 in Heq.
Qed.


Lemma three_bc1 {Ni Ni1 V V1 c c1 Nc O W} :
  all_diff_in_fw Ni V c Nc ->
  cceval_w ( Ni, V, c) O (Ni1, V1, c1) W ->
    checkpoint \notin O ->
  ( exists(Nc1: nvmem), cceval_w (Nc, V, c) O (Nc1, V1, c1) W /\
                   all_diff_in_fw Ni1 V1 c1 Nc1).
intros. move: (two H H0) => [Nc1 [Hcceval Heq] ]. exists Nc1.
    split. assumption. 
    inversion H. subst. 
    assert (O0 <> [::]) as Ho0.
-
  intros Heq1. subst.
  move/empty_trace_cs1 : T => [ [contra10 [contra11 contra12] ] contra2]. subst. case H2 as [Hskip | [crem [w Hcp] ] ]; subst.
    inversion Hcceval. move/negP : H1. apply.
    apply (observe_checkpt_s Hcceval).
         move: (single_step_alls T Ho0 H0) => [W1 [O1 [T1 [Hsub Hw ] ] ] ].
         econstructor; try apply T1; try assumption.
         apply/ negP => contra.
         move/ negP : H3. apply.
 rewrite Hsub.
rewrite mem_cat. apply/orP.
by right.
         move => l Hl.
         destruct ((getmap Ni l) == (getmap Nc l)) eqn: Hcase;
           move/eqP: Hcase => Hcase.
         move: (update_onec H0 Hcceval Hcase Hl) => Hw1.
         apply Heq in Hw1. exfalso. by apply Hl.
         apply H4 in Hcase. subst. move/fw_split : Hcase => [Hc1 | Hc2].
         move : (in_subseq (fw_subst_wt_c H0) Hc1) => contra.
         apply Heq in contra.
         exfalso. by apply Hl. by destruct Hc2.
Qed.

(*if two memories are related and there is a continuous trace starting from one, there
 is a continuous trace starting from the other with identical observations*)
  Lemma three_bc  {Ni Ni1 V V1 c c1 Nc O W} :
  all_diff_in_fw Ni V c Nc ->
  trace_cs (Ni, V, c) (Ni1, V1, c1) O W ->
  checkpoint \notin O ->
  ( exists(Nc1: nvmem), trace_cs (Nc, V, c) (Nc1, V1, c1) O W /\
                   all_diff_in_fw Ni1 V1 c1 Nc1).
Proof. intros. move: Nc H. dependent induction H0; intros.
    (*empty trace case*)
  - exists Nc; split; auto; constructor.
    (*cceval case*)
  -  move: (three_bc1 H0 H H1) => [Nc1 [Hcceval Hdiff] ].
     exists Nc1. split; try assumption. apply (CsTrace_Single Hcceval).
  - (*inductive cs case*)
    destruct Cmid as [ [Nmid Vmid] cmid]. Check three_bc1.
    rewrite mem_cat in H2. move/norP : H2 => [H21 H22].
    move: (three_bc1 H3 H1 H21) => [Ncmid [Tmid Hmid] ].
    suffices: exists Nc1,
               trace_cs (Ncmid, Vmid, cmid) (Nc1, V1, c1) O2 W2 /\
               all_diff_in_fw Ni1 V1 c1 Nc1.
  - move => [ Nc1 [Tmid2end Hmid2end] ]. exists Nc1. split; try assumption.
    eapply CsTrace_Cons; try apply Tmid2end; try assumption.
    eapply IHtrace_cs; try reflexivity; try assumption.
 Qed.


(*if two memories are related and there is an intermittent trace starting from one which does
not cross a checkpoint boundary, there is a continuous trace starting from the other
with identical observations (only unbroken by reboots).
further, the relation is preserved from starting memories to ending memories,
 and given that the intermittent ending memory can proceed continuously to the end of
 a segment, the continuous ending memory can do the same, with related observations*)
Lemma threeIS1 {N0 Ni Ni1 Nend V V1 Vend c c1 Nc O W Oend Wend cend}:
  all_diff_in_fw Ni V c Nc -> 
  trace_i1 ((N0, V, c), Ni, V, c) ((N0, V, c), Ni1, V1, c1) O W ->
  WARok (getdomain N0) [::] [::] c ->
  subset_nvm N0 Ni ->
  checkpoint \notin O ->
  trace_cs (Ni1, V1, c1) (Nend, Vend, cend) Oend Wend ->
  end_com cend -> checkpoint \notin Oend ->
  (exists(Oc Oendc: obseq) (Nc1: nvmem) (Wc Wendc: the_write_stuff),
      trace_cs (Nc, V, c) (Nc1, V1, c1) Oc Wc /\
      all_diff_in_fw Ni1 V1 c1 Nc1 /\ (O ++ Oend <=m Oc ++ Oendc)
     /\ trace_cs (Nc1, V1, c1) (Nend, Vend, cend) Oendc Wendc
  ).
Proof. intros. move: Nc H H3.
       dependent induction H0; intros.
  + move: (three_bc H3 H H0) => [ Nc1 [Tdone Hdone] ].
 exists O Oend Nc1 W Wend. repeat split; try assumption.
    apply RB_Base; try (rewrite mem_cat; apply/ norP; split);
    try assumption.
    apply (neg_observe_rb H).
    apply (neg_observe_rb H4).
      apply (adif_works Hdone H4); try assumption.
  + assert (all_diff_in_fw Ni V c (N0 U! Nmid)) as Hdiffrb.
    - inversion H8. subst.  econstructor; try apply T; try assumption.
   move => l. move/eqP/update_diff => [ [diff11 diff12] | [diff21 diff22] ]. case diff11. apply (H4 l diff12).
   move: (update H (not_eq_sym diff21)) => Hdiff.
   move: (wts_cped_sv H H3 H1 diff22 Hdiff)  => [good | bad].
   rewrite/remove filter_predT in good.
   apply (fw_gets_bigger H H1 T H10 good).
   rewrite in_nil in bad. by discriminate bad.
   suffices:
               exists Oc Oendc Nc1 Wc Wendc,
  trace_cs (Nc, V, c) (Nc1, V1, c1) Oc Wc /\
  all_diff_in_fw Ni1 V1 c1 Nc1 /\
  (O2 ++ Oend <=m Oc ++ Oendc) /\
  trace_cs (Nc1, V1, c1) (Nend, Vend, cend) Oendc Wendc.
   intros [Oc [Oendc [Nc1 [Wc [Wendc
                                 [ass1
                                    [ass2
                                       [ass3 ass4] ] ] ] ] ] ] ].
   exists Oc Oendc Nc1 Wc Wendc.
   repeat split; try assumption.
    assert (checkpoint \notin Oc ++ Oendc).
    apply no_CP_in_seq in ass3.
    by move: ass3 => [Ha1 Ha2].
   rewrite- catA.
   rewrite - catA.
   apply RB_Ind; try assumption.
   apply (neg_observe_rb H).
   rewrite mem_cat; apply/ norP; split.
    apply (neg_observe_rb ass1).
    apply (neg_observe_rb ass4).
    rewrite mem_cat.
    apply/ norP.
    split; assumption.
      move: (three_bc H8 H H1) => [Nc3 [threetrace whatever] ].
      move: (append_c ass1 ass4) => bigtrace.
      apply (ctrace_det_obs threetrace H1 bigtrace); try assumption.
   eapply IHtrace_i1; try reflexivity; try assumption.
   apply sub_update. apply (adif_trans (adif_sym Hdiffrb) H8).

  + repeat rewrite mem_cat in H3. move/norP: H3 => [Hb H3].
        move/norP: H3 => [contra Hb1]. by case/negP : contra. 
Qed.



(*the same as threeIS1, only the intermittent trace can cross arbitrary checkpoint boundaries.
 the final result follows pretty quickly from this; one need only apply three with (the continuous trace ending
 at cend) equal to the empty trace*)
Lemma three {N0 N01 V01 c01 Ni Ni1 Nend V V1 Vend c c1 Nc O W Oend Wend cend}:
  all_diff_in_fw Ni V c Nc ->
  trace_i1 ((N0, V, c), Ni, V, c) ((N01, V01, c01), Ni1, V1, c1) O W ->
  WARok (getdomain N0) [::] [::] c ->
  subset_nvm N0 Ni -> 
  trace_cs (Ni1, V1, c1) (Nend, Vend, cend) Oend Wend ->
  end_com cend -> checkpoint \notin Oend ->
  (exists(Oc Oendc: obseq) (Nc1: nvmem) (Wc Wendc: the_write_stuff) ,
      trace_cs (Nc, V, c) (Nc1, V1, c1) Oc Wc /\
      all_diff_in_fw Ni1 V1 c1 Nc1 /\ (O ++ Oend <=f (Oc ++ Oendc)) /\
      trace_cs (Nc1, V1, c1) (Nend, Vend, cend) Oendc Wendc
  ).
Proof.
  intros. move: Nc H H3. dependent induction H0; intros.
  + move: (three_bc H3 H H0) => [ Nc1 [Tdone Hdone] ].
    exists O Oend Nc1 W Wend. repeat split; try assumption.
    apply CP_Base. apply RB_Base; try (rewrite mem_cat; apply/ norP; split);
    try assumption.
    apply (neg_observe_rb H).
    apply (neg_observe_rb H6).
    apply (adif_works Hdone H6); try assumption.
  + 
    move: (iTrace_RB H H0 H1 H2) => bigtrace.
    assert (checkpoint \notin O1 ++ [:: reboot] ++ O2) as Hcp.
    rewrite mem_cat. apply/ norP. split; try assumption.
move: (threeIS1 H7 bigtrace H3 H4 Hcp H8 H5 H6) =>
[Oc
   [Oendc
      [Nc1
         [Wc [
              Wendc
               [ ass1 [
                     ass2
                       [ass3 ass4]
                   ]
               ]
            ]
         ]
      ]
   ]
].
exists Oc Oendc Nc1 Wc Wendc. repeat split; try assumption.
repeat rewrite - catA.
apply CP_Base.
by repeat rewrite - catA in ass3.
  +
        remember ((incheckpoint w);;crem) as ccp.
       assert (end_com ccp) as Hend. unfold end_com. right.
       subst.
         by exists crem w.
        suffices: (exists Oc Oendc Nc1 Wc
                 Wendc Nc1end Vc1end cend,
                 trace_cs (Nc, V, c)
                          (Nc1, Vmid, ccp) Oc Wc /\
                 all_diff_in_fw Nmid Vmid ccp Nc1 /\
                 (O1 <=m Oc) /\
                 trace_cs (Nc1, Vmid, crem)
                   (Nc1end, Vc1end, cend) Oendc
                   Wendc /\ checkpoint \notin Oendc /\ end_com cend
                  ).
    - move => [Oc1 [Oendc1 [Nc1 [Wc1 [Wendc1 [ Nc1end [ Vc1end
            [ ccend [H11 [H12 [Ho1 [H13 [H14 H15] ] ] ] ] ] ] ] ] ] ] ] ]. subst.
      move: (trace_converge H12 Hend) => Heq. subst.
      assert (WARok (getdomain
                       (restrict Nc1 w Hw)) [::] [::] crem) as Hwarok2.
      destruct Nc1 as [mc1 dc1 Hnc1]. rewrite/getdomain. simpl.
      apply (warok_cp H1 H11). 
        remember ((incheckpoint w);;crem) as ccp.
      suffices: (
                 exists Oc2 Oendc2 Nc2 Wc2 Wendc2,
                   trace_cs (Nc1, Vmid, crem)
                            (Nc2, V1, c1) Oc2 Wc2 /\
                   all_diff_in_fw Ni1 V1 c1 Nc2 /\
                   (O2 ++ Oend <=f Oc2 ++ Oendc2) /\
                 trace_cs (Nc2, V1, c1) 
                   (Nend, Vend, cend) Oendc2 Wendc2
                ).
      move => [Oc2 [Oendc2 [Nc2 [Wc2 [Wendc2 [H21 [H22 [Ho2 H23] ] ] ] ] ] ] ].
     - subst. move: (append_cps H11 H21 Hw) => T1.
      exists (Oc1 ++ [::checkpoint] ++ Oc2) Oendc2 Nc2 (append_write Wc1 Wc2) Wendc2.
      repeat split; try assumption.
      repeat rewrite - catA. apply CP_IND; try assumption.
      - eapply IHtrace_i1_2;try reflexivity; try assumption;
        try apply sub_restrict.
        apply (adif_refl H13 H15 H14).
       move: (trace_append_ic H0_0 H3 H5) => Tendi.
              assert ( checkpoint \notin [::]) as Hcp.
              by rewrite in_nil.
       move: (threeIS1 H0 H0_ H1 H2 H
                       (CsTrace_Empty
                          (Nmid, Vmid, ccp )) Hend Hcp).
       => [Oc [Oendc [Nc1 [Wc [ Wendc500 [T1 [Hdiff [Hm Tempty] ] ] ] ] ] ] ].
       subst.
       move: (trace_converge Hdiff) => Hsamemem. subst.
       move/ empty_trace_cs : Tempty => [Heq
                                          blah ].
       subst.
       move: (exist_endcom Tendi H4) => [Oendc0 [Wendc0 [Nc1end0 [Vc1end
                                                           [cend0 [Tend [Hendcom Hoendc] ] ] ] ] ] ].
      apply trace_converge in Hdiff. subst.
      assert (WARok (getdomain
                       (restrict Nc1 w Hw)) [::] [::] crem) as Hwarok2.
      destruct Nc1 as [mc1 dc1 Hnc1]. rewrite/getdomain. simpl.
      subst.
      move: (same_comi H1 H2 H0_ H) => [Nend1 [Oc1 [Wc1 [Tc1 Hoc1] ] ] ].
      apply (warok_cp H1 Tc1).
       subst.
      move: (same_comi Hwarok2 (sub_restrict Nc1 w Hw) Tend Hoendc).
      =>
      [Nc1end [Oendc [Wendc [Tendc Hcpoendc] ] ] ].                                                            
       exists Oc Oendc Nc1 Wc Wendc Nc1end. exists Vc1end cend0. subst.
       repeat split; try assumption. 
       econstructor; try eapply CsTrace_Empty; auto.
       by repeat rewrite cats0 in Hm. assumption.
Qed.

(*proof that definition 1 from 'Towards a Formal Foundation' holds for
 any intermittent trace which satisfies the WARok relation*)
Theorem One {N0 V c N01 V01 c01 N Oi Nendi Vend Wi
           }:
      trace_i1 ((N0, V, c), N, V, c) ((N01, V01, c01), Nendi, Vend, Ins skip) Oi Wi ->
subset_nvm N0 N -> 
WARok (getdomain N0) [::] [::] c ->
(exists (Oc: obseq) (Wc: the_write_stuff) , trace_cs (N, V, c) (Nendi, Vend, Ins skip) Oc Wc /\
                                                     (Oi <=f Oc)).
  intros.
assert (end_com skip) as Hskip. by left.
suffices: 
  (exists(Oc Oendc: obseq) (Nendc: nvmem) (Wc Wendc: the_write_stuff),
      trace_cs (N, V, c) (Nendc, Vend, Ins skip) Oc Wc /\
 all_diff_in_fw Nendi Vend skip Nendc /\ trace_cs (Nendc, Vend, Ins skip)
            (Nendc, Vend, Ins skip) Oendc Wendc
  ).
move => [Oc
          [ Oendc [Nendc
             [Wc
                [Wendc
                   [Tc
                      [Hdiff Tend] ] ] ] ] ] ].
exists Oc Wc. repeat skip; try assumption.
suffices: all_diff_in_fw N V c N.
move => Hdiff.
move: (three Hdiff H H1 H0 (CsTrace_Empty (Nendi, Vend, (Ins skip))) Hskip
      (notin checkpoint)).
=> [Oc [Oendc [Nendc [Wc [ Wendc [T1 [Hdiffend [Hm Tempty] ] ] ] ] ] ] ].
exists Oc Oendc Nendi Wc Wendc.
move: (empty_trace_cs Tempty). => [Ho [Hn [Hv Hw] ] ]. subst.
repeat split; try assumption.
move: (exist_endcom H Hskip) => [Osmall
                                  [Wsmall
                                     [Nmid
                                     [Vmid
                                           [cmid
                                              [Tsmall
                                                 [Hend Hcp ]  ] ] ] ] ] ].
move: (same_comi H1 H0 Tsmall Hcp) => [N2 [Osc [c2 [Tsc Hosc] ] ] ].
econstructor; try apply Tsc; try assumption.
  by intros.
 Qed.



