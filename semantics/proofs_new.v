Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Strings.String Program Logic.FunctionalExtensionality.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq fintype ssrnat ssrfun.
From TLC Require Import LibTactics LibLogic.
From Semantics Require Export programs semantics algorithms lemmas_1
     lemmas_0 proofs_0 proofs_w. 
Implicit Types N: nvmem. Implicit Types V: vmem.
Implicit Types O: obseq.
Implicit Types c: command.
Implicit Types W: the_write_stuff.
Implicit Types x: smallvar.

Definition end_com c := c = Ins skip \/ exists(crem: command)(w: warvars), c= (incheckpoint w);; crem.


Lemma same_endcom_help {N V c N1 V1 c1 O1 W1}:
  trace_cs (N, V, c) (N1, V1, c1) O1 W1 ->
  checkpoint \notin O1 ->
  end_com c -> end_com c1 -> c1 = c.
  intros. destruct H1. subst.
  move: (trace_skip H) => Heq. subst.
  move/empty_trace_cs1 :H => [one two]. by inversion one.
  destruct H1 as [crem [w Hrem] ]. subst.
  inversion H; subst; try by [].
  apply observe_checkpt_s in H1. exfalso. move/negP : H0.
    by apply.
    destruct Cmid as [ [nm vm] cm].
    apply observe_checkpt_s in H4. exfalso.
    rewrite mem_cat in H0. move/norP: H0 => [one two].
    move/negP : one. 
  by apply. Qed.


  Lemma same_endcom_bc {N V c N1 V1 c1 O1 O2 W1 N2 V2 c2 W2}:
cceval_w (N, V, c) O1 (N1, V1, c1) W1 ->
trace_cs (N, V, c) (N2, V2, c2) O2 W2 ->
end_com c1 ->
end_com c2 ->
checkpoint \notin O1 ->
checkpoint \notin O2 ->
c1 = c2.
    move => Hcc T Hc1 Hc2 Ho1 Ho2.
move: V1 N1 O1 W1 c1 Hcc Hc1 Ho1. dependent induction T; intros.
apply (same_endcom_help (CsTrace_Single Hcc) Ho1 Hc2 Hc1).
move: (determinism_c H Hcc) => [one [two three] ]. inversion one. by subst.
destruct Cmid as [ [nm vm] cm].
move: (determinism_c H0 Hcc) => [one [two three] ].
inversion one. subst. rewrite mem_cat in Ho2. move/norP: Ho2 => [H11 H12].
symmetry. eapply same_endcom_help; try apply T; try assumption.
Qed.


Lemma same_endcom {N V c N1 V1 c1 O1 O2 W1 N2 V2 c2 W2}:
trace_cs (N, V, c) (N1, V1, c1) O1 W1 ->
trace_cs (N, V, c) (N2, V2, c2) O2 W2 ->
end_com c1 ->
end_com c2 ->
checkpoint \notin O1 ->
checkpoint \notin O2 ->
c1 = c2.
  move => T1 T2 Hc1 Hc2 Ho1 Ho2.
  destruct (O2 == [::]) eqn: Hemp;move/ eqP: Hemp => Heq; subst.
move/ empty_trace_cs1 : T2 => [one two]. inversion one. subst.
apply (same_endcom_help T1 Ho1 Hc2 Hc1).
  move: N2 V2 c2 O2 W2 Ho2 Hc2 T2 Heq.
  dependent induction T1; intros.
  symmetry. apply (same_endcom_help T2 Ho2 Hc1 Hc2).
apply (same_endcom_bc H T2 Hc1 Hc2 Ho1 Ho2).
destruct Cmid as [ [nmid vmid] cmid].
inversion T2; subst. exfalso. by apply Heq.
move: (determinism_c H1 H0) => [one [two three] ]. inversion one. subst.
rewrite mem_cat in Ho1. move/ norP: Ho1 => [Ho1 Ho22].
apply (same_endcom_help T1 Ho22 Hc2 Hc1).
destruct Cmid as [ [nmm vmm] cmm].
rewrite mem_cat in Ho2. move/ norP: Ho2 => [Ho21 Ho22].
rewrite mem_cat in Ho1. move/ norP: Ho1 => [Ho11 Ho12].
move: (determinism_c H0 H3) => [one [two three] ]. inversion one. subst. 
eapply IHT1; try reflexivity; try (apply H1); try assumption.
Qed.

  Lemma exist_endcom {N0 V0 c0 N01 V01 c01 N V c N1 V1 O W cend}:
  trace_i1 ((N0, V0, c0), N, V, c) ((N01, V01, c01), N1, V1, cend) O W ->
  end_com cend ->
  (exists(Osmall: obseq) (Wsmall: the_write_stuff) (N2: nvmem) (V2: vmem) (c2: command),
    trace_i1 ((N0, V0, c0), N, V, c) ((N0, V0, c0), N2, V2, c2) Osmall Wsmall /\
    end_com c2 /\ checkpoint \notin Osmall).
    intros T Hend.
    inversion T; subst; try (exists O W N1 V1 cend; repeat split; try assumption).
    exists (O1 ++ [::reboot] ++ O2) (append_write W1 W2) N1 V1 cend.
    repeat split; try assumption.
    rewrite/ eqP mem_cat. rewrite/ norP mem_cat.
    apply/ norP. split; try assumption; apply/ norP.
exists O1 W1 Nmid Vmid (incheckpoint w;; crem). split; try split; try assumption. right. by exists crem w. Qed.

  Inductive all_diff_in_fw: nvmem -> vmem -> command -> nvmem -> Prop :=
  Diff_in_FW: forall{N1 V1 c1 N2 V2 c2 N1c O W} (T: trace_cs (N1, V1, c1) (N2, V2, c2) O W),
    end_com c2 -> checkpoint \notin O -> (*c2 is nearest checkpoint or termination*)
( forall(l: loc ), ((getmap N1) l <> (getmap N1c) l) -> (l \in getfstwt W))
-> all_diff_in_fw N1 V1 c1 N1c.

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
             ( forall(z: loc), z \in (getrd W) ->                    (getmap N) z = (getmap N2) z).
   intros. apply adifw_adif in H. eapply agreeonread_w_l; try apply H; try apply H0; try assumption. Qed.



 Lemma add_skip_ins {N1 V l N2}: all_diff_in_fw N1 V (Ins l) N2 ->
                                 all_diff_in_fw N1 V (l;; skip) N2.
Admitted.

    Lemma two_bcw {Ni Ni1 V V1 l c1 crem Nc O W} : all_diff_in_fww Ni V (l;;crem) Nc ->
                              cceval_w (Ni, V, Ins l) O (Ni1, V1, c1) W ->
                              exists(Nc1: nvmem), (cceval_w (Nc, V, Ins l) O (Nc1, V1, c1) W /\
                              forall(l: loc), l \in (getwt W) -> ((getmap Ni1) l = (getmap Nc1) l)).
      intros.
      move: (agreeonread_ins_w_l H H0) => agr.
      dependent induction H0; simpl in agr.
    (*  - exists Nc. split. apply CheckPoint. move => l contra.
        rewrite in_nil in contra. by exfalso.*)
      - exists (updateNV_sv Nc x v). split. apply NV_Assign; try assumption.
        eapply agr_imp_age; try apply H2; try assumption.
        simpl. intros l Hin. rewrite mem_seq1 in Hin.
        move/ eqP : Hin => Hin. subst.
        destruct Ni as [Nimap NiD].
        destruct Nc as [Ncmap NcD].
        unfold updateNV_sv. unfold updatemap. simpl.
        remember (inl x) as xloc.
        suffices: (if xloc == xloc then v else Nimap xloc) = v /\
                  (if xloc == xloc then v else Ncmap xloc) = v.
        move => [one two].
        destruct (v == error) eqn: Hbool.
        move/ eqP : Hbool => Heq. subst. inversion H1.
          by rewrite one two.
        split; by apply ifT.
     - exists Nc. split. apply V_Assign; try assumption.
       eapply agr_imp_age; try apply H2; try assumption.
       simpl. move => l contra.
        rewrite in_nil in contra. by exfalso.
     - exists (updateNV_arr Nc element a v). split. eapply Assign_Arr.
       eapply agr_imp_age; try apply H3; try assumption.
       intros z Hin.
       suffices: (z \in readobs_wvs (r ++ ri)).
       move => Hin1.
         by apply (agr z).
         rewrite readobs_app_wvs.
         by eapply in_app_r.
       eapply agr_imp_age; try apply H0; try assumption.
       intros z Hin.
       suffices: (z \in readobs_wvs (r ++ ri)).
       move => Hin1.
         by apply (agr z).
         rewrite readobs_app_wvs.
           by eapply in_app_l. assumption. assumption.
           simpl.
           intros l Hin.
        destruct Ni as [Nimap NiD].
        destruct Nc as [Ncmap NcD].
        unfold updateNV_arr. simpl.
        rewrite mem_seq1 in Hin.
        move/ eqP : Hin => Hin. subst.
        (*move: (genloc_contents l a Hin) => [el Heq].
        subst.
        destruct (el == element) eqn: Hbool.
        move/ eqP : Hbool => Heq. subst.*)
        unfold updatemap.
        suffices: 
          ((if inr element == inr element then v else Nimap (inr element)) = v
                                                                              /\
  (if inr element == inr element then v else Ncmap (inr element)) = v).
        move => annoying.
        move: (annoying loc_eqtype loc_eqtype) => [one two].
        destruct (v == error) eqn: Hbool.
        move/ eqP : Hbool => Heq. subst. inversion H1.
          by rewrite one two. 
       intros. split; by apply ifT.
Qed.
    
    -(* exists Nc. split. apply Skip. move => l contra.
      rewrite in_nil in contra. by exfalso.
      suffices: 
               exists Nc1,
               cceval_w (Nc, V, (Ins l)) [:: o] (Nc1, V1, Ins skip) W /\
               (forall l : loc,
                l \in getwt W ->
                getmap Ni1 l = getmap Nc1 l).
      move => [Nc1 [Hsmall Hloc] ]. exists Nc1. split; try assumption.
      apply Seq; try assumption.
      eapply IHcceval_w; try reflexivity; try assumption.*)


    Lemma two_bc {Ni Ni1 V V1 l c1 crem Nc O W} : all_diff_in_fw Ni V (l;;crem) Nc ->
                              cceval_w (Ni, V, Ins l) O (Ni1, V1, c1) W ->
                              exists(Nc1: nvmem), (cceval_w (Nc, V, Ins l) O (Nc1, V1, c1) W /\
                                              forall(l: loc), l \in (getwt W) -> ((getmap Ni1) l = (getmap Nc1) l)).
      intros.
      apply adifw_adif in H.
      eapply two_bcw; try apply H; try assumption. Qed.
(*can't do this one till youve fixed your eq types*)
Lemma trace_converge_minus1 {N V N' Nmid Vmid Nmid'
                            O W} {l: instruction}:
  all_diff_in_fw N V l N' ->
  cceval_w (N, V, Ins l) O (Nmid, Vmid, Ins skip) W ->
  cceval_w (N', V, Ins l) O (Nmid', Vmid, Ins skip) W ->
  Nmid = Nmid'.
   intros. apply adifw_adif in H.
   eapply trace_converge_minus1w; try apply H; try apply H0; try assumption. Qed.

(*use update_one_c*)
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
apply (in_subseq Hsub) in contra. move/ negP : H3. by apply.
Qed.

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
       (*move => l contra.
       rewrite in_nil in contra. by exfalso.*)
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
       apply (in_subseq Hsubseq contra).
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
       apply (in_subseq Hsubseq contra).
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
       move/(in_subseq Hsubseq) => contra. move/negP: H3.
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
       move/(in_subseq Hsubseq) => contra. move/negP: H3.
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

Lemma war_works_loc_c {N0 N Nend: nvmem} {V Vend: vmem} {c cend: command} {O: obseq} {W: the_write_stuff}
      {Wstart Rstart: warvars}:
    cceval_w (N, V, c) O (Nend, Vend, cend) W ->
    WARok (getdomain N0) Wstart Rstart c ->
    checkpoint \notin O ->
    (*O <> [::] -> empty trace annoying and i dont think
               i have to deal w it*)
  forall (l: loc),
(l \notin (remove Rstart (getfstwt W)) -> (*l not in OVERALL FW for this trace*)
    l \in (getwt W) -> (*l written to
                       IN THIS trace*)
          l \in (getdomain N0) \/ l \in Wstart).
  intros Hcceval Hwarok Ho.
  move: Rstart Wstart Hwarok Ho. remember Hcceval as Hcceval1.
  clear HeqHcceval1.
  dependent induction Hcceval1; intros; simpl in H;
    try discriminate H0; try discriminate H1.
  -  remember H3 as Hwt.
    clear HeqHwt.
    simpl in H3. rewrite mem_seq1 in H3.
    move/eqP : H3 => Heq. subst.
   inversion Hwarok; subst; inversion H7;
       subst. (*casing on warIns*)
     (*vol case, x \notin getwt W*)
       +  exfalso. apply (negNVandV x H0 H10).
       + (*nord case*)
         (*showing l in rd W*)
         rewrite mem_cat in H13.
         move / negP / norP : H13 => [Hre Hrs].
         rewrite mem_filter in H2.
         move/nandP: H2. => [contra | H2].
         rewrite Hrs in contra. discriminate contra.
         pose proof (negfwandw_means_r Hcceval H2 Hwt) as Hrd.
         
         simpl in Hrd.
       (*showing x notin RD(W)*)
         move: (read_deterministic H10 (RD H)) => Heq. subst.
         exfalso. move/negP : Hre. by apply.
     + (*CP case*)
        by left.
     + (*written case*)
       by right.
     - (*vol case*)
       rewrite in_nil in H3.
       discriminate H3.
     - (*array case*)
    (*showing x = l*)
       remember H4 as Hwt. clear HeqHwt.
       simpl in H4.
       rewrite mem_seq1 in H4. move/ eqP : H4 => Heq. subst.
       inversion Hwarok; subst; inversion H8;
       subst. (*casing on warIns*)
       + (*nord arr*)
           remember (inr element) as l.
           destruct element as [a0 index].
         (*showing l in rd W*)
         -         (* rewrite mem_cat in H22.
         move / negP / norP : H16 => [H160 H161].*)
           rewrite mem_filter in H3.
           move/nandP : H3 => [contra | H3].
           unfold intersect in H15. exfalso. apply H15.
            exists l.
           split. subst.
           eapply gen_locs_works. apply H2.
           repeat rewrite mem_cat.
           repeat (apply/ orP; right).
           apply /negPn : contra.
           pose proof (negfwandw_means_r Hcceval H3 Hwt) as Hrd. simpl in Hrd.
       (*showing rd sets are same*)
       pose proof
            (read_deterministic (RD H0) H11).
       pose proof
            (read_deterministic (RD H) H14).
       subst.
       exfalso.
       apply H15.
       remember (inr (El a0 index)) as l. exists l.
           split. subst.
           eapply gen_locs_works. apply H2.
       rewrite catA.
       rewrite <- readobs_app_wvs.
       rewrite mem_cat.
       apply/ orP. by left.
           + (*CP array*)
         destruct element.
             left. 
         apply (in_subseq H16 (gen_locs_works H2)).
- (*seq case*)
           inversion Hwarok; subst. exfalso. by apply (H w).
           eapply IHHcceval1; try apply Hcceval1;
             try reflexivity;
             try assumption.
           eapply WAR_I; try apply H8; try reflexivity; try assumption. assumption.
           Qed.

Lemma war_works_loc {N0 N Nend: nvmem} {V Vend: vmem} {c cend: command} {O: obseq} {W: the_write_stuff}
      {Wstart Rstart: warvars}:
    trace_cs (N, V, c) (Nend, Vend, cend) O W ->
    WARok (getdomain N0) Wstart Rstart c ->
    checkpoint \notin O ->
    (*O <> [::] -> empty trace annoying and i dont think
               i have to deal w it*)
  forall (l: loc),
(l \notin (remove Rstart (getfstwt W)) -> (*l not in OVERALL FW for this trace*)
    l \in (getwt W) -> (*l written to
                       IN THIS trace*)
          l \in (getdomain N0) \/ l \in Wstart).
intros T Hwarok Ho.
move: Wstart Rstart Hwarok.
dependent induction T; intros.
+ rewrite in_nil in H0. discriminate H0.
+ eapply war_works_loc_c; try apply H; try apply Hwarok; try assumption.
+ destruct W1 as [ [wW1 rW1] fwW1].
  destruct W2 as [ [wW2 rW2] fwW2].
  destruct Cmid as [ [Nmid Vmid] cmid].
  simpl in H1. simpl in H2. simpl in IHT.
  remember Ho as Hoo. clear HeqHoo.
  rewrite mem_cat in Hoo. move/ norP : Hoo => [Ho1 Ho2].
  move: (war_works_loc_c H0 Hwarok Ho1) => Hl1.
  move: (warok_partial H0 Ho1 Hwarok) => Hwarok2.
  simpl in Hwarok2.
  suffices: 
        (forall l : loc,
        l \notin remove (rW1 ++ Rstart) fwW2 ->
        l \in wW2 -> l \in getdomain N0 \/ l \in (wW1 ++ Wstart)).
  move => Hl2. simpl in Hl1.
  rewrite mem_cat in H2. move/orP: H2 => Happ.
destruct (l \in wW1) eqn: Hbool;
  rewrite mem_filter in H1; move/nandP : H1 => [Hr1 | Hweird].
+ suffices: (l \notin remove Rstart fwW1).
intros H500. apply Hl1; try assumption.
rewrite mem_filter. apply/nandP. by left.
+ rewrite mem_cat in Hweird. move/ norP: Hweird => [Hdone H600].
  apply Hl1. rewrite mem_filter. apply/ nandP. by right.
    by [].
 +suffices: (l \notin remove (rW1 ++ Rstart) fwW2).
  intros H500. destruct Happ as [Hw2 | contra].
  suffices: (l \in getdomain N0 \/ l \in wW1 ++ Wstart).
  move => [one | two]. by left. right. rewrite mem_cat in two.
  move/ orP : two => [contra | done]. rewrite Hbool in contra.
  discriminate contra. assumption.
  eapply Hl2; try assumption.
  rewrite Hbool in contra. discriminate contra.
  rewrite mem_filter. apply/nandP. left. rewrite mem_cat.
  apply/negPn / orP. right. apply/negPn: Hr1.
 +
(*what's below could well be stupid*)
   suffices: (l \notin remove (rW1 ++ Rstart) fwW2).
  intros H500. destruct Happ as [Hw2 | contra].
  suffices: (l \in getdomain N0 \/ l \in wW1 ++ Wstart).
  move => [one | two]. by left. right. rewrite mem_cat in two.
  move/ orP : two => [contra | done]. rewrite Hbool in contra.
  discriminate contra. assumption.
  eapply Hl2; try assumption.
  rewrite Hbool in contra. discriminate contra.
  rewrite mem_filter. apply/nandP.
  rewrite mem_cat in Hweird. move/ norP: Hweird. => [Hdone H600].
  rewrite mem_filter in Hdone. move/ nandP : Hdone => [Hd1 | Hd2].
  left. rewrite mem_cat. apply/negPn/ orP. left.
  by apply/negPn. by right.
  eapply IHT; try reflexivity; try assumption.
  Qed.


(*saying the exact same thing as war_works_loc*)
Lemma wts_cped_sv: forall{N0 N Nend: nvmem} {V Vend: vmem} {c cend: command} {O: obseq} {W: the_write_stuff}
                  {Wstart Rstart: warvars} {l: loc},
    trace_cs (N, V, c) (Nend, Vend, cend) O W ->
    WARok (getdomain N0) Wstart Rstart c ->
    checkpoint \notin O ->
    (*O <> [::] -> empty trace annoying and i dont think
               i have to deal w it*)
    l \notin (getdomain N0) ->
    l \in (getwt W) -> (*l written to
                       IN THIS trace*)
    l \in (remove Rstart (getfstwt W)) (*l not in OVERALL FW for this trace*)
          \/ l \in Wstart.
  intros.
  move: (war_works_loc H H0 H1) => Hl.
  destruct (l \in remove Rstart (getfstwt W)) eqn: Hin.
    by left.
    move/ negbT / (Hl l): Hin => Himp.
    move: (Himp H3) => [one | two].
    exfalso. by move/ negP : H2. by right.
Qed.

Lemma war_works {N0 N Nend: nvmem} {V Vend: vmem} {c cend: command} {O: obseq} {W: the_write_stuff}:
    trace_cs (N, V, c) (Nend, Vend, cend) O W ->
  subset_nvm N0 N ->
    WARok (getdomain N0) [::] [::] c ->
    checkpoint \notin O ->
    all_diff_in_fww N V c (N0 U! Nend).
  intros T Hsub Hwarok Ho.
  econstructor; try apply T; try assumption.
  intros l Hneq.
  destruct N as [Nmap Nd].
  destruct N0 as [N0map N0d].
  destruct Nend as [Nendmap Nendd].
  unfold updatemaps in Hneq. simpl in Hneq.
  assert (l \notin N0d) as Hnin0.
  apply/negP. intros contra.
  rewrite ifT in Hneq. apply Hneq.
  unfold subset_nvm in Hsub. symmetry. by eapply Hsub.
  assumption.
  rewrite ifF in Hneq.
  apply (update T) in Hneq.
  move: (war_works_loc T Hwarok Ho) => Hl.
  rewrite remove_empty in Hl.
  apply/ negPn/ negP. intros contra.
  move/ Hl : contra. => [contra1 | contra2].
  assumption.
  move/negP: Hnin0. by apply.
    by [].
    by apply negbTE. 
Qed.

Lemma same_com {N0 N V c Nmid Vmid cmid O1 W1 Nend1 Vend cend O2 W2}:
  WARok (getdomain N0) [::] [::] c ->
  subset_nvm N0 N ->
  trace_cs (N, V, c) (Nmid, Vmid, cmid) O1 W1 -> (*need this so you know what
                                                 to update with*)
  checkpoint \notin O1 ->
  trace_cs (N0 U! Nmid, V, c) (Nend1, Vend, cend) O2 W2 ->
  checkpoint \notin O2 ->
  exists (Nend2: nvmem), trace_cs (N, V, c) (Nend2, Vend, cend) O2 W2.
  intros Hwar Hsub Tmid Ho1 T2 Ho2.
  move: (war_works Tmid Hsub Hwar Ho1) => Hdiff.
  eapply same_com_help; try apply Hdiff; try assumption. apply T2.
Qed.

Lemma same_comi {N0 N V c O1 W1 Nend Vend cend }:
  WARok (getdomain N0) [::] [::] c ->
  subset_nvm N0 N ->
  trace_i1 ((N0, V, c), N, V, c) ((N0, V, c), Nend, Vend, cend) O1 W1 ->
  checkpoint \notin O1 ->
  exists (Nend2: nvmem) (Oc: obseq) (Wc: the_write_stuff), (trace_cs (N, V, c) (Nend2, Vend, cend) Oc Wc /\
checkpoint \notin Oc).
  intros. dependent induction  H1.
  exists Nend O W. split; assumption.
  suffices:(exists Nend2 Oc Wc,
               trace_cs (N0 U! Nmid, V, c)
                 (Nend2, Vend, cend) Oc Wc /\
               checkpoint \notin Oc
           ). move => [Nend2 [Ocend [Wcend [Tend Hocend] ] ] ].
  move: (same_com H H0 H3 H4 Tend Hocend) => [Nend0 Tdone].
  exists Nend0 Ocend Wcend. split; assumption.
  eapply IHtrace_i1; try reflexivity; try assumption.
  apply sub_update.
  repeat rewrite mem_cat in H2. move/norP: H2 => [Hblah H2].
  move/norP: H2 => [contra Hb]. rewrite mem_seq1 in contra.
    by case/eqP : contra.
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
    (*getting ready to apply single_step_alls*)
    assert (O0 <> [::]) as Ho0.
-
  intros Heq1. subst.
  move/empty_trace_cs1 : T => [ [contra10 [contra11 contra12] ] contra2]. subst. case H2 as [Hskip | [crem [w Hcp] ] ]; subst.
    inversion Hcceval. move/negP : H1. apply.
    (*start here why is apply/negP different from this*)
    apply (observe_checkpt_s Hcceval).
    (*ask arthur i want to write
     exists O exists W H, like a function*)
         move: (single_step_alls T Ho0 H0) => [W1 [O1 [T1 [Hsub Hw ] ] ] ].
         econstructor; try apply T1; try assumption.
         apply/ negP => contra.
         move/ negP : H3. apply.
         apply (in_subseq Hsub contra).
        (* apply (update_domc H Hcceval); assumption.*)
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

Lemma fw_gets_bigger:forall{ N Nmid Nend: nvmem} {V Vmid Vend: vmem} {c cmid cend: command}
                         {Omid O: obseq} {Wmid W: the_write_stuff} {l: loc},
    trace_cs (N, V, c) (Nmid, Vmid, cmid) Omid Wmid ->
    checkpoint \notin Omid ->
    trace_cs (N, V, c) (Nend, Vend, cend) O W ->
    end_com cend ->
    l \in (getfstwt Wmid) -> l \in (getfstwt W). Admitted.
                  

Check prefix_seq. 
  Lemma ctrace_det_obs_skip {N V c Nmid Vmid cmid
                          Nend Vend Omid Wmid Oend Wend}:
    trace_cs (N, V, c)
             (Nmid, Vmid, cmid) Omid Wmid ->
    checkpoint \notin Omid ->
 trace_cs (N, V, c)
 (Nend, Vend, Ins skip) Oend Wend ->
    checkpoint \notin Oend ->
 Omid <=p Oend. Admitted. (*induct over 1, then 2 nested*)

  Lemma ctrace_det_obs_CP {N V c Nmid Vmid cmid
                          Nend Vend Omid Wmid Oend Wend w crem}:
    trace_cs (N, V, c)
             (Nmid, Vmid, cmid) Omid Wmid ->
    checkpoint \notin Omid ->
 trace_cs (N, V, c)
 (Nend, Vend, (incheckpoint w);; crem) Oend Wend ->
    checkpoint \notin Oend ->
 Omid <=p Oend. Admitted. (*induct over 1, then 2 nested*)


  (*need the CPs so i know which command is bigger
   might be easier to just have a stpe index lol*)
  Lemma ctrace_det_obs {N V c Nmid Vmid cmid
                          Nend Vend Omid Wmid Oend Wend cend}:
    trace_cs (N, V, c)
             (Nmid, Vmid, cmid) Omid Wmid ->
    checkpoint \notin Omid ->
 trace_cs (N, V, c)
 (Nend, Vend, cend) Oend Wend ->
 checkpoint \notin Oend ->
 end_com cend ->
 Omid <=p Oend. Admitted. 

  Lemma append_c {N1 V1 c1 N2 V2 crem O1 W1 N3 V3 c3 O2 W2}
        :
        trace_cs (N1, V1, c1) (N2, V2, crem) O1 W1 ->
        trace_cs (N2, V2, crem) (N3, V3, c3) O2 W2 ->
        trace_cs (N1, V1, c1) (N3, V3, c3) (O1 ++ O2) (append_write W1 W2).
Admitted.

  Lemma append_cps {N1 V1 c1 N2 V2 crem O1 W1 N3 V3 c3 O2 W2}
        {w: warvars}:
        trace_cs (N1, V1, c1) (N2, V2, incheckpoint w;; crem) O1 W1 ->
        trace_cs (N2, V2, crem) (N3, V3, c3) O2 W2 ->
        trace_cs (N1, V1, c1) (N3, V3, c3) (O1 ++ [::checkpoint] ++ O2) (append_write W1 W2).
Admitted.

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
    (*start here is there a way to combine the above*)
    move: (three_bc1 H3 H1 H21) => [Ncmid [Tmid Hmid] ].
    suffices: exists Nc1,
               trace_cs (Ncmid, Vmid, cmid) (Nc1, V1, c1) O2 W2 /\
               all_diff_in_fw Ni1 V1 c1 Nc1.
  - move => [ Nc1 [Tmid2end Hmid2end] ]. exists Nc1. split; try assumption.
    eapply CsTrace_Cons; try apply Tmid2end; try assumption.
    eapply IHtrace_cs; try reflexivity; try assumption.
 Qed.


Lemma neg_observe_rb: forall {N N': nvmem} {V V': vmem}
                     {c c': command} 
                    {O: obseq} {W: the_write_stuff},
    trace_cs (N, V, c) (N', V', c') O W ->
    reboot \notin O.
Admitted.

   Lemma update_diff N0 N1 N2: forall(l: loc), ((getmap N1) l !=
                                                       (getmap (N0 U! N2)) l) ->
                                          ((getmap N0) l <> (getmap N1) l /\ l \in (getdomain N0)) \/
                                          ( (getmap N2) l <> (getmap N1) l /\
                                            l \notin (getdomain N0)
                                          ). Admitted.

  (* Lemma sub_update: forall(N0 N1: nvmem),
    subset_nvm N0 (N0 U! N1).
  intros.
  destruct N0, N1.
  unfold subset_nvm. split.
  simpl. apply prefix_subseq.
  intros. simpl. by rewrite H.
  Qed.*)

   Lemma sub_restrict: forall(N1: nvmem) (w: warvars) (Hf: wf_dom w (getmap N1)), subset_nvm
                                                                   (restrict N1 w Hf) N1.
   Admitted.


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





   Lemma adif_refl {N V c c1 Nend Vend O W}:
  trace_cs (N, V, c) (Nend, Vend, c1) O W ->
  end_com c1 ->
  checkpoint \notin O ->
        all_diff_in_fw N V c N.
Admitted.
(*cant actually use ww for this*)
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
   (*apply (eq_trans (getmap Nc1 (inr el))).
  apply (H1 el). apply (H9 el).*)
  intros l Hneq.
  destruct (getmap Nc0 l == getmap Nc1 l) eqn:Hbool; move/ eqP : Hbool => Heq. rewrite Heq in Hneq. by apply H8 in Hneq.
  by apply H1 in Heq.
Qed.

        (*induct on length of 1st trace, rewrite nested filters into filtering
         out the appended list*)

Lemma warok_cp {N1 N2 V1 V2 c crem O W}
      {w0 w1: warvars}:
  WARok w0 [::] [::] c ->
  trace_cs (N1, V1, c) (N2, V2, incheckpoint w1;; crem) O W ->
  WARok w1 [::] [::] crem. Admitted.


Lemma no_CP_in_seq: forall{O1 O2: obseq},
    (O1 <=m O2) -> checkpoint \notin O1 /\ checkpoint \notin O2.
  Admitted.

Lemma threeIS1 {N0 Ni Ni1 Nend V V1 Vend c c1 Nc O W Oend Wend cend}:
  all_diff_in_fw Ni V c Nc -> (*ensures well formed up till nearest endcom*)
  trace_i1 ((N0, V, c), Ni, V, c) ((N0, V, c), Ni1, V1, c1) O W ->
  WARok (getdomain N0) [::] [::] c ->
  subset_nvm N0 Ni ->
  checkpoint \notin O ->
   trace_cs (Ni1, V1, c1) (Nend, Vend, cend) Oend Wend -> (*ensuring int mem is well formed,
                                                   can put Ni1 arbitrarily far back after this lemma is finished*)
   end_com cend -> checkpoint \notin Oend ->
  (exists(Oc Oendc: obseq) (Nc1: nvmem) (Wc Wendc: the_write_stuff),
      trace_cs (Nc, V, c) (Nc1, V1, c1) Oc Wc /\
      all_diff_in_fw Ni1 V1 c1 Nc1 /\ (O ++ Oend <=m Oc ++ Oendc)
     /\ trace_cs (Nc1, V1, c1) (Nend, Vend, cend) Oendc Wendc
  ).
  Proof. intros. move: Nc H H3. (* remember H0 as Ht. induction H0.
                    ask arthur*)
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
    (*move => el. apply/ eqP / negPn/ negP => contra.
   apply update_diff in contra. destruct contra as [ [con11 con12] | [con21 con22] ].
   apply con11. apply (H4 (inr el) con12).
   move: (update H (not_eq_sym con21)) => Hdiff.
   move/negP :(wts_cped_arr H H3 H1 con22). by apply.*)
   move => l. move/eqP/update_diff => [ [diff11 diff12] | [diff21 diff22] ]. case diff11. apply (H4 l diff12).
   move: (update H (not_eq_sym diff21)) => Hdiff.
   (*start here clean up repeated work in above*)
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
   (*apply CP_Base.
   rewrite- catA.
   rewrite - catA.*)
    assert (checkpoint \notin Oc ++ Oendc).
    apply no_CP_in_seq in ass3.
    by move: ass3 => [Ha1 Ha2].
   (* rewrite mem_cat.
      by apply/ norP.*)
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

(*wouldnt need this guy if i took in an intermittent trace in 3?*)
Lemma trace_append_ic {N0 V0 c0 N01 V01 c01 N1 V1 c1 N2 V2 c2
                                      N3 V3 c3}
                  {O1 O2: obseq}
                  {W1 W2: the_write_stuff}:
                  trace_i1 ((N0, V0, c0), N1, V1, c1) ((N01, V01, c01), N2, V2, c2) O1 W1 ->
      trace_cs (N2, V2, c2) (N3, V3, c3) O2 W2  ->
      exists(N02: nvmem) (V02: vmem) (c02: command), trace_i1 ((N0, V0, c0), N1, V1, c1)
                                                         ((N02, V02, c02), N3, V3, c3) (O1 ++ O2) (append_write W1 W2).
  Admitted.



Lemma three {N0 N01 V01 c01 Ni Ni1 Nend V V1 Vend c c1 Nc O W Oend Wend cend}:
  all_diff_in_fw Ni V c Nc ->
  trace_i1 ((N0, V, c), Ni, V, c) ((N01, V01, c01), Ni1, V1, c1) O W ->
  WARok (getdomain N0) [::] [::] c ->
  subset_nvm N0 Ni -> 
  trace_cs (Ni1, V1, c1) (Nend, Vend, cend) Oend Wend -> (*ensuring int mem is well formed,
                                                   can put Ni1 arbitrarily far back after this lemma is finished*)
  end_com cend -> checkpoint \notin Oend ->
  (exists(Oc Oendc: obseq) (Nc1: nvmem) (Wc Wendc: the_write_stuff) ,
      trace_cs (Nc, V, c) (Nc1, V1, c1) Oc Wc /\
      all_diff_in_fw Ni1 V1 c1 Nc1 /\ (O ++ Oend <=f (Oc ++ Oendc)) /\
      trace_cs (Nc1, V1, c1) (Nend, Vend, cend) Oendc Wendc
  ).
Proof.
  intros. move: Nc H H3. (* remember H0 as Ht. induction H0.
                    ask arthur*)
dependent induction H0; intros.
  + move: (three_bc H3 H H0) => [ Nc1 [Tdone Hdone] ].
    exists O Oend Nc1 W Wend. repeat split; try assumption.
    apply CP_Base. apply RB_Base; try (rewrite mem_cat; apply/ norP; split);
    try assumption.
    apply (neg_observe_rb H).
    apply (neg_observe_rb H6).
    apply (adif_works Hdone H6); try assumption.
  + 
    move: (iTrace_RB H H0 H1 H2) => bigtrace. Check threeIS1.
    assert (checkpoint \notin O1 ++ [:: reboot] ++ O2) as Hcp.
    rewrite mem_cat. apply/ norP. split; try assumption.
Check threeIS1.
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
        (*last inductive case starts here*)
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
      (*consider: maybe your type should just split by reboots
       rather than checkpoints*)
     - subst. move: (append_cps H11 H21) => T1.
      exists (Oc1 ++ [::checkpoint] ++ Oc2) Oendc2 Nc2 (append_write Wc1 Wc2) Wendc2.
      repeat split; try assumption.
      repeat rewrite - catA. apply CP_IND; try assumption.
      - eapply IHtrace_i1_2;try reflexivity; try assumption;

        (*Nmid and Nc1 are the same but they aren't
         substituting*)
        try apply sub_restrict.
        apply (adif_refl H13 H15 H14).
        (*why not just do an empty trace here
         up till nearest cp*)
       Check trace_append_ic.
       move: (trace_append_ic H0_0 H3) => [Nc1endi [Vc1endi [cmend Tendi] ] ].
       Check threeIS1.
              assert ( checkpoint \notin [::]) as Hcp.
              by rewrite in_nil.
       move: (threeIS1 H0 H0_ H1 H2 H
                       (CsTrace_Empty
                          (Nmid, Vmid, ccp )) Hend Hcp).

       (*need to put in a bigger trace for threeIS1
        also to get the crem part*)
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
      Check same_comi. subst.
      move: (same_comi Hwarok2 (sub_restrict Nc1 w Hw) Tend Hoendc).
      =>
      [Nc1end [Oendc [Wendc [Tendc Hcpoendc] ] ] ].                                                            
       exists Oc Oendc Nc1 Wc Wendc Nc1end. exists Vc1end cend0. subst.
       repeat split; try assumption. 
       econstructor; try eapply CsTrace_Empty; auto.
       by repeat rewrite cats0 in Hm. assumption.
Qed.

  Lemma both_cp {O1 O2} :
    (O1 <=f O2) -> checkpoint \notin O1 ->
    (O1 <=m O2) /\ checkpoint \notin O2.
    Admitted.
  (*  intros. inversion H; subst; try assumption.
    repeat rewrite mem_cat in H0.
    move/norP : H0 => [Hb H0]. move/norP: H0 => [contra Hb2].
    exfalso. move/negP: contra. by apply. Qed.*)



Lemma notin (o: obs) : o \notin [::].
Admitted.

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
Check three.
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



