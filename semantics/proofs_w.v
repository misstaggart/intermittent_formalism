Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Strings.String Program Logic.FunctionalExtensionality.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq fintype ssrnat ssrfun.
From TLC Require Import LibTactics LibLogic.
From Semantics Require Export programs semantics algorithms lemmas_1
     lemmas_0 proofs_0 proofs_n proofs_d. 


(*weaker version of all_diff_in_fw where the requireement that
 the program can make it up till a checkpoint or termination is omitted*)
Inductive all_diff_in_fww: nvmem -> vmem -> command -> nvmem -> Prop :=
  Diff_in_FWw: forall{N1 V1 c1 N2 V2 c2 N1c O W} (T: trace_cs (N1, V1, c1) (N2, V2, c2) O W),
    checkpoint \notin O -> 
( forall(l: loc ), ((getmap N1) l <> (getmap N1c) l) -> (l \in getfstwt W))
-> all_diff_in_fww N1 V1 c1 N1c.

 Lemma add_skip_ins_w {N1 V l N2}: all_diff_in_fww N1 V (Ins l) N2 ->
                                 all_diff_in_fww N1 V (l;; skip) N2.
   intros Hdiff. inversion Hdiff; subst.
   inversion T; subst.
   - 
     econstructor; try eapply CsTrace_Empty; try by [].
     econstructor. eapply CsTrace_Single.
     move: (cceval_skip H1) => eq. subst.
     eapply Seq; try apply H1; try by []; try assumption. intros w contra. subst. inversion H1.
     intros contra. subst. inversion H1. assumption.
     assumption.
     destruct Cmid as [ [nm vm] cm].
     move: (cceval_skip H3) => eq. subst.
     econstructor. eapply CsTrace_Single.
     eapply Seq; try apply H3; try by []; try assumption. intros w contra. subst. inversion H3.
     intros contra. subst. inversion H3.
     rewrite mem_cat in H. move/ norP: H => [Ho1 Ho2].
     assumption.
     suffices: W2 = emptysets. move => eq. subst.
     rewrite append_write_empty in H0.
     assumption.
     move: (trace_skip H1) => Heq. subst.
       by move/empty_trace_cs1: H1 => [one two].
     Qed.

 Lemma agreeonread_ins_w_r: forall{N Nend N2: nvmem} {V Vend: vmem}
                        {l: instruction} {crem c1: command}
                   {O : obseq} {W: the_write_stuff},
  all_diff_in_fww N V (l;;crem) N2 ->
             cceval_w (N2, V, Ins l) O (Nend, Vend, c1) W ->
             ( forall(z: loc), z \in (getrd W) ->
                                (getmap N2) z = (getmap N) z).
      intros. inversion H; subst. apply/ eqP /negPn /negP.
        rename H1 into Hread.
      intros contra.
      move/ eqP: contra => contra. apply not_eq_sym in contra.
      apply (H3 z) in contra.
      destruct (O0 == [::]) eqn: Hbool.
      - move/eqP : Hbool => Heq. subst.
        move: (empty_trace_cs1 T) => [ [one two] three four].
        subst. discriminate contra.
      - move/ negbT /eqP : Hbool => Hneq.
        move: (single_step_alls_rev T Hneq) =>
        [Cmid [W1 [Wrest [O1 [Hcceval [Hsubseq Hw] ] ] ] ] ].
        subst.
        simpl in contra.
        inversion Hcceval; subst.
        destruct Hsubseq as [Orest Hsub].
        rewrite Hsub mem_cat in H2.
        move/norP : H2 => [contra1 H111].
        move/ negP: contra1. by apply.
        inversion H0; subst.
        move: (cceval_agr H0 H12) => Heqrd.
        rewrite Heqrd in Hread.
        move: (fw_nin_r_c z H12 Hread) => Hfw.
        rewrite mem_cat in contra.
        move/orP : contra => [contra1 | contra2].
        rewrite mem_filter in contra1.
        move/ andP : contra1  => [one two].
        move/negP : one. by apply.
        move/negP : Hfw. by apply.
    Qed.

    Lemma agreeonread_ins_w_l: forall{N Nend N2: nvmem} {V Vend: vmem}
                        {l: instruction} {crem c1: command}
                   {O : obseq} {W: the_write_stuff},
  all_diff_in_fww N V (l;;crem) N2 ->
             cceval_w (N, V, Ins l) O (Nend, Vend, c1) W ->
             ( forall(z: loc), z \in (getrd W) ->
                                (getmap N) z = (getmap N2) z).
      intros. inversion H; subst. apply/ eqP /negPn /negP.
        rename H1 into Hread.
      intros contra.
      move/ eqP: contra => contra. 
      apply (H3 z) in contra.
      destruct (O0 == [::]) eqn: Hbool.
      - move/eqP : Hbool => Heq. subst.
        move: (empty_trace_cs1 T) => [ [one two] three four].
        subst. discriminate contra.
      - move/ negbT /eqP : Hbool => Hneq.
        assert (cceval_w (N, V, l;; crem) O (Nend, Vend, crem) W) as Hcceval.
        move: (single_step_alls_rev T Hneq). =>
        [Cmid [W1 [Wrest [O1 [Hcceval [Hsubseq Hw] ] ] ] ] ].
        inversion Hcceval; subst.
        destruct Hsubseq as [Orest Hsub].
        rewrite Hsub mem_cat in H2.
        move/norP : H2 => [contra1 H111]. exfalso.
        move/ negP: contra1. by apply.
        inversion H0; subst.
        move: (determinism_c H0 H12) => [one [two three] ].
        inversion one. subst.
        assumption.
        move: (single_step_alls T Hneq Hcceval). =>
        [W1 [O1 [Trem [Hsub Heq] ] ] ].
        rewrite Heq in contra. unfold append_write in contra.
        simpl in contra.
        move: (fw_nin_r_c z Hcceval Hread) => Hfw.
        rewrite mem_cat in contra.
        move/orP : contra => [contra1 | contra2].
        rewrite mem_filter in contra1.
        move/ andP : contra1  => [one two].
        move/negP : one. by apply.
        move/negP : Hfw. by apply.
        Qed.

 Lemma agreeonread_w_r: forall{N Nend N2: nvmem} {V Vend: vmem}
                        {c c1: command}
                   {O : obseq} {W: the_write_stuff},
  all_diff_in_fww N V c N2 ->
             cceval_w (N2, V, c) O (Nend, Vend, c1) W ->
            ( forall(z: loc), z \in (getrd W) ->
                   (getmap N2) z = (getmap N) z).
   intros. move: H H0 H1 => Hdiff Hcc Hr. dependent induction c.
   apply add_skip_ins_w in Hdiff.
   eapply agreeonread_ins_w_r; try apply Hdiff; try apply Hcc; try assumption.
   inversion Hcc; subst; try( rewrite in_nil in Hr; discriminate Hr).
   eapply agreeonread_ins_w_r; try apply Hdiff; try apply H10; try assumption.
   inversion Hdiff; subst.
   apply/eqP /negPn/ negP. intros contra. move/eqP: contra => contra.
   apply not_eq_sym in contra. apply (H0 z) in contra.
      destruct (O0 == [::]) eqn: Hbool; move/eqP : Hbool => Heq; subst.
      - 
        move: (empty_trace_cs1 T) => [ [one two] three four].
        subst. discriminate contra.
      - 
        move: (single_step_alls_rev T Heq) =>
        [Cmid [W1 [Wrest [O1 [Hcceval [Hsubseq Hw] ] ] ] ] ].
        move: (cceval_agr Hcceval Hcc) => Hww.
        rewrite Hw in contra.
        unfold append_write in contra. simpl in contra. rewrite Hww in contra. rewrite - Hww in Hr.
        move: (fw_nin_r_c z Hcceval Hr) => Hfw.
        rewrite mem_cat in contra.
        move/ orP : contra. => [con1 | con2].
        rewrite mem_filter in con1. move/andP: con1 => [con11 con12]. move/ negP: con11. apply. by rewrite - Hww.
        move/ negP: Hfw. by apply.
    Qed.

 Lemma agreeonread_w_l: forall{N Nend N2: nvmem} {V Vend: vmem}
                        {c c1: command}
                   {O : obseq} {W: the_write_stuff},
  all_diff_in_fww N V c N2 ->
             cceval_w (N, V, c) O (Nend, Vend, c1) W ->
            ( forall(z: loc), z \in (getrd W) ->
                   (getmap N) z = (getmap N2) z).
   intros. move: H H0 H1 => Hdiff Hcc Hr. dependent induction c.
   apply add_skip_ins_w in Hdiff.
   eapply agreeonread_ins_w_l; try apply Hdiff; try apply Hcc; try assumption.
   inversion Hcc; subst; try( rewrite in_nil in Hr; discriminate Hr).
   eapply agreeonread_ins_w_l; try apply Hdiff; try apply H10; try assumption.
   inversion Hdiff; subst.
   apply/eqP /negPn/ negP. intros contra. move/eqP: contra => contra.
   apply (H0 z) in contra.
      destruct (O0 == [::]) eqn: Hbool; move/eqP : Hbool => Heq; subst.
      - 
        move: (empty_trace_cs1 T) => [ [one two] three four].
        subst. discriminate contra.
      - 
        move: (single_step_alls T Heq Hcc). =>
        [Wrest [Orest [Trest [Hsubseq Hw] ] ] ].
        rewrite Hw in contra.
        unfold append_write in contra. simpl in contra.
        move: (fw_nin_r_c z Hcc Hr) => Hfw.
        rewrite mem_cat in contra.
        move/ orP : contra. => [con1 | con2].
        rewrite mem_filter in con1. move/andP: con1 => [con11 con12]. move/ negP: con11. by apply. 
        move/ negP: Hfw. by apply.
    Qed.

 Lemma same_com_hcbc {N N1 Nend1 V V1 l crem O W c1} : all_diff_in_fww N V (l;;crem) N1 ->
                              cceval_w (N1, V, Ins l) O (Nend1, V1, c1) W ->
                              exists(Nend: nvmem), (cceval_w (N, V, Ins l) O (Nend, V1, c1) W) /\
 forall(l: loc), l \in (getwt W) -> ((getmap Nend) l = (getmap Nend1) l).
   intros Hdiff Hcceval1.
move: (agreeonread_ins_w_r Hdiff Hcceval1) => agr.
      dependent induction Hcceval1; simpl in agr.
      - exists (updateNV_sv N x v). split. apply NV_Assign; try assumption.
        eapply agr_imp_age; try apply H; try assumption.
        simpl. intros l Hin. rewrite mem_seq1 in Hin.
        move/ eqP : Hin => Hin. subst.
        destruct N as [Nmap ND].
        destruct N1 as [N1map N1D].
        unfold updateNV_sv. unfold updatemap. simpl.
        destruct (v == error) eqn: Hbool. simpl in agr.
        move/ eqP: Hbool => Heq. subst. inversion H1.
        remember (inl x) as xloc.
        suffices: (if xloc == xloc then v else Nmap xloc) = v /\
                  (if xloc == xloc then v else N1map xloc) = v.
        move => [one two].
          by rewrite one two.
        split; by apply ifT.
     - exists N. split. apply V_Assign; try assumption.
       eapply agr_imp_age; try apply H; try assumption.
       simpl. move => l contra.
        rewrite in_nil in contra. by exfalso.
     - exists (updateNV_arr N element a v). split. eapply Assign_Arr.
       eapply agr_imp_age; try apply H; try assumption.
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
        destruct N as [Nmap ND].
        destruct N1 as [N1map N1D].
        unfold updateNV_arr. simpl.
        rewrite mem_seq1 in Hin. move/ eqP : Hin => Hin. subst.
        unfold updatemap.
        suffices: 
          ((if inr element == inr element then v else Nmap (inr element)) = v
                                                                              /\
  (if inr element == inr element then v else N1map (inr element)) = v).
        move => annoying.
        move: (annoying loc_eqtype loc_eqtype) => [one two].
        destruct (v == error) eqn: Hbool.
        move/ eqP: Hbool => three. subst. inversion H1.
          by rewrite one two.
          intros. split; by apply ifT.
          Qed.

Lemma trace_converge_minus1w {N V N' Nmid Vmid Nmid'
                            O W} {l: instruction}:
  all_diff_in_fww N V l N' ->
  cceval_w (N, V, Ins l) O (Nmid, Vmid, Ins skip) W ->
  cceval_w (N', V, Ins l) O (Nmid', Vmid, Ins skip) W ->
  Nmid = Nmid'.
  move => Hdiff Hcceval1 Hcceval2.
  inversion Hdiff. subst.
dependent induction T.
-
  suffices: N2 = N'. move => Heq. subst.
  move: (determinism_c Hcceval1 Hcceval2). =>
  [ one two]. inversion one. by subst.
  simpl in H0. apply nvmem_eq. intros z.
  apply/eqP/ negPn /negP. intros contra.
  move/ eqP : contra => contra. apply H0 in contra.
  discriminate contra.
-
  apply nvmem_eq. intros z.
  move: (same_com_hcbc (add_skip_ins_w Hdiff) Hcceval2).
  => [Nend [Hcceval3 Hloc] ].
  move: (determinism_c Hcceval3 Hcceval1) => [one [two three] ]. inversion one. subst.
  destruct (z \in (getwt W)) eqn:Hbool.
  by apply (Hloc z) in Hbool.
  suffices: (getmap N) z = (getmap N') z.
  move => Heq.
  apply (connect_mems Hcceval1 Hcceval2 (negbT Hbool) Heq).
  move: (determinism_c H Hcceval1). => [eq0 [eq1 eq2] ]. inversion eq0. subst.
  apply/eqP /negPn /negP. intros contra.
  move/ eqP / (H1 z) : contra => contra.
  apply (in_subseq (fw_subst_wt_c Hcceval1)) in contra.
  rewrite Hbool in contra. discriminate contra.
  destruct Cmid as [ [nm vm] cm]. move: (cceval_skip H0) => Heq. subst. apply trace_skip in T. exfalso. by apply H.
Qed.

 Lemma same_com_hc {N N1 V c Nend2 V1 c1 O W}:
  all_diff_in_fww N V c N1 ->
  cceval_w (N1, V, c) O (Nend2, V1, c1) W -> (*use that W2 must be a subset of W*)
  checkpoint \notin O ->
  exists (Nend1: nvmem), cceval_w (N, V, c) O (Nend1, V1, c1) W
                             /\ all_diff_in_fww Nend1 V1 c1 Nend2.
    intros Hdiff Hcceval1 Ho.
   induction c.
  - move: (same_com_hcbc (add_skip_ins_w Hdiff) Hcceval1). => [Nend [Hcceval Hloc] ].
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
       exfalso. by apply H9.
         + move: (same_com_hcbc Hdiff H10). => [Nend [ Hcceval Hloc] ].
           exists Nend. split.
       apply Seq; try assumption.
       inversion Hdiff; subst.
      destruct (O0 == [::]) eqn: Hbool.
       - move/ eqP : Hbool => Hbool. subst.
      apply empty_trace_cs1 in T. move: T =>
                                  [ [one two ] three four].
      subst.
      suffices: (getmap N2) =1 (getmap N1). move/nvmem_eq => H500. subst.
      move: (determinism_c H10 Hcceval) => [ [one two] ]. subst.
      econstructor; try apply CsTrace_Empty; try assumption.
      by [].
      intros l0. apply/ eqP /negPn /negP. intros contra.
      move/ eqPn / (H0 l0) : contra.
      by rewrite in_nil. auto.
       - move/ negbT / eqP : Hbool => Hneq.
         suffices: cceval_w (N, V, l;;c1) O (Nend, V1, c1) W.
         move => Hccevalbig.
move: (single_step_alls T Hneq Hccevalbig). => [Wrest [Orest
                                                     [Trest
                                [Hsubseq Hwrite] ] ] ].
       econstructor; try apply Trest; try assumption.
       apply/negP. intros contra.
       apply/negP / negPn: H.
       rewrite Hsubseq. rewrite/ orP mem_cat. apply/orP. by right.
           intros l0 Hl0. remember Hl0 as Hneql.
           clear HeqHneql.
           suffices: getmap Nend l0 <> getmap Nend2 l0 -> l0 \notin getwt W.
           intros Hlocc. apply Hlocc in Hl0.
           suffices: (l0 \in getfstwt W0).
           intros Hfw.
           subst. move/ fw_split : Hfw => [one | two].
           apply (in_subseq (fw_subst_wt_c Hcceval
                 )) in one.
           exfalso. move/ negP : Hl0. by apply.
             by move: two => [whatever done].
             apply H0.
             move: (update_one_contra l0 Hcceval Hl0) => Heq1.
             move: (update_one_contra l0 Hcceval1 Hl0) => Heq2.
             by rewrite Heq1 Heq2.
             clear Hneq. intros Hneq. apply/negP. intros contra.
             apply Hneq. by apply Hloc.
             apply Seq; try assumption.
         + inversion Hcceval1; subst; exists N; inversion Hdiff; subst;
           destruct (O == [::]) eqn: Hbool.
          -  move/ eqP : Hbool => Hbool. subst.
      apply empty_trace_cs1 in T. move: T =>
                                  [ [one two ] three four].
      subst.
      suffices: (getmap N2) =1 (getmap Nend2). move/nvmem_eq => H500. subst. split; try assumption.
      econstructor; try apply CsTrace_Empty; try assumption.
      intros l0. apply/ eqP /negPn /negP. intros contra.
      move/ eqPn / (H0 l0) : contra.
      by rewrite in_nil. auto.
          - move/ negbT / eqP : Hbool => Hneq.
            move: (agreeonread_w_r Hdiff Hcceval1) => agr.
            move: (agr_imp_age H9 agr) => Heval.
            split.
           apply If_T; try assumption.
         move: (single_step_alls_rev T Hneq). => [
                                                Cmid [W1
                                                [Wrest1 [O1
                                                     [Hcceval
                                                        [Hsubseq1 Hwrite1] ] ] ] ] ].
       move: (single_step_alls T Hneq Hcceval). => [Wrest [Orest
                                                     [Trest
                                                        [Hsubseq Hwrite] ] ] ].
       destruct Cmid as [ [Nmid Vmid] cmid].
       inversion Hcceval; subst.
       econstructor; try apply Trest; try assumption.
         destruct Wrest1 as [ [w1 w2 ] w3].
         destruct Wrest as [ [wr1 wr2] wr3]. inversion Hwrite.
        
         repeat rewrite cats0 in H2.
         repeat rewrite cats0 in H4.
         intros l Hneql.
         simpl.
         apply H0 in Hneql. subst. simpl in Hneq.
         unfold append_write in Hneql.
         simpl in Hneql. rewrite cats0 in Hneql.
         rewrite H4 in Hneql.
         rewrite mem_filter in Hneql.
           by move/ andP : Hneql => [one two].
           move: (determinism_e H12 Heval) => [one two].
           inversion two.
          -  move/ eqP : Hbool => Hbool. subst.
      apply empty_trace_cs1 in T. move: T =>
                                  [ [one two ] three four].
      subst.
      suffices: (getmap N2) =1 (getmap Nend2). move/nvmem_eq => H500. subst. split; try assumption.
      econstructor; try apply CsTrace_Empty; try assumption.
      intros l0. apply/ eqP /negPn /negP. intros contra.
      move/ eqPn / (H0 l0) : contra.
      by rewrite in_nil. auto.
          - move/ negbT / eqP : Hbool => Hneq.
            move: (agreeonread_w_r Hdiff Hcceval1) => agr.
            move: (agr_imp_age H9 agr) => Heval.
            split.
           apply If_F; try assumption.
         move: (single_step_alls_rev T Hneq). => [
                                                Cmid [W1
                                                [Wrest1 [O1
                                                     [Hcceval
                                                        [Hsubseq1 Hwrite1] ] ] ] ] ].
       move: (single_step_alls T Hneq Hcceval). => [Wrest [Orest
                                                     [Trest
                                                        [Hsubseq Hwrite] ] ] ].
       destruct Cmid as [ [Nmid Vmid] cmid].
       inversion Hcceval; subst.
           move: (determinism_e H12 Heval) => [one two].
           inversion two.
       econstructor; try apply Trest; try assumption.
         destruct Wrest1 as [ [w1 w2 ] w3].
         destruct Wrest as [ [wr1 wr2] wr3]. inversion Hwrite.
        
         repeat rewrite cats0 in H2.
         repeat rewrite cats0 in H4.
         intros l Hneql.
         simpl.
         apply H0 in Hneql. subst. simpl in Hneq.
         unfold append_write in Hneql.
         simpl in Hneql. rewrite cats0 in Hneql.
         rewrite H4 in Hneql.
         rewrite mem_filter in Hneql.
           by move/ andP : Hneql => [one two].
Qed.

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


Lemma war_cceval: forall{N0 N Nmid: nvmem} {V Vmid: vmem} {c cmid: command}
                   {l: instruction}
                   {O: obseq} {W: the_write_stuff} {Wstart Rstart W' R': warvars},

        cceval_w (N, V, l;;c) O (Nmid, Vmid, cmid) W ->
        WAR_ins (getdomain N0) Wstart Rstart l W' R' ->
        (subseq ((getwt W) ++ Wstart)  W')
          /\ get_smallvars ((getwt W) ++ Wstart) = (get_smallvars W')
          /\ (R' =  (getrd W) ++ Rstart).
    intros. move: H H0 => Hcceval Hwar.
    dependent induction Hwar.
    -  inversion Hcceval; subst. split; try split; try by []. exfalso. by apply H9.
    - inversion Hcceval; subst. move: (extract_write_svv H13 H0) => Heq.
      rewrite Heq. split; try split; try by [].
      inversion H13; subst; pose proof (read_deterministic H (RD H10));
        subst; split; reflexivity.
    -inversion Hcceval; subst. move: (extract_write_svnv H13 H) => Heq.
    rewrite Heq. split; try split; try by []. inversion H13; subst;
    pose proof (read_deterministic H0 (RD H10));
    subst; split; reflexivity. 
 - inversion Hcceval; subst. move: (extract_write_svnv H15 H0) => Heq.
    rewrite Heq. inversion H15; subst;
    move: (read_deterministic H (RD H12)) => Heq1; subst;
    split; try split; try by [].
 - inversion Hcceval; subst. move: (extract_write_svnv H14 H2) => Heq.
    rewrite Heq. inversion H14; subst;
    move: (read_deterministic H (RD H11)) => Heq1; subst;
                                              split; try split; try by [].
 
 - inversion Hcceval; subst; inversion H13; subst.
   split; try split. simpl.
   rewrite - cat1s. apply cat_subseq.
   rewrite sub1seq.
   destruct element as [a0 index0]. eapply gen_locs_works.
   apply H17. auto. Opaque get_smallvars. simpl.
   rewrite (sv_add_el W0 W0); try auto.
   symmetry. rewrite (sv_add_arr W0 W0 a); try auto.
   simpl.
   rewrite readobs_app_wvs. rewrite catA.
   move: (read_deterministic H (RD H15)) => Heq1.
   move: (read_deterministic H0 (RD H14)) => Heq2.
   by subst. 
 - inversion Hcceval; subst; inversion H14; subst.
   split; try split. simpl.
   rewrite - cat1s. apply cat_subseq.
   rewrite sub1seq.
   destruct element as [a0 index0]. eapply gen_locs_works.
   apply H18. auto.
   Opaque get_smallvars. simpl.
   rewrite (sv_add_el W0 W0); try auto.
   symmetry. rewrite (sv_add_arr W0 W0 a); try auto.
   simpl. rewrite readobs_app_wvs. rewrite catA.
   pose proof (read_deterministic H (RD H16)).
   pose proof (read_deterministic H0 (RD H15)).
   by subst. 
Qed.


Lemma agsv_war_bc {w W1 W2 R l W' R'}:
             WAR_ins w W1 R l W' R' ->
       (get_smallvars W2) = (get_smallvars W1) ->
       exists(W2': warvars), WAR_ins w W2 R l W2' R' /\
       (get_smallvars W2') = (get_smallvars W').
      
      intros. 
      inversion H; subst.
      - exists W2; split. eapply WAR_Skip. assumption.
      - exists W2. split; try assumption. eapply WAR_Vol; try assumption.
        by apply (agsv_war_h W' W2).
      - exists(inl x :: W2). split.
        eapply WAR_NoRd; try apply H1; try assumption. by apply sv_add_sv.
      - exists(inl x :: W2). split. eapply WAR_Checkpointed; try apply H0; try assumption.
        apply/ negP.
        apply (agsv_war_h W1 W2). assumption. by
            move/negP: H4. by apply sv_add_sv.
      - exists(inl x :: W2). split. eapply WAR_WT; try apply H0; try assumption.
        symmetry in H0.
        apply/ negPn.
        apply (contra (agsv_war_h W2 W1 x H0)). 
          by apply/negPn. by apply sv_add_sv.
      - exists(generate_locs a ++ W2). split.
        eapply WAR_NoRd_Arr. apply H1. apply H2. assumption.
        apply sv_add_arr.
        rewrite (sv_add_arr W1 W2 a); try by [].
      -exists(generate_locs a ++ W2). split.
       eapply WAR_Checkpointed_Arr; try apply H0; try apply H1; try assumption. 
        apply sv_add_arr.
        rewrite (sv_add_arr W1 W2 a); try by [].
Qed.

 Lemma agsv_war {w W1 W2 R c}:
       WARok w W1 R c ->
       (get_smallvars W2) = (get_smallvars W1) ->
       WARok w W2 R c. intros.
      move: W2 H0.  dependent induction H; intros; simpl.
      - move: (agsv_war_bc H H0) => [W2' Done]. eapply WAR_I. apply Done.
      - eapply WAR_CP; assumption.
      - move: (agsv_war_bc H H1) => [W2' [H21 H22] ].
        eapply WAR_Seq; try assumption.
        apply H21. by apply IHWARok.
     - eapply WAR_If. apply H. by apply IHWARok1. by apply IHWARok2.
Qed.


Lemma warok_partial:  forall{N0 N Nmid: nvmem} {V Vmid: vmem} {c cmid: command} {O: obseq} {W: the_write_stuff} {Wstart Rstart: warvars},
    cceval_w (N, V, c) O (Nmid, Vmid, cmid) W ->
    checkpoint \notin O ->
    WARok (getdomain N0) Wstart Rstart c ->
    WARok (getdomain N0) ((getwt W) ++ Wstart) ((getrd W) ++ Rstart) cmid.
    intros. move: H H0 H1 => Hcceval Ho Hwarok.
    dependent induction Hwarok; simpl.
    - apply cceval_skip in Hcceval. subst. eapply WAR_I. constructor.
    - inversion Hcceval; subst. discriminate Ho.
      exfalso. by apply (H8 w).
   - move: (war_cceval Hcceval H) => [Hsubseq [Hsmallvars Hr] ]. subst. apply cceval_steps in Hcceval. subst.  eapply agsv_war. apply Hwarok. assumption.
 - inversion Hcceval; subst; 
    pose proof (read_deterministic H (RD H10));
    subst; assumption.
Qed.

Lemma two_bcw {Ni Ni1 V V1 l c1 crem Nc O W} : all_diff_in_fww Ni V (l;;crem) Nc ->
                              cceval_w (Ni, V, Ins l) O (Ni1, V1, c1) W ->
                              exists(Nc1: nvmem), (cceval_w (Nc, V, Ins l) O (Nc1, V1, c1) W /\
                              forall(l: loc), l \in (getwt W) -> ((getmap Ni1) l = (getmap Nc1) l)).
      intros.
      move: (agreeonread_ins_w_l H H0) => agr.
      dependent induction H0; simpl in agr.
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

Lemma war_works_loc_c {N0 N Nend: nvmem} {V Vend: vmem} {c cend: command} {O: obseq} {W: the_write_stuff}
      {Wstart Rstart: warvars}:
    cceval_w (N, V, c) O (Nend, Vend, cend) W ->
    WARok (getdomain N0) Wstart Rstart c ->
    checkpoint \notin O ->
  forall (l: loc),
(l \notin (remove Rstart (getfstwt W)) -> 
 l \in (getwt W) ->
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
     subst.
     +  exfalso. apply (negNVandV x H0 H10).
     +
       rewrite mem_cat in H13.
         move / negP / norP : H13 => [Hre Hrs].
         rewrite mem_filter in H2.
         move/nandP: H2. => [contra | H2].
         rewrite Hrs in contra. discriminate contra.
         pose proof (negfwandw_means_r Hcceval H2 Hwt) as Hrd.
         
         simpl in Hrd.
         move: (read_deterministic H10 (RD H)) => Heq. subst.
         exfalso. move/negP : Hre. by apply.
     + 
        by left.
     + 
       by right.
     - 
       rewrite in_nil in H3.
       discriminate H3.
     - 
       remember H4 as Hwt. clear HeqHwt.
       simpl in H4.
       rewrite mem_seq1 in H4. move/ eqP : H4 => Heq. subst.
       inversion Hwarok; subst; inversion H8;
       subst. 
       + 
           remember (inr element) as l.
           destruct element as [a0 index].
     -
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
           + 
         destruct element.
             left. 
         apply (in_subseq H16 (gen_locs_works H2)).
- 
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
  forall (l: loc),
(l \notin (remove Rstart (getfstwt W)) -> 
 l \in (getwt W) ->
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


Lemma wts_cped_sv: forall{N0 N Nend: nvmem} {V Vend: vmem} {c cend: command} {O: obseq} {W: the_write_stuff}
                  {Wstart Rstart: warvars} {l: loc},
    trace_cs (N, V, c) (Nend, Vend, cend) O W ->
    WARok (getdomain N0) Wstart Rstart c ->
    checkpoint \notin O ->
    l \notin (getdomain N0) ->
    l \in (getwt W) -> 
    l \in (remove Rstart (getfstwt W)) 
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
  trace_cs (N, V, c) (Nmid, Vmid, cmid) O1 W1 ->
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

   Lemma warok_cp {N1 N2 V1 V2 c crem O W Wstart Rstart}
      {w0 w1: warvars}:
  WARok w0 Wstart Rstart c ->
  trace_cs (N1, V1, c) (N2, V2, incheckpoint w1;; crem) O W ->
  WARok w1 [::] [::] crem. intros Hwar T.
   move: N1 V1 N2 V2 O W T.
   dependent induction Hwar; subst; intros.
   2: {
     destruct (O == [::]) eqn: Hbool; move/ eqP: Hbool => Hbool. subst.
     move/empty_trace_cs1: T => [one two]. inversion one.
     subst. assumption.
     move: (single_step_alls_rev T Hbool). =>
 [ [ [nm vm] cm]
     [W1
        [Wrest
           [ O1
               [Hcceval
                  [Hsub Hw]
               ]
           ]
        ]
 ] ].
     move: (cceval_steps Hcceval) => one. subst.
     move: (single_step_alls T Hbool Hcceval). =>
                                               [Wrest0 [Orest [Trest [Hsubr Hwr] ] ] ].
     eapply IHHwar; try by []. apply Trest.
   }
   2: {
     destruct (O == [::]) eqn: Hbool; move/ eqP: Hbool => Hbool. subst.
     move/empty_trace_cs1: T => [one two]. inversion one.
     subst. inversion H. 
     move: (single_step_alls_rev T Hbool). =>
 [ [ [nm vm] cm]
     [W1
        [Wrest
           [ O1
               [Hcceval
                  [Hsub Hw]
               ]
           ]
        ]
 ] ].
     move: (cceval_steps Hcceval) => one. subst.
     move: (single_step_alls T Hbool Hcceval). =>
                                               [Wrest0 [Orest [Trest [Hsubr Hwr] ] ] ].
     eapply IHHwar; try by []. apply Trest.
   }
   2: {
suffices: O <> [::]. move => Hneq.
     move: (single_step_alls_rev T Hneq). =>
 [ [ [nm vm] cm]
     [W1
        [Wrest
           [ O1
               [Hcceval
                  [Hsub Hw]
               ]
           ]
        ]
 ] ].
     move: (single_step_alls T Hneq Hcceval). =>
                                              [Wrest0 [Orest [Trest [Hsubr Hwr] ] ] ].
     inversion Hcceval; subst;
       [eapply IHHwar1 | eapply IHHwar2]; try by []; apply Trest.
     intros contra. subst.
     move/ empty_trace_cs1: T => [one two]. inversion one.
   }
   move/ trace_skip1: T => [one | one]; inversion one.
   Qed.
