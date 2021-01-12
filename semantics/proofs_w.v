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

    Lemma agreeonread_ins_w: forall{N Nend N2: nvmem} {V Vend: vmem}
                        {l: instruction} {crem c1: command}
                   {O : obseq} {W: the_write_stuff},
  all_diff_in_fww N V (l;;crem) N2 ->
             cceval_w (N2, V, Ins l) O (Nend, Vend, c1) W ->
            ( forall(z: loc), z \in (getrd W) -> (*z was read immediately cuz trace is only 1
                                thing long*)
                   (getmap N2) z = (getmap N) z). (*since z isnt in FW of trace from Ins l to skip*)
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
        rewrite sub1seq in Hsubseq. move/negP : H2. by apply.
        inversion H0; subst.
        move: (cceval_agr H0 H12) => Heqrd.
        rewrite Heqrd in Hread.
        move: (fw_nin_r_c z H12 Hread) => Hfw.
        rewrite mem_cat in contra.
        move/orP : contra => [contra1 | contra2].
        rewrite mem_filter in contra1.
        move/ andP : contra1  => [one two].
        move/negP : one. by apply.
        move/ mem_filter: contra.
        rewrite Hread.
        unfold append_write in H3.
        simpl in H3. 
    Admitted.

        destruct W as [ [w r ] fw].
        destruct W1 as [ [w1 r1 ] fw1].
        destruct Wrest as [ [wrem rrem ] fwrem].

 Lemma agreeonread_w: forall{N Nend N2: nvmem} {V Vend: vmem}
                        {c c1: command}
                   {O : obseq} {W: the_write_stuff},
  all_diff_in_fww N V c N2 ->
             cceval_w (N2, V, c) O (Nend, Vend, c1) W ->
            ( forall(z: loc), z \in (getrd W) -> (*z was read immediately cuz trace is only 1
                                thing long*)
                   (getmap N2) z = (getmap N) z). (*since z isnt in FW of trace from Ins l to skip*)
 Admitted.

 Lemma same_com_hcbc {N N1 Nend1 V V1 l crem O W c1} : all_diff_in_fww N V (l;;crem) N1 ->
                              cceval_w (N1, V, Ins l) O (Nend1, V1, c1) W ->
                              exists(Nend: nvmem), (cceval_w (N, V, Ins l) O (Nend, V1, c1) W) /\
 forall(l: loc), l \in (getwt W) -> ((getmap Nend) l = (getmap Nend1) l).
   intros Hdiff Hcceval1.
move: (agreeonread_ins_w Hdiff Hcceval1) => agr.
      dependent induction Hcceval1; simpl in agr.
    (*  - exists Nc. split. apply CheckPoint. move => l contra.
        rewrite in_nil in contra. by exfalso.*)
      - exists (updateNV_sv N x v). split. apply NV_Assign; try assumption.
        eapply agr_imp_age; try apply H; try assumption.
        simpl. intros l Hin. rewrite mem_seq1 in Hin.
        move/ eqP : Hin => Hin. subst.
        destruct N as [Nmap ND].
        destruct N1 as [N1map N1D].
        unfold updateNV_sv. unfold updatemap. simpl.
        remember (inl x) as xloc.
        suffices: (if xloc == xloc then v else Nmap xloc) = v /\
                  (if xloc == xloc then v else N1map xloc) = v.
        move => [one two]. by rewrite one two.
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
          by rewrite one two. 
          intros. split; by apply ifT.
          Qed.
      (*  unfold updatemap.
        suffices: 
          ((if inr el == inr element then v else Nmap (inr el)) =
           Nmap (inr el) /\
           (if inr el == inr element then v else N1map (inr el)) = N1map (inr el)).
        move => annoying.
        move: (annoying loc_eqtype loc_eqtype) => [one two]. rewrite one two.
        inversion Hdiff; subst.
        apply (H4 el).
        intros. split; apply ifF;
        move/eqP: (negbT Hbool) => Hneq;
        apply negbTE;
        apply/eqP; intros contra; inversion contra; subst;
          by apply Hneq.
Qed.*)

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
  - move: (same_com_hcbc (add_skip_ins Hdiff) Hcceval1). => [Nend [Hcceval Hloc] ].
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
         + move: (same_com_hcbc Hdiff H10). => [Nend [ Hcceval Hloc] ].
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
      by [].
      (*intros l0 contra. exfalso. by apply contra.*)
      intros l0. apply/ eqP /negPn /negP. intros contra.
      move/ eqPn / (H0 l0) : contra.
      by rewrite in_nil. auto.
       - move/ negbT / eqP : Hbool => Hneq.
         suffices: cceval_w (N, V, l;;c1) [:: o] (Nend, V1, c1) W.
         move => Hccevalbig.
move: (single_step_alls T Hneq Hccevalbig). => [Wrest [Orest
                                                     [Trest
                                [Hsubseq Hwrite] ] ] ].
       econstructor; try apply Trest; try assumption.
       apply/negP. intros contra.
       apply/negP / negPn: H.
       apply (in_subseq Hsubseq contra).
       (*intros. destruct ((inr el) \in (getwt W)) eqn: Hbool.
         by apply Hloc in Hbool.
       move : (update_one_contra (inr el) Hcceval) => Ho2ni.
       move : (update_one_contra (inr el) Hcceval1) => Ho2nc.
       move/ negbT : Hbool => Hbooli.
       remember Hbooli as Hboolc. clear HeqHboolc.
       apply Ho2ni in Hbooli.
       apply Ho2nc in Hboolc.
       suffices: getmap N (inr el) = getmap N1 (inr el).
       intros Heq3. symmetry in Hbooli.
         by move: (trans_eq (trans_eq Hbooli Heq3) Hboolc).
         apply/eqP/ negPn/ negP. move/eqP => contra.
           by apply contra.*)
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
      suffices: (getmap N2) =1 (getmap Nend2). move/hack => H500. subst. split; try assumption.
      econstructor; try apply CsTrace_Empty; try assumption.
      intros l0. apply/ eqP /negPn /negP. intros contra.
      move/ eqPn / (H0 l0) : contra.
      by rewrite in_nil. auto.
          - move/ negbT / eqP : Hbool => Hneq.
            move: (agreeonread_w Hdiff Hcceval1) => agr.
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
       apply/negP.
       move/(in_subseq Hsubseq) => contra. move/negP: H.
         by apply.
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
      suffices: (getmap N2) =1 (getmap Nend2). move/hack => H500. subst. split; try assumption.
      econstructor; try apply CsTrace_Empty; try assumption.
      intros l0. apply/ eqP /negPn /negP. intros contra.
      move/ eqPn / (H0 l0) : contra.
      by rewrite in_nil. auto.
          - move/ negbT / eqP : Hbool => Hneq.
            move: (agreeonread_w Hdiff Hcceval1) => agr.
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
       apply/negP.
       move/(in_subseq Hsubseq) => contra. move/negP: H.
         by apply.
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

Fixpoint get_smallvars (w: warvars) :=
  filter (fun v =>
          match v with
            (inl _) => true
          | (inr _) => false
          end) w.

  Lemma get_sv_works: forall (w1: warvars) (x: smallvar),
    (inl x \in w1) <->
    (inl x \in (get_smallvars w1)). Admitted.

        Lemma agsv_war_h : forall(w1 w2: warvars) (x: smallvar),
            get_smallvars w2 = get_smallvars w1 ->
            inl x \notin w1 -> inl x \notin w2.
          Admitted.

        Lemma sv_add_sv: forall(w1 w2 :warvars) (x: smallvar),
            (get_smallvars w1) = (get_smallvars w2) ->
            (get_smallvars ((inl x) :: w1) = get_smallvars ((inl x) :: w2)).
        Admitted.

        Lemma sv_add_el:forall(w1 w2 :warvars) (el: el_loc),
            (get_smallvars w1) = (get_smallvars w2) ->
            (get_smallvars ((inr el) :: w1) =
             get_smallvars w2).
Admitted.

        Lemma sv_add_arr: forall(w1 w2 :warvars) (a: array),
            (get_smallvars w1) = (get_smallvars w2) ->
            (get_smallvars ((generate_locs a) ++ w1) =
             (get_smallvars w2)).
          Admitted.

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
    - (*skip case*) inversion Hcceval; subst. split; try split; try by []. exfalso. by apply H9.
    - inversion Hcceval; subst. move: (extract_write_svv H13 H0) => Heq.
      rewrite Heq. split; try split; try by [].
      inversion H13; subst; pose proof (read_deterministic H (RD H10));
    subst; split; reflexivity. (*vol case*)
 -inversion Hcceval; subst. move: (extract_write_svnv H13 H) => Heq.
    rewrite Heq. split; try split; try by []. inversion H13; subst;
    pose proof (read_deterministic H0 (RD H10));
    subst; split; reflexivity. (*CP case*)
 - inversion Hcceval; subst. move: (extract_write_svnv H15 H0) => Heq.
    rewrite Heq. inversion H15; subst;
    move: (read_deterministic H (RD H12)) => Heq1; subst;
    split; try split; try by [].
 - inversion Hcceval; subst. move: (extract_write_svnv H14 H2) => Heq.
    rewrite Heq. inversion H14; subst;
    move: (read_deterministic H (RD H11)) => Heq1; subst;
                                              split; try split; try by [].
 
 - (*nrd arr case*) inversion Hcceval; subst; inversion H13; subst.
   split; try split. simpl.
   rewrite - cat1s. apply cat_subseq.
   rewrite sub1seq.
   destruct element as [a0 index0]. eapply gen_locs_works.
   apply H16. auto. Opaque get_smallvars. simpl.
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
   apply H17. auto.
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

