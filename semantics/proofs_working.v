Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Strings.String Program Logic.FunctionalExtensionality.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq fintype ssrnat ssrfun.
From TLC Require Import LibTactics LibLogic.
From Semantics Require Export programs semantics algorithms lemmas_1
lemmas_0 proofs_0 proofs. (*shouldn't have to import both of these*)
(*starting point in terms only of current mem so don't need to parameterize it,
 don't need to induct over length of starting trace!*)
Lemma sixteen: forall{Nstart N0 N1 Nend N2 : nvmem} {V V1 Vend: vmem}
                {c c1 cend: command}
                    {O Ostart: obseq} {W Wstart: the_write_stuff},
    trace_c (Nstart, V, c) (N1, V1, c1) Ostart Wstart -> (*initializes V1 as correct*) subset_nvm N0 Nstart ->
        trace_i ((N0, V, c), N1, V1, c1) ((N0, V, c), Nend, Vend, cend) O W -> cend <> (Ins inreboot) ->
        (checkpoint \notin O) ->
             (reboot \notin O) ->
             WARok (getdomain N0) [::] [::] c ->
             same_pt Nstart V c c1 N1 N2 ->
             checkpoint \notin Ostart
           -> exists(Nend2: nvmem),(trace_c (N2, V1, c1) (Nend2, Vend, cend) O W /\
             same_pt Nstart V c cend Nend Nend2).
      intros.
      dependent induction H1.
      (*empty trace case*)
      + exists N2. split. eapply CTrace_Empty.
        assumption.
        (*single intermittent step case*)
      + remember H1 as Hiceval.
        clear HeqHiceval.
        (*show arthur the ridiculous error message
         that i get if i take this out*)
        (*start here consider a different
         command type where the BC is all grouped
         together as one instruction
         i mean, if you wanted to do that you'd
         induct on c
         but i remember that being annoying for a different
         reason
if you induct on c you wont have info about how N gets updated which will break the existence
         see how you go with this and then try it*)
          pose proof (iceval_cceval1 Hiceval H2 H4) as Hcceval.
          pose proof (nineteen H6 Hcceval) as Hloceq.
(*for 20 you need an eeval*) 
         dependent induction H1; (*indict iceval*)
            try (pose proof (twenty H Hloceq) as Heval2);
          try (pose proof (twenty_arr H0 H Hloceq) as [ Heval20 Heval21]).
        - (*pf*) give_up. 
        - (*rb*) exfalso. move/negP :H4.
            by apply.
        - (*cp*) exfalso. move/negP: H3. by apply.
        - (*nv*) exists((updateNV_sv N2 x v)).
          pose proof (NV_Assign Heval2 H0 H1) as Hcceval2.
          (*volatile*)
          2: {
            exists(N2).
            pose proof (V_Assign Heval2 H0 H1) as Hcceval2.
            (*start here consider combining this with NV assign through function based on H0*)
            shelve. 
          }
          (*ask arthur there must be a better way
how to unfocus a goal before you are finished with it*)
          (*asgn_arr*)
          2: {
            exists(updateNV_arr N2 element a v). (*could definitely extract this given the cceval and N2*)
            pose proof (Assign_Arr Heval21 Heval20 H1 H2) as Hcceval2. 
            (*start here consider combining this with NV assign through function based on H0*)
            shelve. 
          }
          (*skip case*)
          2: {
            exists(N2).
            pose proof (Skip N2 Vend cend) as Hcceval2.
            (*start here consider combining this with NV assign through function based on H0*)
            shelve. 

          }
(*seq inductive iceval case*)
          2: {
            suffices: exists Nend2,
               trace_c (N2, V1, Ins l) (Nend2, Vend, cend)
                 [:: o] W /\
               same_pt Nstart V c cend Nend Nend2.
            - move => [Nend2 [Tcins Hsp] ]. exists Nend2. split.
            apply CTrace_Single. constructor; try assumption.
            apply (singletc_cceval Tcins).
              by []. assumption.
            shelve. 
          }
          split.
          (*try doing just the top part case by case and automating
           what's below; don't see any dependencies*)
            - by apply CTrace_Single.
            -
              (*showing
  same_pt (N0 U! updateNV_sv N1 x v) V c 
    (Ins skip) (updateNV_sv N1 x v)
    (updateNV_sv N2 x v)
               *)
(*prep as i use this in multiple goals generated
 by same_mem*)
              assert (checkpoint \notin Ostart ++ [:: RdObs r]) as Hcp.
              apply (introT negP).
              move => contra.
              rewrite mem_cat in contra.
              move/orP : contra => [contra1 | contra2].
              apply (elimT negP) in H9.
              (*ask arthur how is it that those switch*)
                by apply H9.
                rewrite mem_seq1 in contra2.
                  by move/eqP : contra2.
              inversion H8. subst.
              eapply same_mem; try auto.
              (*consider is there any point to the
               multistep part*)
            - (*showing
  trace_c (N0 U! updateNV_sv N1 x v, V, c)
    (updateNV_sv N1 x v, ?V1, Ins skip) 
    ?O1 ?W1
               *)
              (*NTS crem = skip*)
              pose proof (trace_stops T2) as Hrem.
              pose proof (trace_append T1 T2) as Tend.
              pose proof (and_or_elim Hrem H10).
              assert (~
        (crem = Ins (asgn_sv x e) /\
         (exists w crem2, crem = incheckpoint w;; crem2))).
              intros [contra1 [b1 [b2 contra2] ] ].
              subst. discriminate contra2.
              apply H15 in H16. subst.
              (*ask arthur what the hell is this*)
              (*make Hcceval into a continuous trace,
               combine it with H2*)
pose proof (trace_append H2 (CTrace_Single Hcceval)) as Tcs2e.
                assert (multi_step_i (N0, V, c, Nstart,
                                     V, c)
                                     (N0, V, c, (updateNV_sv N1 x v), Vend, Ins skip) (Ostart ++ [:: RdObs r])) as Ts2e.
pose proof (ctrace_itrace c Tcs2e).
exists (append_write Wstart
             ([:: inl x],
             readobs_wvs r,
             remove
               (readobs_wvs r)
               [:: inl x])).
eapply H16.
apply (trace_append H2 (CTrace_Single Hcceval)).
       (*showing
  trace_c (updateNV_sv N1 x v, Vend, Ins skip)
(?N2, ?V2, ?crem) ?O2 ?W2 *)
          apply CTrace_Empty. apply Hcp.
          auto.
     (*showing N1 =1 N2*)
        - intros l contra.
          remember contra as contra1. clear Heqcontra1.
          apply update_mask in contra.
          apply H14 in contra.
          remember T2 as T21. clear HeqT21.
          move/trace_stops: T21 => [c1 | c2]; subst.
          move/empty_trace_sc :T2 =>
          [b1 [b2 [b3 b4] ] ]. subst.
          simpl in contra.
          destruct contra as [c1 c2].
          exfalso. rewrite in_nil in c1.
            by move: c1.
            apply trace_ins1 in T2.
            inversion T2; subst.
            simpl in contra. move: contra => [c1 c2]. rewrite mem_seq1 in c1. move/ eqP :c1 => c1. subst.
            exfalso. apply contra1.
            apply same_update. simpl in contra.
            move: contra => [c1 c2]. rewrite in_nil in c1.
            discriminate c1. intros contra2. discriminate contra2.
(*need to add other cases for 16
 consider some function where it takes in a map and an instruction
 and returns the resulting map
 and then prove that this works with cceval
 could save automation?*)
Admitted.
            (*NV case done*)
            (*consider making a separate proof for the instruction
             case so you dont have to do this reasoning 500 times
             start here*)
          
(*start here you'd think there'd be some
               sort of reboots req for first trace in twelve00*)

           (*     pose proof (twelve00 Hm H3 H5
                           )
              apply (iTrace_Single Hiceval) .
(*ask arthur can i use exist in a function
 sort of way*)
              suffices: (trace_c updateNV_sv N1 x v, V, c)
              pose proof (single_step_all
                         (CTrace_Single Hcceval))
        (*kind of weird that the restarting actually takes
         2 steps with this RB step in the middle,
         maybe easier if we handled restarting in the base case?*)
        (*induct on instruction to get correct map*)
        induction l.
      - (*skip*) inversion H; subst. by exfalso.
      -
        exists((updateNV_sv N2 x v))
        (*apply 19*)*)


      (*ask arthur i want this enforced at the type level*)
    Lemma dom_eq: forall(N0 N1: nvmem),
        (getmap N0) =1 (getmap N1) ->
        N0 = N1.
      Admitted.

Lemma eleven_bc: forall{N0 N1 Nmid Nend N2: nvmem} {V Vmid Vend: vmem} {c cmid cend: command}
                  {O1 Orem: obseq} {W1 Wrem: the_write_stuff},
        (*need the N0 here cuz of same config*)
        trace_i ((N0, V, c), N1, V, c) ((N0, V, c), Nmid, Vmid, cmid) O1 W1 ->
        (checkpoint \notin O1) ->
        (reboot \notin O1) ->
             subset_nvm N0 N1 ->
             subset_nvm N0 N2 ->
             current_init_pt N0 V c N1 N1 N2 ->
             WARok (getdomain N0) [::] [::] c ->
             trace_i ((N0, V, c), Nmid, Vmid, cmid) ((N0, V, c), Nend, Vend, cend) Orem Wrem ->
             (* Sigma -> Sigma'
configs can always make progress assumption*)
             (checkpoint \notin Orem) ->
             (reboot \notin Orem) ->
             ((cend = Ins skip) \/ exists(w: warvars) (cend2: command), cend = (incheckpoint w);; cend2) ->
             (exists(sigma: context) (Wc:
                                            the_write_stuff),
                 trace_c (N2, V, c) sigma O1 Wc /\
                         (*write SETS have to be the same
                          but write lists do not,
                          can add that extra specificity
                          if I need it*)
             same_config N1 ((N0, V, c), Nmid, Vmid, cmid) (*Sigma ~ sigma*)
                         sigma /\
             trace_c sigma (Nend, Vend, cend) Orem Wrem (*sigma -> Sigma'-*)
             (*same obs, write as "intermittent" execution*)
             ).
  intros.
        suffices: exists(Nmid2: nvmem),
          (trace_c (N2, V, c) (Nmid2, Vmid, cmid) O1 W1 /\
           same_pt N1 V c cmid Nmid Nmid2).
      - move => [Nmid2 [Tc1 Hsp] ].
        exists (Nmid2, Vmid, cmid) W1. split.
        + assumption.
        + (*split.
           - constructor. assumption.*)
            (* destruct H8 as [H80 | H81].*)
           (*  subst.
             split.
             +*)
               assert (cend <> (Ins inreboot)) as Hcend.
               - intros contra. subst.
                 destruct H9 as [contra1 | [b1 [b2 contra2] ] ].
                 discriminate contra1.
                 discriminate contra2.
                 Check sixteen.

                 pose proof (itrace_ctrace H H1) as Tcs.
               destruct (sixteen Tcs H2 H6 Hcend H7 H8 H5 Hsp H0)
                   as [Nend2 [Tc2 Hspend] ].
               suffices: Nend = Nend2.
               move=> Heq. subst.
               split; try assumption; constructor; try assumption.
               - inversion Hspend. subst.
                 apply dom_eq.
             intros l.
             apply: eqP.
             apply: negPn.
             (*start here why didn't normal apply work*)
             apply (introT negP).
             move/ eqP => contra.
             apply H14 in contra.
             destruct contra as [contra0 [contra1 contra2] ].
             (*now showing that W2 is empty*)
               destruct H9 as [H81 | H82]; subst.
             pose proof (skiptrace_empty T2). subst.
             apply empty_trace in T2; auto. destruct T2 as [Heq1 Heq2]. subst.
             rewrite in_nil in contra0. discriminate contra0.
             destruct H82 as [w [cend2 Heqcend] ]. subst.
             pose proof (observe_checkpt T2) as
                 [contra3 | contra3].
             subst.
             apply empty_trace_sc in T2.
             destruct T2 as [blah [blah1 [blah2 blah3] ] ].
             subst.
             rewrite in_nil in contra0. discriminate contra0.
             by apply: (negP H13).
   - eapply sixteen; try eapply iTrace_Empty; try
        (*how is auto too stupid to solve this*)
                                                (by rewrite in_nil); try apply (CTrace_Empty (N1, V, c)); try
     (*start here learn the company coq keystrokes*)
     apply H2; try assumption. intros contra. subst.
     pose proof (observe_rb H6) as contra.
     destruct contra as [contra1 | contra2]; subst.
     destruct H9 as [contra1 | [b1 [b2 contra2] ] ].
     discriminate contra1. discriminate contra2.
     move/negP : H8.
     by apply.
     (* start here
pretty cool that this works given the theorem statement of
update_sub rewrite - {1} (update_sub H1).*)
     (*rewrite {1} (update_sub H2).*)
     eapply eight; try apply H2; try assumption.
     by rewrite in_nil.
     Qed.

      Lemma obseq_readobs: forall{O: obseq}
                            {N1 N2: nvmem}
                            {V1 V2: vmem}
                            {c1 c2: command}
                            {W: the_write_stuff},
trace_c (N1, V1, c1) (N2, V2, c2) O
        W ->
checkpoint \notin O ->
exists(o: readobs), O = [::RdObs o].
Admitted.

      Lemma can_make_progress: forall(N: nvmem) (V: vmem)
                                (c: command),
                                  exists(Nend: nvmem) (Vend: vmem)
                                   (cend: command)
                                   (O: obseq)
                                  (W: the_write_stuff),
                                    trace_c (N, V, c) (Nend, Vend, cend) O W /\ checkpoint \notin O /\
(cend = Ins skip \/
        (exists w cend2,
            cend = incheckpoint w;; cend2)).
        Admitted.

Lemma same_nearest_CP: forall{Ns Nend1 Nend2: nvmem} {Vs Vend1
                                            Vend2: vmem}
                {c cend1 cend2: command} {O1 O2: obseq}
                {W1 W2: the_write_stuff},
    trace_c (Ns, Vs, c) (Nend1, Vend1, cend1) O1 W1 ->
    checkpoint \notin O1 ->
    (cend1 = Ins skip \/
     (exists w1 crem1, cend1 = incheckpoint w1;; crem1))
      (*start here make that into a prop*) ->
    trace_c (Ns, Vs, c) (Nend2, Vend2, cend2) O2 W2 ->
    checkpoint \notin O2 -> 
    (cend2 = Ins skip \/
     (exists w2 crem2, cend2 = incheckpoint w2;; crem2))
   -> cend1 = cend2.
Admitted.


Lemma cp_const {N01 N02 V01 V02 c01 c02 N1 N2 V1 V2 c1 c2 O W} :
  trace_i ((N01, V01, c01), N1, V1, c1) ((N02, V02, c02), N2, V2, c2) O W ->
  checkpoint \notin O ->
  N01 = N02 /\ V01 = V02 /\ c01 = c02. Admitted.

Inductive same_mem11: nvmem -> Prop :=
            Same_Mem11: forall {N0 Nstart Nvar Nc V c N Nend Vend cend O W},
              current_init_pt N0 V c Nstart Nvar Nc ->
              trace_i ((N0, V, c), N, V, c) ((N0, V, c), Nend, Vend, cend) O W ->
              Nvar = N -> same_mem11 N.

    Lemma eleven: forall{N0 N1 Nmid Nend N2 Nstart: nvmem} {V Vmid Vend: vmem} {c cmid cend: command}
                   {O1 Orem: obseq} {W1 Wrem: the_write_stuff},
                   trace_i ((N0, V, c), N1, V, c) ((N0, V, c), Nmid, Vmid, cmid) O1 W1 ->
          current_init_pt N0 V c N1 N1 N2 ->
             (checkpoint \notin O1) ->
             subset_nvm N0 N1 ->
             subset_nvm N0 N2 ->
             WARok (getdomain N0) [::] [::] c ->
             trace_i ((N0, V, c), Nmid, Vmid, cmid) ((N0, V, c), Nend, Vend, cend) Orem Wrem ->
             (* Sigma -> Sigma'
configs can always make progress assumption*)
             (checkpoint \notin Orem) ->
             (reboot \notin Orem) ->
             ((cend = Ins skip) \/ exists(w: warvars) (cend2: command), cend = (incheckpoint w);; cend2) ->
             (exists(O2: obseq) (sigma: context) (Wc:
                                            the_write_stuff),
                 trace_c (N2, V, c) sigma O2 Wc /\
                 checkpoint \notin O2 /\ (*cuz its taking
                                         the same path as N1 to
                                         cmid*)
                 (*write SETS have to be the same
                          but write lists do not,
                          can add that extra specificity
                          if I need it*)
             same_config N1 ((N0, V, c), Nmid, Vmid, cmid) (*Sigma ~ sigma*)
                         sigma /\
             trace_c sigma (Nend, Vend, cend) Orem Wrem  /\ (*sigma -> Sigma'-*)
             (*same obs, write as "intermittent" execution*)
             (O1 ++ Orem <=m O2 ++ Orem)).
      intros.
      move: H0 H1 H2 H3 H4 H5 H6 H7 H8.
      move: Wrem Orem cend Vend Nend N2.
      apply trace_convert in H.
      dependent induction H; intros.
      2: {
        suffices: (exists O3 sigma Wc,
               trace_c (N2, V, c) sigma O3 Wc /\
                      is_true (checkpoint \notin O3) /\
               same_config
                 N1 (N0, V, c, Nmid, Vmid, cmid)
                 sigma /\
               trace_c sigma (Nend, Vend, cend)
                 Orem Wrem /\
               (O2 ++ Orem <=m O3 ++ Orem)).
        (*ask arthur how does it let me
         get away with Nmid when it's not in the context*)
      - intros [O3 [sigma [Wc [Hc1 [Hc2 [Hc3 [ Hc4 Hc5 ]
                   ] ] ] ] ] ].
      exists O3, sigma, Wc.
      repeat (try split); try assumption.
      destruct3 sigma Ns Vs cs.
      pose proof (obseq_readobs Hc1 Hc2) as [o3 Ho3].
      pose proof (obseq_readobs Hc4 H9) as [o4 Ho4].
      pose proof (obseq_readobs H H1) as [o1 Ho1].
      (*dont think obseq_readobs is actually true
       because the trace doesnt append consecutive read observations together*
      why do i even need the above
       to get it to match the structure of RB_IND w a singleton on the
       right. if i didnt bunch readobs up into one list, wouldnt need*)
      subst.
      repeat rewrite - catA.
      apply RB_Ind; try assumption.
      rewrite mem_cat negb_orb. apply (introT andP). split; try assumption.
      (*2nd goal should come out of Hc5*)
      Check eleven_bc.
      assert (reboot \notin [:: RdObs o1]) as Ho1.
      apply (introT negP).
      rewrite mem_seq1. move/eqP => contra. discriminate contra.
      pose proof (can_make_progress Nmid0 Vmid0 cmid0) as
          [Nend1 [Vend1 [cend1 [Oend1 [Wend1 [Tendc [Hcend1
                 Hcend2]  ] ] ] ] ] ].
      pose proof (obseq_readobs Tendc Hcend1) as [oend Hoend].
      subst.
      assert (reboot \notin [:: RdObs oend]) as Hoend.
      apply (introT negP).
      rewrite mem_seq1. move/eqP => contra. discriminate contra.
      Check eleven_bc.
      rewrite mem_cat negb_orb in H4.
      move/ andP : H4 => [H31 H32].
      Check eleven_bc.
      pose proof (iTrace_Cont N0 V c H H31) as Hi.
      pose proof (iTrace_Cont N0 V c Tendc Hcend1) as Tendci.
      (*consider having two directions for trace_Convertso that
       you can combine this*)
      apply trace_convert in Hi. apply trace_convert in Tendci.
      (*prop which forces N1 from
current init and Ns2 to be the same
       *)
      Check eleven_bc.
pose proof (eleven_bc Hi H31 Ho1 H5 H6 H3 H7 
                           Tendci 
                            Hcend1 Hoend
                            Hcend2)
      as [ [ [Ns1 Vs1] cs1]  [Wc1 [Hc11 [Hc21 Hc31]
         ] ] ].
      pose proof (trace_append Hc11 Hc31) as Hc2end1.
      pose proof (trace_append Hc1 Hc4) as Hc2end.
      assert (checkpoint \notin [:: RdObs o3] ++ [:: RdObs o4])
           (*start here it does the weird search thing with
            2nd occurrence as well! with /Obs it's fine!
            *)
        as Hcp1.
      apply (introT negP). intros contra.
      rewrite mem_cat in contra.
      move/orP : contra => [contra1 | contra2].
      move/negP : Hc2. by apply.
      move/negP : H9. by apply.
      assert (checkpoint \notin ([:: RdObs o1] ++ [:: RdObs oend]))
        as Hcp2.
      apply (introT negP). intros contra.
      rewrite mem_cat in contra.
      move/orP : contra => [contra1 | contra2].
      move/negP : H31. by apply.
      move/negP : Hcend1. by apply.
      pose proof (same_nearest_CP Hc2end Hcp1 H11 Hc2end1 Hcp2 Hcend2). subst.
      apply (ctrace_deterministic Hc2end1) in Hc2end.
      destruct Hc2end as [e1 [e2 [e3 e4] ] ]. subst.
      rewrite - e3. repeat constructor.
      - eapply IHtrace_i1; try reflexivity. try assumption.
        apply sub_update.
        Check twelve.
        (*might make my life easier to have 12 take in a continuous trace*)
        pose proof (iTrace_Cont N0 V c H H1) as T12.
        apply trace_convert in T12.
        eapply (twelve T12 H1
                       (neg_observe_rb H)
                       H7 H6 H4). }
      (*BC*)
      Check eleven_bc.
      Check ctrace_itrace.
        (*i think this is 12*)

      (*split up Hc2end
Hc51 should give it
       *)



     (* ask arthur.. seriously?
pose proof (and4 Hc1 Hc2 Hc3 Hc4) as Hc.
Record types where each one of those guys is a field
      *)





 (*   Lemma eleven1: forall{N0 N1 Nmid Nend N2: nvmem} {V Vmid Vend: vmem} {c cmid cend: command}
                   {O1 Orem: obseq} {W1 Wrem: the_write_stuff},
        trace_i ((N0, V, c), N1, V, c) ((N0, V, c), Nmid, Vmid, cmid) O1 W1 ->
             (checkpoint \notin O1) ->
             subset_nvm N0 N1 ->
             subset_nvm N0 N2 ->
             current_init_pt N0 V c N1 N1 N2 ->
             WARok (getdomain N0) [::] [::] c ->
             trace_i ((N0, V, c), Nmid, Vmid, cmid) ((N0, V, c), Nend, Vend, cend) Orem Wrem ->
             (* Sigma -> Sigma'
configs can always make progress assumption*)
             (checkpoint \notin Orem) ->
             (reboot \notin Orem) ->
             ((cend = Ins skip) \/ exists(w: warvars) (cend2: command), cend = (incheckpoint w);; cend2) ->
             (exists(O2: obseq) (sigma: context) (Wc:
                                            the_write_stuff),
                 trace_c (N2, V, c) sigma O2 Wc /\
                         (*write SETS have to be the same
                          but write lists do not,
                          can add that extra specificity
                          if I need it*)
             same_config ((N0, V, c), Nmid, Vmid, cmid) (*Sigma ~ sigma*)
                         sigma /\
             trace_c sigma (Nend, Vend, cend) Orem Wrem  /\ (*sigma -> Sigma'-*)
             (*same obs, write as "intermittent" execution*)
             O1 ++ Orem <= O2 ++ Orem).
      intros.
      (*inducting on reboots in start => Sigma*)
      + dependent induction H using reboot_ind.
        (*ask arthur bad induction principl here ):*)
        destruct ((count_reboots H) == O) eqn: BC.
        move/ eqP / count_memPn : BC => BC.
        (*base case*)
      +
        suffices: exists(Nmid2: nvmem),
          (trace_c (N2, V, c) (Nmid2, Vmid, cmid) O1 W1 /\
           same_pt (N0 U! Nmid) V c cmid Nmid Nmid2).
      - move => [Nmid2 [Tc1 Hsp] ].
        exists O1 (Nmid2, Vmid, cmid) W1. split.
        + assumption.
        + split.
           - constructor. assumption.
           - (*trying to use 16 instead of 17*)
            (* destruct H8 as [H80 | H81].*)
             subst.
             split.
             +
               assert (cend <> (Ins inreboot)) as Hcend.
               - intros contra. subst.
                 destruct H8 as [contra1 | [b1 [b2 contra2] ] ].
                 discriminate contra1.
                 discriminate contra2.
                 Check sixteen.
               destruct (sixteen H5 Hcend H6 H7 H4 Hsp)
                 as [Nend2 [Tc2 Hspend] ].
               suffices: Nend = Nend2.
               move=> Heq. subst. assumption.
           - inversion Hspend. subst.
             apply dom_eq.
             intros l.
             apply: eqP.
             apply: negPn.
             (*start here why didn't normal apply work*)
             apply (introT negP).
             move/ eqP => contra.
             apply H14 in contra.
             destruct contra as [contra0 [contra1 contra2] ].
             (*now showing that W2 is empty*)
               destruct H8 as [H81 | H82]; subst.
             pose proof (skiptrace_empty T2). subst.
             apply empty_trace in T2; auto. destruct T2 as [Heq1 Heq2]. subst.
             (*ask arthur how the above works with applying it
              for you sort of*)
             rewrite in_nil in contra0. discriminate contra0.
             destruct H82 as [w [cend2 Heqcend] ]. subst.
             pose proof (observe_checkpt T2) as
                 [contra3 | contra3].
             subst.
             apply empty_trace_sc in T2.
             destruct T2 as [blah [blah1 [blah2 blah3] ] ].
             subst.
             rewrite in_nil in contra0. discriminate contra0.
               by apply: (negP H13).
      + exists (size (O1 ++ Orem)). rewrite* take_size.
   - eapply sixteen; try eapply iTrace_Empty; try
        (*how is auto too stupid to solve this*)
                                                (by rewrite in_nil); try assumption. apply H. intros contra. subst.
     pose proof (observe_rb H5) as contra.
     destruct contra as [contra1 | contra2]; subst.
     destruct H8 as [contra1 | [b1 [b2 contra2] ] ].
     discriminate contra1. discriminate contra2.
     move/negP : H7.
     by apply.
     (* start here
pretty cool that this works given the theorem statement of
update_sub rewrite - {1} (update_sub H1).*)
     rewrite {1} (update_sub H1).
     eapply eight; try apply H1; try assumption.
(*IH is NOT general enough*)
     Lemma split_rb: forall{N0, N1, Nend: nvmem}
                      {V}

     (*base case done!*)

     
        
             destruct H10 as [H100 | H101].
           - (*both skip case*)
             pose proof (skiptrace_empty T2). subst.
             destruct (empty_trace T2); auto. subst.

             destruct H82 as [w [cend2 Hcendeq] ].
             subst.
             pose proof (observe_checkpt T2) as
                 [contra3 | contra3].
             discriminate contra3.
             move/ negP : H13. by apply.
             pose proof (skiptrace_empty T2). subst.
             apply empty_trace in T2. destruct T2 as [Heq1 Heq2].
             subst. rewrite in+nil in contra
               in_nil in contra0.
             discriminate contra0.
             inversion H8.

             apply: negP.
             apply negbT.
             apply: negP.
             (*should be a way to combine those two start here*)
              introT negPn (elimT eqP)
             extensionality.
ose proof (eight H1 H2 H3) as Height.
               Check sixteen.
               inversion Hsp. subst.
               Check itrace_ctrace.
               pose proof (itrace_ctrace H5 H7) as Tc3.
               destruct (ctrace_deterministic )
               ctrace_det
               (*worry about H11 in a second*)
               suffices: Nend = Nend2.
               move => Heq. subst. assumption.
               inversion Hspend. subst.
               destruct H8 as [H81 | H82].
               destruct H10 as [H101 | H102].
               subst.
(*wiggle with samept and the fact that cend
 is \/ by H8*)


                     iceval_w ((N0, V, c), N1, V, c) O
             ((N0, V, c), N1', V', c') W ->
             (reboot \notin O) ->
             WARok (getdomain N0) [::] [::] c ->
             current_init_pt N0 V c N1 N1 N2 ->
             current_init_pt N0 V c (N0 U! N1') (N0 U! N1')*)

Implicit Types N: nvmem. Implicit Types V: vmem.
Implicit Types O: obseq.
Implicit Types c: command.
Implicit Types W: the_write_stuff.
Implicit Types x: smallvar.
(*start here should be a way to stack these*)

Open Scope type_scope.
