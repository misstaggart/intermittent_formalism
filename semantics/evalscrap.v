(*old 1st IS*)
  + assert (all_diff_in_fw Ni V01 c01 (N01 U! Nmid)) as Hdiffrb.
    - inversion H7. subst.  econstructor; try apply T; try assumption.
    move => el. apply/ eqP / negPn/ negP => contra.
   apply update_diff in contra. destruct contra as [ [con11 con12] | [con21 con22] ].
   apply con11. apply (H4 (inr el) con12).
   move: (trace_diff H con21) => Hdiff.
   move/negP :(wts_cped_arr H H3 H1 con22). by apply.
   move => l. move/eqP/update_diff => [ [diff11 diff12] | [diff21 diff22] ]. case diff11. apply (H4 l diff12).
   move: (trace_diff H diff21) => Hdiff.
   (*start here clean up repeated work in above*)
   move: (wts_cped_sv H H3 H1 diff22 Hdiff)  => [good | bad].
   rewrite/remove filter_predT in good.
   apply (fw_gets_bigger H H1 T H9 good).
   rewrite in_nil in bad. by discriminate bad.
   suffices:
               exists Oc Oendc Nc1 Wc Wendc,
  trace_cs (Nc, V01, c01) (Nc1, V1, c1) Oc Wc /\
  all_diff_in_fw Ni1 V1 c1 Nc1 /\
  (O2 ++ Oend <=f Oc ++ Oendc) /\
  trace_cs (Nc1, V1, c1) (Nend, Vend, cend) Oendc Wendc.
   intros [Oc [Oendc [Nc1 [Wc [Wendc
                                 [ass1
                                    [ass2
                                       [ass3 ass4] ] ] ] ] ] ] ].
   exists Oc Oendc Nc1 Wc Wendc.
   repeat split; try assumption.
   apply CP_Base.
   rewrite- catA.
   rewrite - catA.
    assert (checkpoint \notin Oc ++ Oendc).
    move: (frag_to_seq ass3) => Hannoying.
    apply no_CP_in_seq in Hannoying.
    move: Hannoying => [Ha1 Ha2].
    apply Ha2.
    rewrite mem_cat.
      by apply/ norP.
   apply RB_Ind; try assumption.
   apply (neg_observe_rb H).
   rewrite mem_cat; apply/ norP; split.
    apply (neg_observe_rb ass1).
    apply (neg_observe_rb ass4).
    rewrite mem_cat.
      by apply/ norP.
      move: (three_bc H7 H H1) => [Nc3 [threetrace whatever] ].
      move: (append_c ass1 ass4) => bigtrace.
      apply (ctrace_det_obs threetrace H1 bigtrace); try assumption.
      apply frag_to_seq; try assumption.
      rewrite mem_cat. by apply/ norP.
                               
   eapply IHtrace_i1; try reflexivity; try assumption.
   apply sub_update. apply (all_diff_in_fw_trans (all_diff_in_fw_sym Hdiffrb) H7).





(*Old 2nd IS*)
remember ((incheckpoint w);;crem) as ccp.
        suffices: (exists Oc Oendc Nc1 Wc
                 Wendc Nc1end Vc1end cend,
                 trace_cs (Nc, V, c)
                          (Nc1, Vmid, ccp) Oc Wc /\
                 all_diff_in_fw Nmid Vmid ccp Nc1 /\
                 trace_cs (Nc1, Vmid, crem)
                   (Nc1end, Vc1end, cend) Oendc
                   Wendc /\ checkpoint \notin Oendc /\ end_com cend
                  ).
    - move => [Oc1 [Oendc1 [Nc1 [Wc1 [Wendc1 [ Nc1end [ Vc1end
            [ ccend [H11 [H12 [H13 [H14 H15] ] ] ] ] ] ] ] ] ] ] ]. subst.
      assert (WARok (getdomain (Nc1 |! w)) [::] [::] crem) as Hwarok2.
      destruct Nc1 as [mc1 dc1]. rewrite/getdomain. simpl.
      apply (warok_cp H1 H11). 
      move: (trace_converge H12) => Heq. subst.
      suffices: (
                 exists Oc2 Oendc2 Nc2 Wc2 Wendc2,
                   trace_cs (Nc1, Vmid, crem)
                            (Nc2, V1, c1) Oc2 Wc2 /\
                 all_diff_in_fw Ni1 V1 c1 Nc2 /\
                 trace_cs (Nc2, V1, c1) 
                   (Nend, Vend, cend) Oendc2 Wendc2
                ).
      move => [Oc2 [Oendc2 [Nc2 [Wc2 [Wendc2 [H21 [H22 H23] ] ] ] ] ] ].
      (*consider: maybe your type should just split by reboots
       rather than checkpoints*)
     - move: (append_cps H11 H21) => T1.
      exists (Oc1 ++ Oc2) Oendc2 Nc2 (append_write Wc1 Wc2) Wendc2.
      repeat split; try assumption.
      eapply IHtrace_i1_2; try reflexivity; try assumption;
      try apply sub_restrict.
      apply (adif_refl H13 H15 H14).
     -
       Check trace_append_ic.
       move: (trace_append_ic H0_0 H3) => [Nc1endi [Vc1endi [cmend Tendi] ] ].
       Check threeIS1.
       move: (threeIS1 H0 H0_ H1 H2  H) => [Oc [Nc1 [Wc [T1 Hdiff] ] ] ].
       move: (exist_endcom Tendi H4) => [Oendc0 [Wendc0 [Nc1end0 [Vc1end
                                                           [cend0 [Tend [Hendcom Hoendc] ] ] ] ] ] ].
       Check same_comi.
assert (WARok (getdomain (Nc1 |! w)) [::] [::] crem) as Hwarok2.
      destruct Nc1 as [mc1 dc1]. rewrite/getdomain. simpl.
      subst.
      move: (same_comi H1 H2 H0_ H) => [Nend1 [Oc1 [Wc1 [Tc1 Hoc1] ] ] ].
      apply (warok_cp H1 Tc1).
      Check same_comi. subst.
       apply trace_converge in Hdiff. subst.
       move: (same_comi Hwarok2 (sub_restrict Nc1 w) Tend Hoendc) =>
      [Nc1end [Oendc [Wendc [Tendc Hcpoendc] ] ] ].                                                            
       exists Oc Oendc Nc1 Wc Wendc Nc1end. exists Vc1end cend0. subst.
       repeat split; try assumption. 
       econstructor; try eapply CsTrace_Empty; auto. right.
       exists crem w. by [].



(**)
