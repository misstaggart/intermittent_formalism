Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Strings.String Program Logic.FunctionalExtensionality.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq fintype ssrnat ssrfun.
From TLC Require Import LibTactics LibLogic.
From Semantics Require Export programs semantics algorithms lemmas_1
     lemmas_0 proofs_0. (*shouldn't have to import both of these*)

Implicit Types N: nvmem. Implicit Types V: vmem.
Implicit Types O: obseq.
Implicit Types c: command.
Implicit Types W: the_write_stuff.
Implicit Types x: smallvar.
(*actually ask arthur about that thing with the quantifer
 as against the implication*)

Definition end_com c := c = Ins skip \/ exists(crem: command)(w: warvars), c= (incheckpoint w);; crem.

(*Definition nvm_eq N1 N2 := subseq (getdomain N1) (getdomain N2) /\
                           subseq (getdomain N2) (getdomain N1).

Lemma hacky_nvm_eq N1 N2 : nvm_eq N1 N2 <-> (getdomain N1) = (getdomain N2).
Admitted.*)

Definition nvmem_eq N1 N2 := (getmap N1) =1 (getmap N2).

(*why do you include the volatile memory
 maybe to make the traces more tractable
 leave it in for now, can always take it out*)
Inductive all_diff_in_fw: nvmem -> vmem -> command -> nvmem -> Prop :=
  Diff_in_FW: forall{N1 V1 c1 N2 V2 c2 N1c O W} (T: trace_cs (N1, V1, c1) (N2, V2, c2) O W),
    end_com c2 -> checkpoint \notin O -> (*c2 is nearest checkpoint or termination*)
  (*  (getdomain N1) = (getdomain N1c) -> alternatively
                                       could check N2 domain as well instead of this
 not even clear why i need the domains                                    
   *)
   (forall(el: el_loc), ((getmap N1) (inr el)) = ((getmap N1c) (inr el))) ->
( forall(l: loc ), ((getmap N1) l <> (getmap N1c) l) -> (l \in getfstwt W))
-> all_diff_in_fw N1 V1 c1 N1c.

Lemma two {Ni Ni1 V V1 c c1 Nc O W} : all_diff_in_fw Ni V c Nc ->
                              cceval_w (Ni, V, c) O (Ni1, V1, c1) W ->
                              exists(Nc1: nvmem), (cceval_w (Nc, V, c) O (Nc1, V1, c1) W /\
                              forall(l: loc), l \in (getwt W) -> ((getmap Ni1) l = (getmap Nc1) l)).
Admitted.

Lemma exist_endcom {N0 V0 c0 N01 V01 c01 N V c N1 V1 O W cend}:
  trace_i1 ((N0, V0, c0), N, V, c) ((N01, V01, c01), N1, V1, cend) O W ->
  end_com cend ->
  (exists(Osmall: obseq) (Wsmall: the_write_stuff) (N2: nvmem) (V2: vmem) (c2: command),
    trace_i1 ((N0, V0, c0), N, V, c) ((N0, V0, c0), N2, V2, c2) Osmall Wsmall /\
    end_com c2 /\ checkpoint \notin Osmall). Admitted.

Lemma same_com {N0 N V c Nmid Vmid cmid O1 W1 Nend1 Vend cend O2 W2}:
  WARok (getdomain N0) [::] [::] c ->
  subset_nvm N0 N ->
  trace_cs (N, V, c) (Nmid, Vmid, cmid) O1 W1 ->
  trace_cs (N0 U! Nmid, V, c) (Nend1, Vend, cend) O2 W2 ->
  exists (Nend2: nvmem), trace_cs (N, V, c) (Nend2, Vend, cend) O2 W2.
Admitted.

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
  move: (same_com H H0 H3 Tend) => [Nend0 Tdone].
  exists Nend0 Ocend Wcend. split; assumption.
  eapply IHtrace_i1; try reflexivity; try assumption.
  apply sub_update.
  repeat rewrite mem_cat in H2. move/norP: H2 => [Hblah H2].
  move/norP: H2 => [contra Hb]. rewrite mem_seq1 in contra.
    by case/eqP : contra.
    Qed.
 


Lemma empty_trace_s: forall{C1 C2: context} {O: obseq} {W: the_write_stuff},
    trace_cs C1 C2 O W -> O = [::] -> C1 = C2 /\ W = emptysets.
Admitted.


Lemma observe_checkpt_s: forall {N N': nvmem} {V V': vmem}
                     {c c' : command} {w: warvars}
                    {O: obseq} {W: the_write_stuff},
    cceval_w (N, V, (incheckpoint w ;; c)) O (N', V', c') W ->
    checkpoint \in O. Admitted.

Lemma single_step_alls: forall{C1 Cmid C3: context}
                    {Obig O1 : obseq} {W1 Wbig: the_write_stuff},
    trace_cs C1 C3 Obig Wbig ->
    Obig <> [::] ->
     cceval_w C1 O1 Cmid W1 ->
    exists(Wrest: the_write_stuff) (Orest: obseq), trace_cs Cmid C3 Orest Wrest
/\ subseq Orest Obig /\ Wbig = (append_write W1 Wrest).
 Admitted.

Lemma update_domc {N11 N12 V11 V12  N21 N22 V21 V22
                       c c1 c2 O1 O2 W1 W2}:
  cceval_w (N11, V11, c) O1 (N12, V12, c1) W1 ->
  cceval_w (N21, V21, c) O2 (N22, V22, c2) W2 ->
  (getdomain N11) = (getdomain N21) ->
  (getdomain N12) = (getdomain N22).
  Admitted.

Lemma update_onec {N11 N12 V11 V12 N21 N22 V21 V22
                       c c1 c2 O1 O2 W} {l: loc} :
  cceval_w (N11, V11, c) O1 (N12, V12, c1) W ->
  cceval_w (N21, V21, c) O2 (N22, V22, c2) W ->
    (getmap N11) l = (getmap N21) l ->
    (getmap N12) l <> (getmap N22) l ->
    l \in (getwt W). Admitted.

Lemma trace_diff {N1 V1 c1 N2 V2 c2 O W} {l: loc}:
  trace_cs (N1, V1, c1) (N2, V2, c2) O W ->
  (getmap N2) l <> (getmap N1) l ->
l \in (getwt W). Admitted.

Lemma fw_split {W W1} {l: loc}:
           l \in getfstwt (append_write W W1) ->
                 l \in (getfstwt W) \/ l \in (getfstwt W1).
  Admitted.

Lemma fw_subst_wt: forall{C1 C2: context} {O: obseq} {W: the_write_stuff},
      (* pose proof (cceval_to_rd_sv H H5). *)
  trace_cs C1 C2 O W ->
  subseq (getfstwt W) (getwt W). Admitted.

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
    - move/ (empty_trace_s T) => [ [contra10 [contra11 contra12] ] contra2]. subst. case H2 as [Hskip | [crem [w Hcp] ] ]; subst.
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
         move => el. apply/ eqP / negPn/ negP.
         move/ eqP => contra.
         move: (update_onec H0 Hcceval (H4 el) contra) => Hwcontra.
         apply Heq in Hwcontra. by apply contra.
         move => l Hl.
         destruct ((getmap Ni l) == (getmap Nc l)) eqn: Hcase;
           move/eqP: Hcase => Hcase.
         move: (update_onec H0 Hcceval Hcase Hl) => Hw1.
         apply Heq in Hw1. exfalso. by apply Hl.
         apply H5 in Hcase. subst. move/fw_split : Hcase => [Hc1 | Hc2].
         move/ Heq : (in_subseq (fw_subst_wt (CsTrace_Single H0)) Hc1) => contra. exfalso. by apply Hl. by [].
         Qed.

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
 \/ l \in Wstart. Admitted. (*14*)

Lemma wts_cped_arr: forall{N0 N Nend: nvmem} {V Vend: vmem} {c cend: command} {O: obseq} {W: the_write_stuff}
                  {Wstart Rstart: warvars} {el: el_loc},
    trace_cs (N, V, c) (Nend, Vend, cend) O W ->
    WARok (getdomain N0) Wstart Rstart c ->
    checkpoint \notin O ->
    (*O <> [::] -> empty trace annoying and i dont think
               i have to deal w it*)
    (inr el) \notin (getdomain N0) ->
   (inr el) \notin (getwt W).
Admitted. (*14*)

Lemma fw_gets_bigger:forall{ N Nmid Nend: nvmem} {V Vmid Vend: vmem} {c cmid cend: command}
                         {Omid O: obseq} {Wmid W: the_write_stuff} {l: loc},
    trace_cs (N, V, c) (Nmid, Vmid, cmid) Omid Wmid ->
    checkpoint \notin Omid ->
    trace_cs (N, V, c) (Nend, Vend, cend) O W ->
    end_com cend ->
    l \in (getfstwt Wmid) -> l \in (getfstwt W). Admitted.
                  

  Lemma ctrace_det_obs_skip {N V c Nmid Vmid cmid
                          Nend Vend Omid Wmid Oend Wend}:
    trace_cs (N, V, c)
             (Nmid, Vmid, cmid) Omid Wmid ->
    checkpoint \notin Omid ->
 trace_cs (N, V, c)
 (Nend, Vend, Ins skip) Oend Wend ->
    checkpoint \notin Oend ->
 Omid <= Oend. Admitted. (*induct over 1, then 2 nested*)

  Lemma ctrace_det_obs_CP {N V c Nmid Vmid cmid
                          Nend Vend Omid Wmid Oend Wend w crem}:
    trace_cs (N, V, c)
             (Nmid, Vmid, cmid) Omid Wmid ->
    checkpoint \notin Omid ->
 trace_cs (N, V, c)
 (Nend, Vend, (incheckpoint w);; crem) Oend Wend ->
    checkpoint \notin Oend ->
 Omid <= Oend. Admitted. (*induct over 1, then 2 nested*)

  Lemma ctrace_det_obs {N V c Nmid Vmid cmid
                          Nend Vend Omid Wmid Oend Wend cend}:
    trace_cs (N, V, c)
             (Nmid, Vmid, cmid) Omid Wmid ->
    checkpoint \notin Omid ->
 trace_cs (N, V, c)
 (Nend, Vend, cend) Oend Wend ->
 checkpoint \notin Oend ->
 end_com cend ->
 Omid <= Oend. Admitted. (*induct over 1, then 2 nested*)

  Lemma append_c {N1 V1 c1 N2 V2 crem O1 W1 N3 V3 c3 O2 W2}
        {w: warvars}:
        trace_cs (N1, V1, c1) (N2, V2, crem) O1 W1 ->
        trace_cs (N2, V2, crem) (N3, V3, c3) O2 W2 ->
        trace_cs (N1, V1, c1) (N3, V3, c3) (O1 ++ O2) (append_write W1 W2).
Admitted.

  (*this is false!!! a checkpoint gets added between O1 and O2!!!!!*)
  Lemma append_cps {N1 V1 c1 N2 V2 crem O1 W1 N3 V3 c3 O2 W2}
        {w: warvars}:
        trace_cs (N1, V1, c1) (N2, V2, incheckpoint w;; crem) O1 W1 ->
        trace_cs (N2, V2, crem) (N3, V3, c3) O2 W2 ->
        trace_cs (N1, V1, c1) (N3, V3, c3) (O1 ++ O2) (append_write W1 W2).
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

   Lemma sub_restrict: forall(N1: nvmem) (w: warvars), subset_nvm (N1 |! w) N1.
     Admitted.

Lemma all_diff_in_fw_sym {N1 V1 c1 Nc1}: 
  all_diff_in_fw N1 V1 c1 Nc1 ->
all_diff_in_fw Nc1 V1 c1 N1. Admitted.

Lemma all_diff_in_fw_trans {Nc0 V1 c1 Nc1 Nc2}:
  all_diff_in_fw Nc0 V1 c1 Nc1 ->
  all_diff_in_fw Nc1 V1 c1 Nc2 ->
  all_diff_in_fw Nc0 V1 c1 Nc2. Admitted.

Lemma adif_works {N1 N2 V c Nend Vend O1 W1 cend}:
  all_diff_in_fw N1 V c N2 ->
  trace_cs (N1, V, c) (Nend, Vend, cend) O1 W1 ->
  end_com cend -> checkpoint \notin O1 ->
  trace_cs (N2, V, c) (Nend, Vend, cend) O1 W1. Admitted.

Lemma trace_converge {N V crem Nc} {w: warvars}:
  all_diff_in_fw N V ((incheckpoint w);;crem) Nc ->
  N = Nc. Admitted.

(*might be easier to just do appending in general*)

Lemma step_end_cpi {N0 V0 N1 V1 c1 N2 V2 crem O1 W1 }
        {w: warvars}:
        trace_i1 ((N0, V0, c1), N1, V1, c1) ((N0, V0, c1), N2, V2, incheckpoint w;; crem) O1 W1 ->
        trace_i1 ((N0, V0, c1), N1, V1, c1) ((N0, V0, c1), N2, V2, crem) O1 W1. 
Admitted.

        (*induct on length of 1st trace, rewrite nested filters into filtering
         out the appended list*)

Lemma warok_cp {N1 N2 V1 V2 c crem O W}
      {w0 w1: warvars}:
  WARok w0 [::] [::] c ->
  trace_cs (N1, V1, c) (N2, V2, incheckpoint w1;; crem) O W ->
  WARok w1 [::] [::] crem. Admitted.

Lemma adif_refl {N V c c1 Nend Vend O W}:
  trace_cs (N, V, c) (Nend, Vend, c1) O W ->
  end_com c1 ->
  checkpoint \notin O ->
        all_diff_in_fw N V c N.
Admitted.

Lemma threeIS1 {N0 Ni Ni1 V V1 c c1 Nc O W}:
  all_diff_in_fw Ni V c Nc -> (*ensures well formed up till nearest endcom*)
  trace_i1 ((N0, V, c), Ni, V, c) ((N0, V, c), Ni1, V1, c1) O W ->
  WARok (getdomain N0) [::] [::] c ->
  subset_nvm N0 Ni -> 
  checkpoint \notin O ->
  (exists(Oc: obseq) (Nc1: nvmem) (Wc: the_write_stuff) , trace_cs (Nc, V, c) (Nc1, V1, c1) Oc Wc /\ all_diff_in_fw Ni1 V1 c1 Nc1 
  ).
Proof. intros. move: Nc H H3. (* remember H0 as Ht. induction H0.
                    ask arthur*)
dependent induction H0; intros.
  + move: (three_bc H3 H H0) => [ Nc1 [Tdone Hdone] ].
    exists O Nc1 W. repeat split; try assumption.
  + assert (all_diff_in_fw Ni V c (N0 U! Nmid)) as Hdiffrb.
    - inversion H5. subst.  econstructor; try apply T; try assumption.
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
   apply (fw_gets_bigger H H1 T H7 good).
   rewrite in_nil in bad. by discriminate bad.
   eapply IHtrace_i1; try reflexivity; try assumption.
   apply sub_update. apply (all_diff_in_fw_trans (all_diff_in_fw_sym Hdiffrb) H5).
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


Lemma frag_to_seq: forall{O1 O2: obseq},
                    (O1 <=f O2) ->
                    checkpoint \notin O1 ->
                    O1 <=m O2.
Admitted.

Lemma no_CP_in_seq: forall{O1 O2: obseq},
    (O1 <=m O2) -> checkpoint \notin O1 /\ checkpoint \notin O2.
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
   apply RB_Ind; try assumption.
   apply (neg_observe_rb H).
   rewrite mem_cat; apply/ norP; split.
    apply (neg_observe_rb ass1).
    apply (neg_observe_rb ass4).
    move: (frag_to_seq ass3) => Hannoying.
    apply no_CP_in_seq in Hannoying.
    move: Hannoying => [Ha1 Ha2].
    apply Ha2.
    rewrite mem_cat.
    by apply/ norP.
    rewrite mem_cat.
      by apply/ norP.
      move: (three_bc H7 H H1) => [Nc3 [threetrace whatever] ].
   move: (append_c ass1 ass4) => bigtrace.
    eapply ctrace_det_obs; try apply (append_c ).


   eapply IHtrace_i1; try reflexivity; try assumption.
   apply sub_update. apply (all_diff_in_fw_trans (all_diff_in_fw_sym Hdiffrb) H7).
      +
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
Qed.

  Lemma both_cp {O1 O2} :
    (O1 <=f O2) -> checkpoint \notin O1 ->
    (O1 <=m O2) /\ checkpoint \notin O2.
    Admitted.
  (*  intros. inversion H; subst; try assumption.
    repeat rewrite mem_cat in H0.
    move/norP : H0 => [Hb H0]. move/norP: H0 => [contra Hb2].
    exfalso. move/negP: contra. by apply. Qed.*)


Lemma empty_trace_cs:
  forall{N1 N2: nvmem} {V1 V2: vmem} {c: command} {O: obseq} {W: the_write_stuff},
    trace_cs (N1, V1, c) (N2, V2, c) O W -> O = [::] /\ N1 = N2 /\ V1 = V2 /\ W = emptysets.
Admitted.

Theorem One2 {N0 V c N01 V01 c01 Ni Oi Nendi Vend Nc Wi
           }:
      trace_i1 ((N0, V, c), Ni, V, c) ((N01, V01, c01), Nendi, Vend, Ins skip) Oi Wi ->
subset_nvm N0 Ni -> 
all_diff_in_fw Ni V c Nc ->
WARok (getdomain N0) [::] [::] c ->
(exists(Nendc: nvmem) (Oc: obseq) (Wc: the_write_stuff) , trace_cs (Nc, V, c) (Nendc, Vend, Ins skip) Oc Wc /\
(Oi <=f Oc) /\ (nvmem_eq Nendi Nendc)).
suffices: 
  (exists(Oc Oendc: obseq) (Nendc: nvmem) (Wc Wendc: the_write_stuff),
      trace_cs (Nc, V, c) (Nendc, Vend, Ins skip) Oc Wc /\
 all_diff_in_fw Nendi Vend skip Nendc /\ trace_cs (Nendc, Vend, Ins skip)
            (Nendc, Vend, Ins skip) Oendc Wendc
  ).
move => [Oc threehyp] Ti Hsub Hdiff Hok.



    Theorem One {N0 V c N01 V01 c01 Ni Oi Nendi Vend Nc Wi
           }:
      trace_i1 ((N0, V, c), Ni, V, c) ((N01, V01, c01), Nendi, Vend, Ins skip) Oi Wi ->
subset_nvm N0 Ni -> 
all_diff_in_fw Ni V c Nc ->
WARok (getdomain N0) [::] [::] c ->
(exists(Nendc: nvmem) (Oc: obseq) (Wc: the_write_stuff) , trace_cs (Nc, V, c) (Nendc, Vend, Ins skip) Oc Wc /\
(Oi <=f Oc) /\ (nvmem_eq Nendi Nendc)).
intros. dependent induction H.
- (*all continuous execution*)
  exists Nendi O W. repeat split. apply (adif_works H2 H); try assumption. by left.
  repeat constructor. apply (neg_observe_rb H). assumption.
- (*reboot*)
  Check three_bc.
  assert (trace_i1
         (N01, V01, c01, Ni, V01,
         c01)
         (N01, V01, c01, N01 U! Nmid, V01, c01)
         (O1 ++ [:: reboot] ++ [::]) (append_write W1 emptysets)) as Tis3.
  eapply iTrace_RB; try apply H; try assumption; try repeat constructor.
  Check threeIS1.
  assert (checkpoint \notin O1 ++ [:: reboot] ++ [::]) as Hcp. repeat rewrite mem_cat. repeat (apply/norP; split); try assumption; try auto.
  Check threeIS1.
  move: (threeIS1 H4 Tis3 H5 H3 Hcp) => [Ocuseless [Ncuseless [Wcusless
                                                         [Tusless Hdiff] ] ] ].
  suffices: (exists Nendc Oc Wc,
               trace_cs (Nc, V01, c01)
                 (Nendc, Vend, Ins skip) Oc Wc /\
               (O2 <=f Oc) /\
               nvmem_eq Nendi Nendc).
  - move => [Nendc [Oc [ Wc [Tdone [Hoend HNdone] ] ] ] ].
  exists Nendc Oc Wc; repeat split; try assumption.
  move: (both_cp Hoend H2) => [Hprefixend Hoccp].
  move: (three_bc H4 H H1) => [Ncmid [Tcmid Hdiffmid] ].
  move: (ctrace_det_obs Tcmid H1 Tdone Hoccp) => Hprefixstart.
  constructor. apply RB_Ind; try assumption.
  apply (neg_observe_rb H). apply (neg_observe_rb Tdone).
  - move: (empty_trace_cs Tusless) => [eq1 [eq2 [eq3 eq4] ] ]. subst.
    eapply IHtrace_i1; try reflexivity; try assumption. apply sub_update.
  - apply exist_endcom in H1. move: H1 =>
                              [Oendmi [Wendmi [Nendmi [Vendm [cendm
                              [Tendmi [Hendcom Hoendmi] ] ] ] ] ] ].
      assert (WARok (getdomain (Nmid |! w)) [::] [::] crem) as Hwarok2.
      + destruct Nmid as [mc1 dc1]. rewrite/getdomain.
      move: (same_comi H4 H2 H H0) => [Ncstart [Ocstart [Wcstart [Tcstart Hocstart] ] ] ].
      apply (warok_cp H4 Tcstart). 
    move: (same_comi Hwarok2 (sub_restrict Nmid w) Tendmi Hoendmi) => [Nendm [Oendm
                                                     [Wendm
                                           [Tendm Hoendm] ] ] ].
    assert (exists(Oc Oendmc: obseq) (Ncmid: nvmem) (Wc Wendmc: the_write_stuff),
               trace_cs (Nc, V, c) (Ncmid, Vmid, crem) Oc Wc
               /\ all_diff_in_fw Nmid Vmid crem Ncmid /\ trace_cs (Ncmid, Vmid, crem) (Nendm, Vendm, cendm) Oendmc Wendmc) as Hdiff.
    apply step_end_cpi in H. 
    Check three. eapply (three H3 H); try apply Tendm; try assumption.
    apply Tendm; try assumption.
    Check same_comi.
    eapply three.



  repeat constructor; try assumption; try 
  (eapply (neg_observe_rb); try eassumption).


  Lemma ctrace_subseq

  eapply IHtrace_i1.
  (*strange philosophically that one can approach deductive truth
   from a sort of back door*)










