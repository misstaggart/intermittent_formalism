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

Definition nvm_eq N1 N2 := subseq (getdomain N1) (getdomain N2) /\
                           subseq (getdomain N2) (getdomain N1).

Lemma hacky_nvm_eq N1 N2 : nvm_eq N1 N2 <-> (getdomain N1) = (getdomain N2).
Admitted.

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

   Lemma sub_update: forall(N0 N1: nvmem),
    subset_nvm N0 (N0 U! N1).
  intros.
  destruct N0, N1.
  unfold subset_nvm. split.
  simpl. apply prefix_subseq.
  intros. simpl. by rewrite H.
  Qed.

Lemma all_diff_in_fw_sym {N1 V1 c1 Nc1}: 
  all_diff_in_fw N1 V1 c1 Nc1 ->
all_diff_in_fw Nc1 V1 c1 N1. Admitted.

Lemma all_diff_in_fw_trans {Nc0 V1 c1 Nc1 Nc2}:
  all_diff_in_fw Nc0 V1 c1 Nc1 ->
  all_diff_in_fw Nc1 V1 c1 Nc2 ->
  all_diff_in_fw Nc0 V1 c1 Nc2. Admitted.

Lemma adif_works {N1 N2 V c Nend Vend O1 W1}:
  all_diff_in_fw N1 V c N2 ->
  trace_cs (N1, V, c) (Nend, Vend, Ins skip) O1 W1 ->
  trace_cs (N2, V, c) (Nend, Vend, Ins skip) O1 W1. Admitted.

Lemma three N0 V0 c0 N01 V01 c01 Ni Ni1 Nend V V1 Vend c c1 Nc O W Oend Wend:
  all_diff_in_fw Ni V c Nc ->
  trace_i1 ((N0, V, c), Ni, V, c) ((N01, V01, c01), Ni1, V1, c1) O W ->
  WARok (getdomain N0) [::] [::] c ->
  subset_nvm N0 Ni -> subset_nvm N0 Nc ->
  trace_cs (Ni1, V1, c1) (Nend, Vend, Ins skip) Oend Wend -> (*ensuring int mem is well formed,
                                                   can put Ni1 arbitrarily far back after this lemma is finished*)
  (exists(Oc Oendc: obseq) (Nc1: nvmem) (Wc Wendc: the_write_stuff) , trace_cs (Nc, V, c) (Nc1, V1, c1) Oc Wc /\ all_diff_in_fw Ni1 V1 c1 Nc1 /\ trace_cs (Nc1, V1, c1) (Nend, Vend, Ins skip) Oendc Wendc
  ).
Proof.
  intros. move: Nc H H3. (* remember H0 as Ht. induction H0.
                    ask arthur*)
dependent induction H0; intros.
  + move: (three_bc H3 H H0) => [ Nc1 [Tdone Hdone] ].
    exists O Oend Nc1 W Wend. repeat split; try assumption.
    apply (adif_works Hdone H4).
  + assert (all_diff_in_fw Ni V01 c01 (N01 U! Nmid)) as Hdiffrb.
    - inversion H6. subst.  econstructor; try apply T; try assumption.
    move => el. apply/ eqP / negPn/ negP => contra.
   apply update_diff in contra. destruct contra as [ [con11 con12] | [con21 con22] ].
   destruct H4 as [H41 H42]. apply con11. apply (H42 (inr el) con12).
   move: (trace_diff H con21) => Hdiff.
   move/negP :(wts_cped_arr H H3 H1 con22). by apply.
   move => l. move/eqP/update_diff => [ [diff11 diff12] | [diff21 diff22] ]. destruct H4 as [H41 H42]. case diff11. apply (H42 l diff12).
   move: (trace_diff H diff21) => Hdiff.
   (*start here clean up repeated work in above*)
   move: (wts_cped_sv H H3 H1 diff22 Hdiff)  => [good | bad].
   rewrite/remove filter_predT in good.
   apply (fw_gets_bigger H H1 T H8 good).
   rewrite in_nil in bad. by discriminate bad.
   eapply IHtrace_i1; try reflexivity; try assumption.
   apply sub_update. apply (all_diff_in_fw_trans (all_diff_in_fw_sym Hdiffrb) H6).
 +

   exfalso. apply/nilP: bad.
   rewrite nilP in bad.
   apply good.


   apply update_diff in Hdiff.

   apply/ eqP / negPn/ negP => contra.
   apply update_diff in contra. destruct contra as [ [con11 con12] | [con21 con22] ].
   destruct H4 as [H41 H42]. apply con11. apply (H42 (inr el) con12).
   move: (trace_diff H con21) => Hdiff.
   move/negP :(wts_cped_arr H H3 H1 con22). by apply.
   rewrite/subset_nvm in H4.



   move: (wts_cped_arr H H3 H1)


    move: (three_bc H6 H H1) => Hmid.
    (*get rid of observation stuff, you dont need it,
     just say exists*)













        dependent induction H; intros.
    (*empty trace case*)
  - exists Nc; split; auto; constructor.
    (*cceval case*)
  -  move: (three_bc1 H4 H H0) => [Nc1 [Hcceval Hdiff] ].
     exists Nc1. split; try assumption. apply (CsTrace_Single Hcceval).
  - (*inductive cs case*)
    destruct Cmid as [ [Nmid Vmid] cmid]. Check three_bc1.
    rewrite mem_cat in H2. move/norP : H2 => [H21 H22].
    (*start here is there a way to combine the above*)
    move: (three_bc1 H6 H1 H21) => [Ncmid [Tmid Hmid] ].
    suffices: exists Nc1,
               trace_cs (Ncmid, Vmid, cmid) (Nc1, V1, c1) O2 W2 /\
               all_diff_in_fw Ni1 V1 c1 Nc1.
  - move => [ Nc1 [Tmid2end Hmid2end] ]. exists Nc1. split; try assumption.
    eapply CsTrace_Cons; try apply Tmid2end; try assumption.
    eapply IHtrace_cs; try reflexivity; try assumption.


    apply Hmid2end.

    Check two.
    suffices: exists Nc1,
       trace_cs (Nc, V, c) (Nc1, Vmid, cmid) O1 W1 /\
       all_diff_in_fw Nmid Vmid cmid Nc1.
  - intros thing.  destruct thing as [Nc1 thing].
    move => [Nc1].

    move: (two H1 H) => [Nc1 [Hcceval Heq] ]. exists Nc1.
    split. apply CsTrace_Single; assumption.
    inversion H1. subst. 
    (*getting ready to apply single_step_alls*)
    assert (O0 <> [::]) as Ho0.
    - move/ (empty_trace_s T) => [ [contra10 [contra11 contra12] ] contra2]. subst. case H2 as [Hskip | [crem [w Hcp] ] ]; subst.
    inversion Hcceval. move/negP : H0. apply.
    (*start here why is apply/negP different from this*)
    apply (observe_checkpt_s Hcceval).
    (*ask arthur i want to write
     exists O exists W H, like a function*)
         move: (single_step_alls T Ho0 H) => [W1 [O1 [T1 [Hsub Hw ] ] ] ].
         econstructor; try apply T1; try assumption.
         apply/ negP => contra.
         move/ negP : H3. apply.
         apply (in_subseq Hsub contra).
        (* apply (update_domc H Hcceval); assumption.*)
         move => el. apply/ eqP / negPn/ negP.
         move/ eqP => contra.
         move: (update_onec H Hcceval (H4 el) contra) => Hwcontra.
         apply Heq in Hwcontra. by apply contra.
         move => l Hl.
         destruct ((getmap Ni l) == (getmap Nc l)) eqn: Hcase;
           move/eqP: Hcase => Hcase.
         move: (update_onec H Hcceval Hcase Hl) => Hw1.
         apply Heq in Hw1. exfalso. by apply Hl.
         apply H5 in Hcase. subst. move/fw_split : Hcase => [Hc1 | Hc2].
         move/ Heq : (in_subseq (fw_subst_wt (CsTrace_Single H)) Hc1) => contra. exfalso. by apply Hl. by [].
   - (*larger continuous trace case*)
         apply Heq in Hc1.
         apply fw_split in Hcase.




         case: ((getmap Ni l) == (getmap Nc l)) => [Hc1 | Hc2].
         apply H5 in el.


         apply/ negP : H3.
    move: (observe_checkpt_s Hcceval) => Hin. apply H3.
    remember T as T1. apply (contra _ _ _) in T.
    econstructor.
    apply T.*)
 -
