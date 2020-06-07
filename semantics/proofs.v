Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From TLC Require Import LibTactics LibLogic.
Import ListNotations.
From Semantics Require Import programs semantics algorithms lemmas. (*shouldn't have to import both of these*)

Open Scope list_scope.
Open Scope type_scope.

(*lemmas for the lemmas; not in paper*)
Lemma sub_disclude: forall(N0 N1 N2: nvmem) (l: loc),
                     subset_nvm N0 N1 ->
                     subset_nvm N0 N2 ->
                     not ((getmap N1) l = (getmap N2) l)
                     -> not (In (loc_warvar l) (getdomain N0)).
Proof. intros. intros contra. unfold subset_nvm in H. destruct H.
       remember contra as contra1. clear Heqcontra1.
       apply H2 in contra.
       unfold subset_nvm in H0. destruct H0. apply H3 in contra1.
       symmetry in contra.
       apply (eq_trans _ _ _ contra) in contra1.
       apply H1. assumption.
Qed.

(*Lemma accwt_assoc_wt: forall(L1 L2: list step),
    getwt(acc_wts L1) ++ getwt(acc_wts L2) =
    getwt (acc_wts (L1 ++ L2)).
  intros. induction L2.
  + simpl. repeat rewrite app_nil_r. reflexivity.
  + destruct a as [blah W]. simpl. *)

(*need to force WL, OL, CL to be the same length...product type*)
Lemma wt_subst_fstwt: forall{L: list step} {s e : nat} (T: trace_c L s e),
    incl (Wt T) (FstWt T).
Proof. induction L; intros.
       +inversion T. subst.
       - inversion H1. 
       + 
         inversion T. subst.
         unfold Wt. unfold FstWt.
         destruct (e <? (Datatypes.length L)) eqn: eqlen.
         cut (trace_c L s e).
         + intros. eapply IHL.
         pose proof (prop_degeneracy (e < (Datatypes.length L))).
         destruct H0.
         -
         unfold Wt. unfold FstWt. induction WL.
       + assert (List.length CL = 0).
       - apply same_len in H. simpl in H. destruct H. assumption.
         rewrite H0 in H1. inversion H1.
       + 
         induction T.
       + simpl. apply (incl_refl []).
       + induction c; try (simpl; apply (incl_refl [])); try (
         rewrite (lock remove) /= -lock;
         rewrite app_nil_r;
          apply remove_subst).
       - assumption.
       - Admitted.

(*actual lemmas*)

Lemma onePointone: forall(N N' W W' R R': warvars) (l: instruction),
    DINO_ins N W R l N' W' R' -> incl N N'.
Proof. intros. induction H; try((try apply incl_tl); apply (incl_refl N)).
Qed.


Lemma onePointtwo: forall(N N' W R: warvars) (c c': command),
    DINO N W R c c' N' -> incl N N'.
Proof. intros. induction H; try(apply onePointone in H); try apply (incl_refl N); try assumption.
       -  apply (incl_tran H IHDINO).
       - apply (incl_appl N2 IHDINO1). (*why is coq too stupid to figure out these instantiations*)
 Qed.

Lemma Two: forall(N N' W W' R R' N1: warvars) (l: instruction),
    DINO_ins N W R l N' W' R' -> incl N' N1 -> WAR_ins N1 W R l W' R'.
  intros. induction H; try (constructor; assumption || (apply War_noRd; assumption));
            (apply WAR_Checkpointed || apply WAR_Checkpointed_Arr);
            (repeat assumption); apply H0; unfold In; left; reflexivity.
Qed.


Theorem DINO_WAR_correct: forall(N W R N': warvars) (c c': command),
    DINO N W R c c' N' -> (forall(N1: warvars), incl N' N1 -> WARok N1 W R c').
  intros N W R c c' N' H. induction H; intros N0 Hincl.
  - eapply WAR_I. applys Two H Hincl.
  - eapply WAR_Seq. applys Two H. apply onePointtwo in H0. eauto using incl_tran.
    apply (IHDINO N0 Hincl).
  - eapply WAR_If; (try eassumption);
      ((apply IHDINO1; apply incl_app_l in Hincl)
       || (apply IHDINO2; apply incl_app_r in Hincl)); assumption.
  - intros. apply WAR_CP. apply IHDINO. apply (incl_refl N').
Qed.


Lemma eight: forall(N0 N1 N2: nvmem) (V0: vmem) (c0: command),
              (subset_nvm N0 N1) ->
              (subset_nvm N0 N2) ->
              current_init_pt N0 V0 c0 N1 N2 ->
              same_pt N1 V0 c0 c0 N1 N2.
Proof. intros. inversion H1; subst.
       apply (same_mem (CTrace_Empty (N1, V0, c0))
                       T); (try assumption).
       - simpl. intros contra. contradiction.
       - intros. simpl.
         assert (H6: not (In (loc_warvar l) (getdomain N0))) by
               apply (sub_disclude N0 N1 N2 l H H0 H5).
           apply H4 in H5. destruct H5. split. 
         + unfold Wt. unfold FstWt in H5. apply ((wt_subst_fstwt T) l H5).
         + split.
       - unfold FstWt. unfold FstWt in H5. assumption.
       - intros contra. contradiction.
         + apply H6 in H5. contradiction.
Qed.


Ltac destruct3 zero one two three:= destruct zero as [Annoying one]; destruct Annoying as [two three].

Ltac ex_destruct3 H := destruct H as [var1 Annoying]; destruct Annoying as [var2 Annoying1];
                       destruct Annoying1 as [var3 H].

Ltac destruct_ms M L WT T obs:= destruct M as [L neverseen]; destruct neverseen as [WT neverseen];
                            destruct neverseen as [T obs].

Ltac generalize_5 N N' V V' O := generalize dependent N;
                               generalize dependent N';
                               generalize dependent V;
                               generalize dependent V';
                               generalize dependent O.
(*Ltac get_trace M :=*)

Lemma ins_to_skip: forall {N N': nvmem} {V V': vmem}
                    {l: instruction} {c: command}
  {L: list step} {W: list the_write_stuff},
    trace_c L (N, V, Ins l) (N', V', c) W ->
    (c = Ins l) \/ (c = skip).
Proof.
  intros N N' V V' l c L W T. dependent induction T.
  + constructor.
  + reflexivity.
  + inversion c0; subst; try(right; reflexivity).
  + destruct3 S2 cmid nmid vmid.
    assert (cmid = l \/ cmid = skip).
    {
      apply (IHT1 N nmid V vmid l cmid); reflexivity.
    }
  + inversion H; subst.
       -  eapply IHT2; reflexivity.
       - right.
         destruct (IHT2 nmid N' vmid V' skip c); (reflexivity || assumption).
Qed.

Lemma obs_subst_app_l: forall(L1 L2: list step),
    incl (acc_obs L1) (acc_obs (L1 ++ L2)).
  Proof. Admitted.

Lemma obs_subst_app_r: forall(L1 L2: list step),
    incl (acc_obs L2) (acc_obs (L1 ++ L2)).
  Proof. Admitted.

  (*WEIRD induction principle when I have T explicitly quantified*)
  (*clean this up or just take observation sequence
   out of the step type*)
Lemma observe_checkpt: forall {N N': nvmem} {V V': vmem}
                     {c c': command} {w: warvars}
                    {L: list step} {W: list the_write_stuff},
    (trace_c L (N, V, (incheckpoint w ;; c)) (N', V', c') W) ->
    c' = (incheckpoint w ;; c) \/ In checkpoint (acc_obs L).
  intros N N' V V' c c' w L W T.
  dependent induction T.
  + left. reflexivity.
  +  inversion c0; subst. right. left. reflexivity.      
  +  inversion H8.
    destruct3 S2 cmid nmid vmid. destruct (IHT1 N nmid V vmid c cmid w); subst; try reflexivity.
  - destruct (IHT2 nmid N' vmid V' c c' w); subst; try reflexivity.
    + left; reflexivity.
    + right. apply (obs_subst_app_r L1 L2). apply H.
 - right. apply (obs_subst_app_l). apply H.
Qed.


(*Lemma single_step: *)

(*could also add that written set of c -> c2 is inside written set of
 l;;c -> c2 but ill wait till I need it *)

(*hack to get around destroying conjunctions all the time
Lemma single_step: forall{N N2: nvmem} {V V2: vmem}
                    {l: instruction} {c c2: command}
                    {O: obseq} {W: the_write_stuff},
    trace_c (N, V, l;;c) (N2, V2, c2) O W ->
    not ((l ;;c ) = c2) -> (*empty trace case *)
    exists(N1: nvmem) (V1: vmem) (O1: obseq), ((multi_step_c (N1, V1, c) (N2, V2, c2) O1)
                                         ).
Proof. intros. pose proof (single_step_all X H).
       ex_destruct3 H0. destruct H0.
       exists var1 var2 var3. assumption.
Qed.*)

(*hacky extra hypothesis L = [], coq should take care of remembering that*)


Lemma append_write_empty: forall{W1 W2: list the_write_stuff},
    (append_write W1) = emptysets ->
    (append_write W2) = emptysets ->
    append_write (W1 ++ W2) = emptysets.
Admitted.

Lemma trace_stops: forall {C1 C2: context} {W: list the_write_stuff}
                     {L: list step}
  (T: trace_c L C1 C2 W), L = [] -> C1 = C2 /\ (append_write W) = emptysets.
Proof. intros C1 C2 W L T. induction T; intros.
       + split; reflexivity.
       + inversion H.
       + apply app_eq_nil in H. destruct H. destruct (IHT1 H).
         destruct (IHT2 H0). subst. split; [reflexivity |
                                            apply (append_write_empty H2 H4)]
                                            .
Qed.

Lemma undo_gets: forall(W: the_write_stuff),
    (getwt W, getrd W, getfstwt W) = W.
  intros. destruct3 W f g h. simpl. reflexivity. Qed.

  (*ask arthur what is up with the variable names where
this doesnt work destruct3 W one two three.*)


(*clean this one up*)
Lemma single_step: forall (C1 C2 C3 C4: context) (W: list the_write_stuff)
                     (L: list step)
                     (O: obseq)
  (T: trace_c L C1 C2 W), L = [(C3, C4, O)] -> cceval_w C1 O C2 W /\ C1 = C3 /\ C2 = C4.
Proof. intros C1 C2 C3 C4 W L a T. induction T.
       + intros. inversion H. 
       + intros.  inversion H. subst. split; [assumption | split; reflexivity].
       + intros H.
         apply app_eq_unit in H. destruct H; destruct H; subst.
       - destruct (trace_stops T1). reflexivity. subst.
         Admitted.
        (* apply append_write_empty in H0.
         unfold append_write. simpl. unfold remove. unfold in_loc_b.
         rewrite filter_false. rewrite undo_gets. apply IHT2. reflexivity.
       - destruct (trace_stops T2). reflexivity. subst.
         unfold append_write. simpl. repeat rewrite app_nil_r.
         rewrite undo_gets. apply IHT1. reflexivity.
Admitted.*)


Lemma cceval_behaves: forall{C1 C2 C3: context} {W2 W3: list the_write_stuff}
                       {O2 O3: obseq},
    cceval_w C1 O2 C2 W2->
    cceval_w C1 O3 C3 W3 ->
    C2 = C3 /\ O2 = O3 /\ W2 = W3.
Admitted.

Lemma single_of_many:
(*conclusion: induction on L is not the way to go
  forall{Lbig Lrest: list step}
                 {N1 N2 N3: nvmem}
                    {V1 V2 V3: vmem}
                    {Ostep: obseq}
                    {s: step}
                    {Wbig Wrest: list the_write_stuff}
                    {w: the_write_stuff}
                    {c1 c2 c3: command},
    trace_c (Lbig) (N1, V1, c1) (N3, V3, c3) (Wbig) ->
    cceval_w (N1, V1, c1) Ostep (N2, V2, c2) [w] ->
    Lbig = (s::Lrest) ->
    Wbig = (w:: Wrest) ->
   trace_c Lrest (N2, V2, c2) (N3, V3, c3) Wrest.
Proof. intros Lbig.
        induction Lbig.
       + intros. inversion H0.
       + intros. subst. inversion H0. subst. clear H0.
         eapply IHLbig.



         destruct3 s s1 s2 s3. remember X as T. clear HeqT. apply (single_step (N1, V1, c1)
                                                  (N3, V3, c3)
                                                  s2
                                                  s3
                                                  (w:: Wrest)
                                                  [(s2, s3, s1)]
                                                  s1) in X.
         destruct X. destruct H1. subst. destruct (cceval_behaves H0 H).
         destruct H2. rewrite H1. inversion H3. apply CTrace_Empty.
         constructor.
      + intros.
         (*need IH to be more general*)
         reflexivity.

   exists(Lsmall: list step)  (Wsmall: list the_write_stuff),
     inhabited (trace_c Lsmall (N2, V2, c2) (N3, V3, c3) Wsmall).*)

Lemma single_step_all: forall{N1 N2 N3: nvmem}
                        {V1 V2 V3: vmem}
                        {Ostep: obseq}
                        {Lbig: list step}
                        {Wbig Wstep: list the_write_stuff}
                     {c1 c2 c3: command},
    trace_c Lbig (N1, V1, c1) (N3, V3, c3) Wbig ->
   (N1, V1, c1) <> (N3, V3, c3) -> (*has stepped*)
   cceval_w (N1, V1, c1) Ostep (N2, V2, c2) Wstep ->
   exists(Lsmall: list step)  (Wsmall: list the_write_stuff),
     inhabited (trace_c Lsmall (N2, V2, c2) (N3, V3, c3) Wsmall).
Proof. intros N1 N2 N3 V1 V2 V3 Ostep Lbig Wbig Wstep c1 c2 c3 T
              Hskip Hceval. induction Lbig.
       + apply trace_stops in T. destruct T. apply Hskip in H. contradiction.
         reflexivity.

    exists(N1: nvmem) (V1: vmem) (O1: obseq), ((multi_step_c (N1, V1, c) (N2, V2, c2) O1)
                                          /\ (incl O1 O)
                                          ).
  intros N N2 V V2 l c c2 O W T H. dependent induction T. 
  + exfalso. apply H. reflexivity.
  + inversion c0; subst; exists N2 V2 (nil : obseq); try (split;
                                                     [exists emptysets; repeat constructor | apply empty_sub]).
  + destruct3 Cmid. assert (Dis: (l ;; c) = cmid \/ not ((l;;c) = cmid))
      by (apply classic). destruct Dis.
  - subst. 
    cut (exists N1 V1 O1, (multi_step_c (N1, V1, c) (N2, V2, c2) O1 /\ incl O1 O2)).
    + intros H3. ex_destruct3 H3. exists var1 var2 var3. destruct H3 as [H31 H32]. split.
      -  assumption.
      - apply (incl_appr O1 H32).  
   + apply (IHT2 nmid N2 vmid V2 l c c2); try reflexivity; try assumption.
 -  assert (Hmid: exists N3 V3 O3,
               multi_step_c (N3, V3, c) (nmid, vmid, cmid) O3
              /\ incl O3 O1
           ).
     - eapply IHT1; try reflexivity; try assumption.
       assert (Hend: multi_step_c (nmid, vmid, cmid)
                                              (N2, V2, c2) O2
            ).
       + exists W2. apply (inhabits T2).
       ex_destruct3 Hmid.
       destruct Hmid as [Hmid Obsmid].
     destruct_ms Hmid Tmid Wmid.
     destruct_ms Hend Tend Wend.
     exists var1 var2 (var3 ++ O2). split.
     + exists (append_write Wmid Wend ). constructor.
       apply (CTrace_App Tmid Tend).
     +  apply (incl_app_dbl Obsmid (incl_refl O2)).
Qed.
(*N0 is checkpointed variables*)
Lemma ten: forall(N0 W R: warvars) (N N': nvmem) (V V': vmem)
            (O: obseq) (c c': command),
            WARok N0 W R c ->
            multi_step_c (N, V, c) (N', V', c') O ->
            not (In checkpoint O) ->
            exists(W' R': warvars), WARok N0 W' R' c'.
  intros.
  (*unfold multi_step_ic in H0. destruct H0 as [Wr].*)
  generalize_5 N N' V V' O.
  remember H as warok. clear Heqwarok.
  induction H; intros.
  + destruct_ms H0 L WT T H0.
    assert (Hc': c' = Ins l \/ c' = skip) by
                                           (apply (ins_to_skip T)).
    destruct Hc'; subst; exists W R. (*eapply WAR_I.*)
    - apply warok.
    - eapply WAR_I. apply WAR_Skip.
 + destruct_ms H0 L WT T H0. remember T as T1. clear HeqT1.
        apply observe_checkpt in T. destruct T.
    - subst. exists W R. apply warok.
    - unfold getobs in H0. subst. apply H1 in H2. contradiction.
 +




    (*how to induct on L*)
    destruct_ms H0 L Wr T.
    generalize_5 N N' V V' O.
    generalize dependent l.
    generalize dependent c'.
    induction L; intros.
  - assert ( (N0, V, Ins l) = (N', V', c')).
    + apply (trace_stops T). reflexivity.
      inversion H2. subst. exists W R. eapply WAR_I. apply H.
  - destruct L. destruct3 a Oa C1 C2.
    remember T as T1. clear HeqT1. eapply single_step in T.
    inversion T; subst.
    (*end of induction on L*)
    remember T as T1. clear HeqT1. apply trace_not_empty in T. exfalso.
    apply T. reflexivity.
  + exists W R. applys WAR_I. apply H.
  + inversion c; subst; try (exists W R; applys WAR_I; constructor).
  - destruct3 Cmid. 
    assert (Hcmid: cmid = Ins l \/ cmid = skip) by
                                           (apply (trace_stops T1)).
    destruct Hcmid; subst.
  - eapply IHT2; (try reflexivity). apply H.
    (*apply (inhabits T2).*)
  - intros contra. eapply in_app_r in contra. apply H1 in contra. contradiction.
 (* - apply (inhabits T2).*)
    - apply trace_stops in T2. destruct T2; subst; exists W R;
                                 eapply WAR_I; constructor.
      + (*inversion H0 as [T].*)
    destruct_ms H0 T Wr.
        apply observe_checkpt in T. destruct T.
        - subst. exists W R. constructor. assumption.
        - apply H1 in H0. contradiction.
        - assert (Dis: (l ;; c) = c' \/ not ((l;;c) = c'))
      by (apply classic). destruct Dis.
         + subst. exists W R. eapply WAR_Seq. apply H. assumption.
         + 
           (*destruct H0 as [T0].*)
           destruct_ms H2 T0 W0.
           pose proof (single_step_all T0 H3) as destroyme.
           ex_destruct3 destroyme.
           destruct destroyme as [MS sub].
           destruct_ms MS T1 WT1.
           eapply (IHWARok var3).
        - intros contra. apply sub, H1 in contra. contradiction. (*cool applying!!*)
          exists WT1. apply (inhabits T1).
 - destruct_ms H3 T3 WT3.
            inversion T3; subst.

          apply (inhabits (single_step_all T0 H3)).
eapply IHT2.
          (*garbage below*)
        inversion T; subst.
        exists W R. constructor. assumption.
        inversion H3; subst.
        exfalso. apply H1. apply in_eq.
        inversion H2.

       apply (in_eq H1). in H1. discriminate H1.
      eapply IHT2. (try reflexivity); try (apply WAR_Skip).
     apply WAR_Skip.

     
     apply H. apply (inhabits T2).
    intros contra. eapply or_intror in contra.
    apply in_or_app in contra. apply H1 in contra. contradiction.


(*garbage below*)
    applys H1 in (in_or_app contra).
      inversion H2. subst. eapply IHT2.
      assert (WAR_ins N0 W R l0 W' R')
    +

    inversion T1; subst.
    + inversion T2; subst; try (applys WAR_I; constructor).
    + applys WAR_I. apply H.

    destruct Cmid as [Annoying cmid].
      destruct Annoying as [nmid vmid].
      apply (IHT1 N nmid V vmid c' l).
     - assumption.
     - 
      apply (inhabits T1 ).
      

    remember H as Hwarins. clear HeqHwarins. eapply (IHT1) in H. apply H.
    destruct Cmid as [Annoying cmid]. destruct Annoying
                                                 as [nmid vmid]. apply (inhabits T1 ).
    inversion H0; subst.
       - applys WAR_I. apply H.
       - inversion H3; subst; try (applys WAR_I; constructor).
         + inversion H0; subst. applys WAR_I. apply H.
         + inversion H5; subst; try(applys WAR_I; constructor).
  + subst.


  inversion H0; subst.
  + exists W. exists R. assumption.
  + inversion H2. subst. inversion H3; subst; try (exists W R; applys WAR_I; constructor).
  - induction H.
    + inversion H2. subst. inversion H3. subst.
  - exists W R. applys WAR_I. apply H.
  - subst. inversion H5. subst. exists W R. applys WAR_I. constructor.


    destruct l. constructor.

    + exists W R. applys WAR_I. constructor.
  induction H.
  + inversion H0. subst.
  + unfold single_com in H2.
    induction c'.
  - induction l.
    + applys WAR_I.
    applys WAR_I.
    induction c. inversion H3; subst; exists W R; applys WAR_I; constructor.
    (*the existence is hacky here but I can't
                            figure out how to be smarter
                            w instantiations*)
    -  
    - applys WAR_Vol.

      inversion H3. subst.
    (try (apply WAR_I); constructor).
             eapply H. induction c'.
    - simpl.

  exists(locs_warvars (getwt Wr)). exists(locs_warvars (getrd Wr)).



Close Scope list_scope.
