Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From TLC Require Import LibTactics.
Import ListNotations.
From Semantics Require Import programs semantics algorithms lemmas. (*shouldn't have to import both of these*)

Open Scope list_scope.

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
       apply (eq_trans contra) in contra1.
       apply H1. assumption.
Qed.

Lemma wt_subst_fstwt: forall{C1 C2: context} {O: obseq} {W: the_write_stuff},
  trace_c C1 C2 O W ->
    incl (getfstwt W) (getwt W).
Proof. intros C1 C2 O W T. induction T.
       + simpl. apply (incl_refl []).
       + induction c;
           (try (simpl; apply (incl_refl [])));
           (try (unfold getfstwt; unfold getwt;
                 apply remove_subst)).
       - inversion s.
       - simpl. apply (incl_app_dbl IHT1
                                    (incl_tran
                                    (remove_subst _ _ _)
                                    IHT2)).
Qed.

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
Proof. intros. inversion H1. subst.
       apply (same_mem (CTrace_Empty (N1, V0, c0))
                       T); (try assumption).
       - simpl. intros contra. contradiction.
       - intros. simpl.
         assert (H6: not (In (loc_warvar l) (getdomain N0))) by
               apply (sub_disclude N0 N1 N2 l H H0 H5).
           apply H4 in H5. destruct H5. split. 
         + unfold Wt. apply ((wt_subst_fstwt T) l H5).
         + split.
             - unfold remove. unfold in_loc_b. rewrite filter_false.
                 apply H5.
             - intros contra. contradiction.
         + apply H6 in H5. contradiction.
Qed.

(*N0 is checkpointed variables*)
(*make ltac for destructing triples*)
Lemma trace_stops: forall {N N': nvmem} {V V': vmem}
                    {l: instruction} {c: command}
  {O: obseq} {W: the_write_stuff},
    trace_c (N, V, Ins l) (N', V', c) O W ->
    (c = Ins l) \/ (c = skip).
Proof.
  intros N N' V V' l c O W T. dependent induction T.
  + constructor.
  + reflexivity.
  + inversion c0; subst; try(right; reflexivity).
  + destruct Cmid as [Annoying cmid].
    destruct Annoying as [nmid vmid].
    assert (cmid = l \/ cmid = skip).
    {
      apply (IHT1 N nmid V vmid l cmid); reflexivity.
    }
  + inversion H; subst.
       -  eapply IHT2; reflexivity.
       - right.
         destruct (IHT2 nmid N' vmid V' skip c); (reflexivity || assumption).
  Qed.
Lemma ten: forall(N0 W R: warvars) (N N': nvmem) (V V': vmem)
            (O: obseq) (c c': command),
            WARok N0 W R c ->
            multi_step_c (N, V, c) (N', V', c') O ->
            not (In checkpoint O) ->
            exists(W' R': warvars), WARok N0 W' R' c'.
  intros. unfold multi_step_c in H0. destruct H0 as [Wr].
  induction H.
  + inversion H0 as [T]. dependent induction T.
  + exists W R. applys WAR_I. apply H.
  + inversion c; subst; try (exists W R; applys WAR_I; constructor).
  - destruct Cmid as [Annoying cmid].
      destruct Annoying as [nmid vmid].
    assert (Hcmid: cmid = Ins l \/ cmid = skip).
    apply (trace_stops T1).
    destruct Hcmid; subst.
    - eapply IHT2. apply H. apply (inhabits T2).
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
