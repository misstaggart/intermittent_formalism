Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From TLC Require Import LibTactics LibLogic.
Import ListNotations.
From Semantics Require Import programs semantics algorithms lemmas_1. (*shouldn't have to import both of these*)

Open Scope list_scope.
Open Scope type_scope.

(*ltac*)
Ltac destruct4r H L1 L2 L3 L4 := destruct H as [L1 rest];
         destruct rest as [L2 rest];
         destruct rest as [L3 L4]. 

Ltac destruct3 Cmid nmid vmid cmid:=
           destruct Cmid as [Annoying cmid]; destruct Annoying as [nmid vmid].

Ltac ex_destruct3 H := destruct H as [var1 Annoying]; destruct Annoying as [var2 Annoying1];
                       destruct Annoying1 as [var3 H].

Ltac destruct_ms M T WT := destruct M as [WT neverseen]; destruct neverseen as [T].

Ltac generalize_5 N N' V V' O := generalize dependent N;
                               generalize dependent N';
                               generalize dependent V;
                               generalize dependent V';
                               generalize dependent O.



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

Lemma wt_subst_fstwt: forall{C1 C2: context} {O: obseq} {W: the_write_stuff},
  trace_c C1 C2 O W ->
    incl (getfstwt W) (getwt W).
Proof. intros C1 C2 O W T. induction T.
       + simpl. apply (incl_refl []).
       + induction c;
           (try (simpl; apply (incl_refl [])));
           (try (unfold getfstwt; unfold getwt;
                 apply remove_subst)).
       - assumption.
       - simpl. apply (incl_app_dbl IHT1
                                    (incl_tran
                                    (remove_subst _ _ _)
                                    IHT2)).
Qed.

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
  + destruct3 Cmid nmid vmid cmid.
    assert (cmid = l \/ cmid = skip).
    {
      apply (IHT1 N nmid V vmid l cmid); reflexivity.
    }
  + inversion H; subst.
       -  eapply IHT2; reflexivity.
       - right.
         destruct (IHT2 nmid N' vmid V' skip c); (reflexivity || assumption).
Qed.

Lemma observe_checkpt: forall {N N': nvmem} {V V': vmem}
                     {c c': command} {w: warvars}
                    {O: obseq} {W: the_write_stuff},
    trace_c (N, V, (incheckpoint w ;; c)) (N', V', c') O W ->
    c' = (incheckpoint w ;; c) \/ In checkpoint O.
  intros N N' V V' c c' w O W T.
  dependent induction T.
  + left. reflexivity.
  +  inversion c0; subst. right.  apply(in_eq checkpoint).
     inversion H10.
  + destruct3 Cmid nmid vmid cmid. destruct (IHT1 N nmid V vmid c cmid w); subst; try reflexivity.
      - destruct (IHT2 nmid N' vmid V' c c' w); subst; try reflexivity;
          [left; reflexivity | right; apply (in_app_r H)].
      - right. apply (in_app_l H).
Qed.

(*tidy up this theorem statement a little*)
Lemma negNVandV: forall(x : smallvar), not(isNV x /\ isV x).
Proof. intros. unfold isNV. unfold isV.
       unfold isNV_b. unfold isV_b.
       destruct x as [x p]. simpl. induction x; (try destruct q); intros contra;
                                         destruct contra as [H1 H2];
      (discriminate H1 || discriminate H2).
Qed.
(*weird that destruct works in the above but inversion does nothing
 ask arthur*)


(*ask arthur how to subtypes!*)
Lemma el_arrayind: forall{e0 e1: el} {a: array} {v: value},
    el_arrayind_eq e0 a v -> el_arrayind_eq e1 a v ->
    e0 = e1.
Proof. intros e0 e1 a v. intros.
       (*cut (val e0 == val e1).*)
       unfold el_arrayind_eq.
       unfold samearray.
       unfold samearray_b.
       unfold getarray.
Admitted.
(*plan is to use these but then I would have to set up
 equality type for expressions;
 going to wait to ask if there is an easier way*)
Check proj1_sig.
Check val_eqP.
Check elimT.

Lemma determinism_e: forall{N: nvmem} {V: vmem} {e: exp} {r1 r2: readobs} {v1 v2: value},
    eeval N V e r1 v1 ->
    eeval N V e r2 v2 ->
    r1 = r2 /\ v1 = v2.
Proof. intros. induction H.
       + inversion H0.
       - subst. split; reflexivity.
         - subst. 
Admitted.
(*waiting till I decide whether or not I'm using the subtypes*)


  (*ask Arthur why the other version acted
 weirdly with inversion*)

Lemma determinism: forall{C1 C2 C3: context} {O1 O2: obseq} {W1 W2: the_write_stuff},
    cceval_w C1 O1 C2 W1 ->
    cceval_w C1 O2 C3 W2 ->
    C2 = C3 /\ O1 = O2 /\ W1 = W2.
Proof. intros C1 C2 C3 O1 O2 W1 W2 cc1 cc2. destruct C1 as [blah c]. destruct blah as [N V].
       destruct3 C2 N2 V2 com2. 
       generalize dependent C3.
       generalize dependent O2.
       generalize dependent W2.
       induction cc1; intros; try (inversion cc2; subst; pose proof (determinism_e H H9); destruct H2; subst;
           try( split; [reflexivity | split; reflexivity]); try(exfalso; apply (negNVandV x); split; assumption)).
       + inversion cc2; subst; split; try (inversion H8); [reflexivity | (split; reflexivity)].
       +  inversion cc2; subst; pose proof (determinism_e H H11) as p. destruct p.
             subst.
             pose proof (el_arrayind H13 H1). subst.
             pose proof (determinism_e H12 H0) as p. destruct p. subst. split;
      [reflexivity | split; reflexivity].
      + inversion cc2; subst; split; (try inversion H8);
      [reflexivity | split; reflexivity]. 
      + inversion cc2; subst.
       - exfalso. apply (H w). reflexivity.
       - contradiction.
       - cut ( N' = N'0  /\ V' = V'0 /\
              [o] = [o0] /\ W = W2).
         + intros H13. destruct4r H13 L1 L2 L3 L4. inversion L3. subst.
         split; [reflexivity | split; reflexivity].
         + cut ((N', V', Ins skip) = (N'0, V'0, Ins skip) /\
                [o] = [o0] /\ W = W2).
           intros Hnew. destruct Hnew as [L1 rest].
           inversion L1. subst. split; [reflexivity |
                                        split; try reflexivity; try assumption].
           apply (IHcc1 W2 [o0] (N'0, V'0, Ins skip) H10).
         + inversion cc2; subst; pose proof (determinism_e H H8) as p; destruct p; subst;
             try (split; [reflexivity| split; reflexivity]); inversion H1.
        + inversion cc2; subst; pose proof (determinism_e H H8) as p; destruct p; subst;
             try (split; [reflexivity| split; reflexivity]); inversion H1.
Qed.


(*concern: the theorem below is not true for programs with io
 but then again neither is lemma 10*)
Lemma single_step_all: forall{C1 Cmid C3: context} 
                    {Obig: obseq} {Wbig: the_write_stuff},
    trace_c C1 C3 Obig Wbig ->
    Obig <> [] ->
    (exists (O1: obseq) (W1: the_write_stuff), cceval_w C1 O1 Cmid W1) ->
    exists(Wrest: the_write_stuff) (Orest: obseq), inhabited (trace_c Cmid C3 Orest Wrest)
/\ incl Orest Obig
.
  intros C1 Cmid C3 Obig Wbig T OH c.
  generalize dependent c.
  generalize dependent Cmid.
  remember T as Tsaved. clear HeqTsaved. (*make ltac for this*)
  dependent induction T; intros.
  + exfalso. apply OH. reflexivity.
  + destruct c0 as [O1 rest]. destruct rest as [W1 c0]. exists emptysets (nil: obseq).
    constructor. cut (C2 = Cmid).
    - intros Hmid. subst. constructor. apply CTrace_Empty.
    - eapply determinism. apply c. apply c0.
    - apply empty_sub.
      + assert (Tfirst: exists Wrest Orest, inhabited (trace_c Cmid0 Cmid Orest Wrest)
                       /\ incl Orest O1                           
               ) by (apply IHT1; try assumption).
        destruct Tfirst as [Wrest rest]. destruct rest as [Orest T0mid]. destruct T0mid as [T0mid incl1].
        destruct T0mid as [T0mid].
   exists (append_write Wrest W2) (Orest ++ O2). destruct Orest; split; (try constructor).
    - simpl. apply empty_trace in T0mid. destruct T0mid as [l r].
      subst. rewrite append_write_empty_l. assumption.
      reflexivity.
    - simpl. apply incl_appr. apply incl_refl.
    - eapply CTrace_App. apply T0mid. intros contra. inversion contra.
      assumption. assumption.
    - eapply incl_app_dbl. assumption. apply incl_refl.
Qed.

Lemma trace_steps: forall{C1 C3: context} 
                    {Obig: obseq} {Wbig: the_write_stuff},
    trace_c C1 C3 Obig Wbig ->
    Obig <> [] ->
    exists(Csmall: context) (Osmall: obseq) (Wsmall: the_write_stuff),
      cceval_w C1 Osmall Csmall Wsmall.
Proof. intros C1 C3 Obig Wbig T H. induction T.
       + exfalso. apply H. reflexivity.
       + exists C2 O W. assumption. apply (IHT1 n).
Qed.

Lemma seq_step: forall{N: nvmem} {V: vmem} {l: instruction} {c: command}
    {C2: context} {O: obseq} {W: the_write_stuff},
    cceval_w (N, V, l;;c) O C2 W ->  c = (getcom C2).
Proof.
  intros. inversion H; subst; simpl; reflexivity.
Qed.


Lemma if_step: forall{N: nvmem} {V: vmem} {e: exp} {c1 c2: command}
    {C2: context} {O: obseq} {W: the_write_stuff},
    cceval_w (N, V, (TEST e THEN c1 ELSE c2)) O C2 W ->  c1 = (getcom C2)
\/ c2 = (getcom C2).
  intros. inversion H; subst; simpl;( (left; reflexivity) || (right; reflexivity)).
Qed.



(*lemmas from paper*)

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



(*Concern: bottom three cases are essentially the same reasoning but with slight differences;
 unsure how to automate
 maybe remembering c so that I can use c instead of the specific form of c?*)
(*N0 is checkpointed variables*)
Lemma ten: forall(N0 W R: warvars) (N N': nvmem) (V V': vmem)
            (O: obseq) (c c': command),
            WARok N0 W R c ->
            multi_step_c (N, V, c) (N', V', c') O ->
            not (In checkpoint O) ->
            exists(W' R': warvars), WARok N0 W' R' c' /\
                               incl ((locs_warvars (Rd T)) ++ R) R' .
  intros.
  generalize_5 N N' V V' O.
  remember H as warok. clear Heqwarok.
  induction H; intros.
  +  destruct_ms H0 T Wr.
    cut (c' = Ins l \/ c' = skip).
  - intros Hdis. destruct Hdis as [Hins | Hskip]; subst; exists W R.
    + apply warok.
    + eapply WAR_I. apply WAR_Skip.
  - apply trace_stops in T. assumption.
  + intros. destruct_ms H0 T WT. remember T as T1. clear HeqT1.
        apply observe_checkpt in T. destruct T as [eq | contra].
    - subst. exists W R. apply warok.
    - apply H1 in contra. contradiction.
+ destruct_ms H2 T WT; subst.
      assert (Dis: (l ;; c) = c' \/ not ((l;;c) = c'))
          by (apply classic). destruct Dis.
    - subst. exists W R. assumption.
    - assert(exists(Csmall: context) (Osmall: obseq) (Wsmall: the_write_stuff),
                  cceval_w (N0, V, l;;c) Osmall Csmall Wsmall).
      + eapply trace_steps. apply T. intros contra. subst.
        apply empty_trace in T. destruct T as [H3 H4].
        inversion H3. apply H2. assumption. reflexivity.
        destruct H3 as [Csmall rest].
        destruct rest as [Osmall rest]. destruct rest as [Wsmall c1].
        remember Csmall as Csmall1.
        destruct Csmall as [blah1 smallcom]. destruct blah1 as [Nsmall Vsmall].
        remember c1 as c11. clear Heqc11.
        apply seq_step in c11. unfold getcom in c11. subst.
        cut (exists(Wrest: the_write_stuff) (Orest: obseq), inhabited
                                                         (trace_c
                                                            (Nsmall, Vsmall, smallcom)
                                                            (N', V', c')
                                                            Orest Wrest)
                                                       /\ incl Orest O).
        intros bigH. destruct bigH as [Wrest blah]. destruct blah as [Orest inhab]. destruct inhab as [inhab inclO].
        assert (Hmulti: multi_step_c
              (Nsmall, Vsmall, smallcom)
              (N', V', c') Orest) by (exists Wrest; assumption).
        eapply IHWARok; try assumption.
        + intros contra. apply inclO in contra. apply H1 in contra. contradiction.
          apply Hmulti.                          
        + eapply single_step_all. apply T.
      - intros contra. apply (empty_trace T) in contra. destruct contra as
            [contra blah]. inversion contra. subst. apply H2. reflexivity.
        exists Osmall Wsmall. assumption.
 + destruct_ms H3 T WT; subst. remember (TEST e THEN c1 ELSE c2) as bigif.
   assert (Dis: bigif = c' \/
                bigif <> c')
     by (apply classic). destruct Dis.
      - subst. exists W R. apply warok.
      - assert(exists(Csmall: context) (Osmall: obseq) (Wsmall: the_write_stuff),
                  cceval_w (N0, V, bigif) Osmall Csmall Wsmall).
        + eapply trace_steps. apply T. intros contra. subst.
          apply empty_trace in T. destruct T as [H10 H11]. inversion H10. apply H3. assumption. reflexivity.
        destruct H4 as [Csmall rest].
        destruct rest as [Osmall rest]. destruct rest as [Wsmall cc].
        remember Csmall as Csmall1.
        destruct Csmall as [blah1 smallcom]. destruct blah1 as [Nsmall Vsmall].
        remember cc as cc1. clear Heqcc1. rewrite Heqbigif in cc1.
        apply if_step in cc1. destruct cc1 as [tcase | fcase].
        - unfold getcom in tcase. subst.
        cut (exists(Wrest: the_write_stuff) (Orest: obseq), inhabited
                                                         (trace_c
                                                            (Nsmall, Vsmall, smallcom)
                                                            (N', V', c')
                                                            Orest Wrest)
                                                       /\ incl Orest O).
        intros bigH. destruct bigH as [Wrest blah]. destruct blah as [Orest inhab]. destruct inhab as [inhab inclO].
        assert (Hmulti: multi_step_c
              (Nsmall, Vsmall, smallcom)
              (N', V', c') Orest) by (exists Wrest; assumption).
        eapply IHWARok1; try assumption.
        + intros contra. apply inclO in contra. apply H2 in contra. contradiction.
          apply Hmulti.                          
        + eapply single_step_all. apply T.
      - intros contra. apply (empty_trace T) in contra. destruct contra as
            [contra blah]. inversion contra. subst. apply H3. reflexivity.
        exists Osmall Wsmall. assumption.
      - unfold getcom in fcase. subst.
        cut (exists(Wrest: the_write_stuff) (Orest: obseq), inhabited
                                                         (trace_c
                                                            (Nsmall, Vsmall, smallcom)
                                                            (N', V', c')
                                                            Orest Wrest)
                                                       /\ incl Orest O).
        intros bigH. destruct bigH as [Wrest blah]. destruct blah as [Orest inhab]. destruct inhab as [inhab inclO].
        assert (Hmulti: multi_step_c
              (Nsmall, Vsmall, smallcom)
              (N', V', c') Orest) by (exists Wrest; assumption).
        eapply IHWARok2; try assumption.
        + intros contra. apply inclO in contra. apply H2 in contra. contradiction.
          apply Hmulti.                          
        + eapply single_step_all. apply T.
      - intros contra. apply (empty_trace T) in contra. destruct contra as
            [contra blah]. inversion contra. subst. apply H3. reflexivity.
        exists Osmall Wsmall. assumption.
Qed.


Lemma thirteen: 


Close Scope list_scope.
