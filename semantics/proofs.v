Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Strings.String Program Logic.FunctionalExtensionality.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq fintype ssrnat ssrfun.
From TLC Require Import LibTactics LibLogic.
From Semantics Require Export programs semantics algorithms lemmas_1
lemmas_0. (*shouldn't have to import both of these*)

Open Scope type_scope.


(*lemmas for the lemmas; not in paper*)
Lemma sub_disclude: forall(N0 N1 N2: nvmem) (l: loc),
                     subset_nvm N0 N1 ->
                     subset_nvm N0 N2 ->
                     not ((getmap N1) l = (getmap N2) l)
                     -> not (l \in (getdomain N0)).
Proof. intros. intros contra. unfold subset_nvm in H. destruct H.
       remember contra as contra1. clear Heqcontra1.
       apply H2 in contra.
       unfold subset_nvm in H0. destruct H0. apply H3 in contra1.
       symmetry in contra.
       apply (eq_trans _ _ _ contra) in contra1.
       apply H1. assumption.
Qed.


Lemma wt_subst_fstwt: forall{C1 C2: context} {O: obseq} {W: the_write_stuff},
      (* pose proof (cceval_to_rd_sv H H5). *)
  trace_c C1 C2 O W ->
    subseq (getfstwt W) (getwt W).
Proof. intros C1 C2 O W T. induction T.
       + auto.
       + induction H; auto; try (unfold getfstwt; unfold getwt;
         apply filter_subseq).
       - simpl. apply (cat_subseq (subseq_trans
                                    (filter_subseq _ _ )
                                    IHT2) IHT1
                                    ).
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
  + inversion H; subst; try(right; reflexivity).
  + destruct3 Cmid nmid vmid cmid.
    assert (cmid = l \/ cmid = skip).
    {
      apply (IHT1 N nmid V vmid l cmid); reflexivity.
    }
  + inversion H1; subst.
       -  eapply IHT2; reflexivity.
       - right.
         destruct (IHT2 nmid N' vmid V' skip c); (reflexivity || assumption).
Qed.

Lemma observe_checkpt: forall {N N': nvmem} {V V': vmem}
                     {c c': command} {w: warvars}
                    {O: obseq} {W: the_write_stuff},
    trace_c (N, V, (incheckpoint w ;; c)) (N', V', c') O W ->
    c' = (incheckpoint w ;; c) \/ checkpoint \in O.
  intros N N' V V' c c' w O W T.
  dependent induction T.
  + left. reflexivity.
  +  inversion H; subst. right.  apply(mem_head checkpoint).
     inversion H11.
  + destruct3 Cmid nmid vmid cmid. destruct (IHT1 N nmid V vmid c cmid w); subst; try reflexivity.
      - destruct (IHT2 nmid N' vmid V' c c' w); subst; try reflexivity;
          [left; reflexivity | right; apply (in_app_r H1)].
      - right. apply (in_app_l H1).
Qed.

Lemma observe_rb:forall {C0 C1: context} {N N': nvmem} {V V': vmem}
                     {c': command} 
                    {O: obseq} {W: the_write_stuff},
    trace_i (C0, N, V, (Ins inreboot)) (C1, N', V', c') O W ->
    c' = (Ins inreboot) \/ reboot \in O.
  Admitted.


Lemma negNVandV: forall(x : smallvar), isNV x -> not (isV x).
Proof. unfold isNV. unfold isV.
       unfold isNV_b. unfold isV_b.
       move => [s v]. destruct v; auto. (*ask arthur do both destructs at once?*)
Qed.

(*ask arthur difference between val and sval
 i think it's to do with one being an equality type
 and the other not?*)
Set Printing Coercions.

Lemma equal_index_works: forall{e0 e1: el_loc} {a: array} {v: value},
    equal_index e0 a v -> equal_index e1 a v ->
    e0 = e1.
        intros. unfold equal_index in H.
        destruct e0.
        destruct e1.
        destruct v eqn: veq; try (exfalso; assumption).
        unfold equal_index in H0.
        destruct H, H0.
        subst.
        cut (i = i0).
        intros. by subst.
          by apply ord_inj.
Qed.

Lemma equal_index_arr: forall{a0 a: array} {i: 'I_(get_length a0)}
                           {v: value},
    equal_index (El a0 i) a v -> a0 = a.
        intros. unfold equal_index in H.
        destruct v eqn: veq; try (exfalso; assumption).
        destruct H. assumption.
Qed.

Lemma gen_locs_works: forall{a a0: array} {i: 'I_(get_length a0)}
                           {v: value},
    equal_index (El a0 i) a v -> (inr (El a0 i)) \in (generate_locs a).
  intros. apply equal_index_arr in H. subst.
  unfold generate_locs. unfold index_loc.
  destruct a.
  simpl in i.
  simpl.  intros.
  Check inE.
  apply (map_f (fun i0 => inr (El (Array s l) i0)))
  .
  by rewrite mem_enum.
Qed.
  (*suffices: 
  rewrite <- inE.
  induction i.
    intros H.
  destruct a. simpl.
  simpl in H.
  injection.
  unfold enum in H.
  unfold in_mem.
  unfold in_mem in H.
  unfold pred_of_mem.
  unfold mem_seq_predType.
  apply H.

  unfold equal_index in H.
        destruct v eqn: veq; try (exfalso; assumption).
        destruct H. assumption.
Qed.*)

(*consider using map cat for the app thing*)
Lemma determinism_e: forall{N: nvmem} {V: vmem} {e: exp} {r1 r2: readobs} {v1 v2: value},
    eeval N V e r1 v1 ->
    eeval N V e r2 v2 ->
    r1 = r2 /\ v1 = v2.
Proof. intros N V e r1 r2 v1 v2 H. move: r2 v2. (*ask arthur; does GD not do what
                                                      I want here bc it's a prop?*)
       dependent induction H.
       + intros r2 v2 H2. dependent induction H2. split; reflexivity.
       + intros r0 v0 H2.
         dependent induction H2.
         appldis IHeeval1 H2_.
         appldis IHeeval2 H2_0.
         subst. split; reflexivity.
       + intros r2 v2 H2. inversion H2; subst.
         - split; reflexivity.
         - exfalso. apply (negNVandV x); assumption.
       + intros r2 v2 H2. inversion H2; subst.
         - exfalso. apply (negNVandV x); assumption.
         - split; reflexivity.
       + intros r2 v2 H2nd. inversion H2nd. subst.
         appldis IHeeval H5. subst.
         cut (element = element0).
        intros. subst.
        split; reflexivity.
        apply (equal_index_works H1 H9).
        Qed.

(*I try to use the same names in all branches for automation
 and it tells me "name" already used!*)
Lemma determinism_c: forall{C1 C2 C3: context} {O1 O2: obseq} {W1 W2: the_write_stuff},
    cceval_w C1 O1 C2 W1 ->
    cceval_w C1 O2 C3 W2 ->
    C2 = C3 /\ O1 = O2 /\ W1 = W2.
Proof. intros C1 C2 C3 O1 O2 W1 W2 cc1 cc2. destruct C1 as [blah c]. destruct blah as [N V].
       destruct3 C2 N2 V2 com2. 
       generalize dependent C3.
       generalize dependent O2.
       generalize dependent W2.
 induction cc1; intros; inversion cc2 as
           [| | | | | N20 N2' V20 V2' l20 c20 o20 W20| | ]
       (*only put vars for 1 branch but all changed? start here do not ask
        arthur this*)
       ; subst; try (exfalso; eapply (negNVandV x); assumption);
         try (destruct (determinism_e H H2); subst);
         try (exfalso; apply (H w); reflexivity);
         try (exfalso; (apply H1 || apply H0); reflexivity);
         try (destruct (determinism_e H H0); inversion H2);
         try (apply IHcc1 in H3; destruct H3 as
             [onee rest]; destruct rest as [two threee];
              inversion onee; inversion two);
         try( 
 destruct (determinism_e H3 H); destruct (determinism_e H4 H0); subst;
   pose proof (equal_index_works H1 H5));
         try (subst;
              split; [reflexivity | (split; reflexivity)]).
Qed.


(*concern: the theorem below is not true for programs with io
 but then again neither is lemma 10*)
Lemma single_step_all: forall{C1 Cmid C3: context} 
                    {Obig: obseq} {Wbig: the_write_stuff},
    trace_c C1 C3 Obig Wbig ->
    Obig <> [::] ->
    (exists (O1: obseq) (W1: the_write_stuff), cceval_w C1 O1 Cmid W1) ->
    exists(Wrest: the_write_stuff) (Orest: obseq), trace_c Cmid C3 Orest Wrest
/\ subseq Orest Obig
.
  intros C1 Cmid C3 Obig Wbig T OH c.
  generalize dependent c.
  generalize dependent Cmid.
  remember T as Tsaved. clear HeqTsaved. (*make ltac for this*)
  dependent induction T; intros.
  + exfalso. apply OH. reflexivity.
  + destruct c as [O1 rest]. destruct rest as [W1 c0]. exists emptysets (nil: obseq).
    constructor. cut (C2 = Cmid).
    - intros Hmid. subst. constructor. 
    - eapply determinism_c. apply H. apply c0.
    - apply sub0seq.
      + assert (Tfirst: exists Wrest Orest,  (trace_c Cmid0 Cmid Orest Wrest)
                       /\ subseq Orest O1                           
               ) by (apply IHT1; try assumption).
        destruct Tfirst as [Wrest rest]. destruct rest as [Orest T0mid]. destruct T0mid as [T0mid incl1].
        exists (append_write Wrest W2) (Orest ++ O2). destruct Orest; split.
    - simpl. apply empty_trace in T0mid. destruct T0mid.
      subst. rewrite append_write_empty_l; auto.
      reflexivity.
    - simpl. apply suffix_subseq.
    - eapply CTrace_App. apply T0mid. intros contra. inversion contra.
      assumption. assumption.
    - eapply cat_subseq. assumption. apply subseq_refl.
Qed.

Lemma trace_steps: forall{C1 C3: context} 
                    {Obig: obseq} {Wbig: the_write_stuff},
    trace_c C1 C3 Obig Wbig ->
    Obig <> [::] ->
    exists(Csmall: context) (Osmall: obseq) (Wsmall: the_write_stuff),
      cceval_w C1 Osmall Csmall Wsmall.
Proof. intros C1 C3 Obig Wbig T H. induction T.
       + exfalso. apply H. reflexivity.
       + exists C2 O W. assumption. apply (IHT1 H0).
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
    DINO_ins N W R l N' W' R' -> subseq N N'.
Proof. intros. induction H; try((try apply subseq_tl); apply (subseq_refl N)).
       apply (subseq_cons N (inl x)).
       apply suffix_subseq.
Qed.


Lemma onePointtwo: forall(N N' W R: warvars) (c c': command),
    DINO N W R c c' N' -> subseq N N'.
Proof. intros. induction H; try(apply onePointone in H); try apply (incl_refl N); try assumption.
       -  apply (subseq_trans H IHDINO).
       - apply subseq_app_rr. assumption. apply subseq_refl.
 Qed.

Lemma Two: forall(N N' W W' R R' N1: warvars) (l: instruction),
    DINO_ins N W R l N' W' R' -> subseq N' N1 -> WAR_ins N1 W R l W' R'.
  intros. induction H; try ((constructor; assumption) || (apply War_noRd; assumption)).
            (apply WAR_Checkpointed);
              (repeat assumption).
            move / in_subseq : H0.
            intros.
            apply (H0 (inl x) (mem_head (inl x) N)).
            apply WAR_Checkpointed_Arr; try assumption. apply (subseq_app_l H0).

Qed.


Theorem DINO_WAR_correct: forall(N W R N': warvars) (c c': command),
    DINO N W R c c' N' -> (forall(N1: warvars), subseq N' N1 -> WARok N1 W R c').
  intros N W R c c' N' H. induction H; intros N0 Hincl.
  - eapply WAR_I. applys Two H Hincl.
  - eapply WAR_Seq. applys Two H. apply onePointtwo in H0.
    apply (subseq_trans H0 Hincl).
    apply (IHDINO N0 Hincl).
  - eapply WAR_If; (try eassumption);
      ((apply IHDINO1; apply subseq_app_l in Hincl)
       || (apply IHDINO2; apply subseq_app_r in Hincl)); assumption.
  - intros. apply WAR_CP. apply IHDINO. apply (subseq_refl N').
Qed.


Lemma eight: forall{N0 N1 N2: nvmem} {V0: vmem} {c0: command},
              (subset_nvm N0 N1) ->
              (subset_nvm N0 N2) ->
              current_init_pt N0 V0 c0 N1 N1 N2 ->
              same_pt N1 V0 c0 c0 N1 N2.
Proof. intros. inversion H1. subst.
 apply (same_mem
                (CTrace_Empty (N1, V0, c0))
                T); auto. 
       - intros l Hl. simpl.
        assert (H6: not (l \in (getdomain N0))) by
               apply (sub_disclude N0 N1 N2 l H H0 Hl).
         (*try appldis here*)
         apply H5 in Hl. destruct Hl.
         split.
         + apply (in_subseq (wt_subst_fstwt T) H7).
         + split. unfold remove. simpl.
           rewrite filter_predT. rewrite cats0. assumption.
             - intros contra. discriminate contra. 
         + apply H6 in H7. contradiction.
Qed.



(*Concern: bottom three cases are essentially the same reasoning but with slight differences;
 unsure how to automate
 maybe remembering c so that I can use c instead of the specific form of c?*)
(*N0 is checkpointed variables*)
Lemma ten: forall(N0 W R: warvars) (N N': nvmem) (V V': vmem)
            (O: obseq) (c c': command),
            WARok N0 W R c ->
            multi_step_c (N, V, c) (N', V', c') O ->
            not (checkpoint \in O) ->
            exists(W' R': warvars), WARok N0 W' R' c'.
   intros.
  generalize_5 N N' V V' O.
  remember H as warok. clear Heqwarok.
  induction H; intros.
  +  destruct H0 as [ Wr T ].
    cut (c' = Ins l \/ c' = skip).
  - intros Hdis. destruct Hdis as [Hins | Hskip]; subst; exists W R.
    + apply warok.
    + eapply WAR_I. apply WAR_Skip.
  - apply trace_stops in T. assumption.
  + intros. destruct H0 as [ WT T ]. remember T as T1. clear HeqT1.
        apply observe_checkpt in T. destruct T as [eq | contra].
    - subst. exists W R. apply warok.
    - apply H1 in contra. contradiction.
+ destruct H2 as [ WT T ]; subst.
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
        cut (exists(Wrest: the_write_stuff) (Orest: obseq), 
                                                         trace_c
                                                            (Nsmall, Vsmall, smallcom)
                                                            (N', V', c')
                                                            Orest Wrest
                                                       /\ subseq Orest O).
        move => [Wrest [ Orest [Tsmall inclO] ] ].
        assert (Hmulti: multi_step_c
              (Nsmall, Vsmall, smallcom)
              (N', V', c') Orest) by (exists Wrest; assumption).
        eapply IHWARok; try assumption.
        + intros contra. apply (in_subseq inclO) in contra. apply H1 in contra. contradiction.
          apply Hmulti.                          
        + eapply single_step_all. apply T.
      - intros contra. apply (empty_trace T) in contra. destruct contra as
            [contra blah]. inversion contra. subst. apply H2. reflexivity.
        exists Osmall Wsmall. assumption.
 + destruct H3 as [WT T]; subst. remember (TEST e THEN c1 ELSE c2) as bigif.
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
        cut (exists(Wrest: the_write_stuff) (Orest: obseq), 
                                                         (trace_c
                                                            (Nsmall, Vsmall, smallcom)
                                                            (N', V', c')
                                                            Orest Wrest)
                                                       /\ subseq Orest O).
        move => [Wrest [ Orest [Tsmall inclO] ] ].
        assert (Hmulti: multi_step_c
              (Nsmall, Vsmall, smallcom)
              (N', V', c') Orest) by (exists Wrest; assumption).
        eapply IHWARok1; try assumption.
        + intros contra. apply (in_subseq inclO) in contra. apply H2 in contra. contradiction.
          apply Hmulti.                          
        + eapply single_step_all. apply T.
      - intros contra. apply (empty_trace T) in contra. destruct contra as
            [contra blah]. inversion contra. subst. apply H3. reflexivity.
        exists Osmall Wsmall. assumption.
      - unfold getcom in fcase. subst.
        cut (exists(Wrest: the_write_stuff) (Orest: obseq), 
                                                         (trace_c
                                                            (Nsmall, Vsmall, smallcom)
                                                            (N', V', c')
                                                            Orest Wrest)
                                                       /\ subseq Orest O).
        move => [Wrest [ Orest [Tsmall inclO] ] ].
        assert (Hmulti: multi_step_c
              (Nsmall, Vsmall, smallcom)
              (N', V', c') Orest) by (exists Wrest; assumption).
        eapply IHWARok2; try assumption.
        + intros contra. apply (in_subseq inclO) in contra. apply H2 in contra. contradiction.
          apply Hmulti.                          
        + eapply single_step_all. apply T.
      - intros contra. apply (empty_trace T) in contra. destruct contra as
            [contra blah]. inversion contra. subst. apply H3. reflexivity.
        exists Osmall Wsmall. assumption.
Qed.

(*if trace from N1,c  to CP
 then trace from N1' U! N0, c to CP
 and indeed should be the SAME cp
with same memories?
yes as if diff in one of the mems, that diff came from a first accessed (in c)
diff between N1 and (N1' U! N0). this diff is x. 
at the start.
case: x is not in CP.
then, N1(x) != N1'(x). Since N1 --> N1' while doing c!,
x was modified on the way to N1' while executing c.
N1' = (N1 with x --> e).
If x was read from before this point while executing c, then x would be in the CP by warok.
So, x was not read from.
So, when going the second time around from c, N1' does x --> e.
Since x is the first diff

Moreover, the expression x := e that x was assigned to must be equal in both cases, since
N1 and (N1' U! N0) have been equal up until x  

and that first diff existed between _whichever one_ and N2...not true, maybe theyre ALL different
which means either it's a FW
or in the CP ....but N1 isn't updated w a CP.... need subset relation?
 but I don't need that just yet
but i do need to show that the write sets are the same
easiest way to do that might be to show everything the same?*)

(*ask arthur is this supported by finite domain
 type*)
Lemma update_sub: forall{N0 N1: nvmem},
    subset_nvm N0 N1 ->
    (N0 U! N1) = N1.
  intros. destruct N0, N1. unfold updatemaps.
  Admitted.
   (* need functionalextensionality here
     also need to remove duplicates from the appending
     so that this actually holds
     only used in 12.1 so not gonna worry about it for now
 i think the strat is to not use nodups and isntead do
 ++ (remove D1 D0) removing D1 from D0 before appending*)

Lemma sub_update: forall(N0 N1: nvmem),
    subset_nvm N0 (N0 U! N1).
  intros.
  destruct N0, N1.
  unfold subset_nvm. split.
  simpl. apply prefix_subseq.
  intros. simpl. by rewrite H.
  Qed.

(*ask arthur how does inversion not cover this*)
Lemma stupid: forall (c: command) (l: instruction),
    c <> (l ;; c).
  move => c w contra.
  induction c; inversion contra.
    by apply IHc.
Qed.


(*the two below are taken for granted by the "configurations always make progress"
 assumption, admitting it now, intend to fix it later*)

(*termination case*)
Lemma twelve00: forall(N0 N1 N1' NT: nvmem) (V V' VT: vmem) (c c': command) (O1 OT: obseq)
  (WT: the_write_stuff),
   multi_step_i ((N0, V, c), N1, V, c) ((N0, V, c), N1', V', c') O1
      -> (checkpoint \notin O1)
      -> WARok (getdomain N0) [::] [::] c
      -> subset_nvm N0 N1
      -> inhabited (trace_c (N1, V, c) (NT, VT, Ins skip) OT WT)
      -> (checkpoint \notin OT)
      -> trace_c ((N0 U! N1'), V, c) (NT, VT, Ins skip) OT WT.
Admitted.

(*checkpoint case*)
Lemma twelve01: forall(N0 N1 N1' NCP: nvmem) (V V' VCP: vmem) (c c' cCP: command) (w: warvars) (O1 OCP: obseq)
  (WCP: the_write_stuff),
   multi_step_i ((N0, V, c), N1, V, c) ((N0, V, c), N1', V', c') O1
      -> (checkpoint \notin O1)
      -> WARok (getdomain N0) [::] [::] c
      -> subset_nvm N0 N1
      -> trace_c (N1, V, c) (NCP, VCP, (incheckpoint w);; cCP) OCP WCP
      -> (checkpoint \notin OCP)
      -> trace_c ((N0 U! N1'), V, c) (NCP, VCP, (incheckpoint w);; cCP) OCP WCP.
  (*intros. rename H3 into T.
  destruct_ms H Ti WTi.
  dependent induction Ti. (*makes a diff here w remembering that N1 and N1' are the same*)
  + rewrite (update_sub H2).  assumption.
  + dependent induction i.
     - rewrite (update_sub H2). assumption.
     - repeat rewrite (update_sub H2).  assumption. 
     - exfalso. eapply stupid in x. contradiction.
     - 
       above might be a little broken bc you changed from type
        to prop w/o checking*)
       (*x has been written to
  unfold multi_step_c in H.
  destruct H.*)

Admitted.

Lemma dom_gets_bigger_rb: forall(N0 N1: nvmem),
    subseq (getdomain N1) (getdomain (N0 U! N1)).
  move => [m0 d0] [m1 d1]. simpl. apply suffix_subseq.
  Qed.

Lemma dom_gets_bigger: forall{N1 N1': nvmem} {V V': vmem} {k0 k1: context}
                        {c c': command} {O: obseq},
      multi_step_i (k0, N1, V, c) (k1, N1', V', c') O ->
   subseq (getdomain N1) (getdomain N1').
  intros. destruct H as [w T].
  dependent induction T.
  apply subseq_refl.
  dependent induction H; try (apply subseq_refl); try
                                                    apply dom_gets_bigger_rb.
  destruct N1. unfold updateNV_sv. unfold getdomain.
 apply (subseq_cons D (inl x)). 
  destruct N1. unfold updateNV_arr. unfold getdomain.
  apply (suffix_subseq (generate_locs a) D).
  eapply IHiceval_w; (try reflexivity).
  destruct Cmid as [ [ [ Kmid Nmid ] Vmid ] cmid].
  eapply subseq_trans; [eapply IHT1 | eapply IHT2]; try reflexivity.
Qed.

Lemma updateone_sv: forall{N: nvmem} {x: smallvar} {v: value}
             {l: loc},
    not (((getmap (updateNV_sv N x v)) l) = ((getmap N) l) ) ->
               (l = (inl x)).
  intros.
  destruct (l == inl x) eqn: beq.
  apply/ eqP : beq.
  destruct N as [M D].
  unfold updateNV_sv in H.
  simpl in H.
  unfold updatemap in H.
  rewrite beq in H.
  exfalso. by apply H. 
  Qed.

Lemma updateone_arr: forall{N: nvmem} {a: array} {v: value}
             {i: el_loc} {l: loc},
    not (((getmap (updateNV_arr N i a v)) l) = ((getmap N) l) ) ->
               (l = (inr i)).
  intros.
  destruct (l == inr i) eqn: beq.
  apply/ eqP : beq.
  destruct N as [M D].
  unfold updateNV_arr in H.
  simpl in H.
  unfold updatemap in H.
  rewrite beq in H.
  exfalso. by apply H. 
  Qed.

Lemma update_one: forall{N N0 Nend: nvmem} {V V0 Vend: vmem} {c c0 cend: command} {O: obseq} {W: the_write_stuff}
  {l: loc},
    iceval_w ((N0, V0, c0), N, V, c) O ((N0, V0, c0), Nend, Vend, cend) W ->
    (getmap N) l <> (getmap Nend) l ->
    reboot \notin O ->
    l \in (getwt W).
  intros.
  dependent induction H; try (exfalso; by (apply H0 ||
                             apply H2)); simpl.
(*start here use ssreflect to fix this garbage*)
  apply not_eq_sym in H2.
  apply updateone_sv in H2.
  subst. by rewrite mem_seq1.
  (*move/ not_eq_sym : H3.
   ask arthur why is this not cooperating*)
  apply not_eq_sym in H3.
  apply updateone_arr in H3.
  subst. destruct element. by pose proof (gen_locs_works H1).
  eapply IHiceval_w; try reflexivity; try
  assumption.
  Qed.

Lemma iceval_cceval: forall{k: context} {N Nend1 Nend2 : nvmem} {V Vend1 Vend2: vmem}
                      {c cend1 cend2 : command} {O1 O2: obseq} {W1 W2: the_write_stuff},
    iceval_w (k, N, V, c) O1 (k, Nend1, Vend1, cend1) W1 ->
    cceval_w (N, V, c) O2 (Nend2, Vend2, cend2) W2 ->
    (Nend1 = N /\ Vend1 = (reset V) /\ W1 = emptysets /\ cend1 = Ins inreboot) \/
    (Nend1 = Nend2 /\ Vend1 = Vend2 /\ W1 = W2).
  intros.
  move : cend2 H0.
  dependent induction H; intros.
  left. (*do! [split]. by [].*)
  split; [reflexivity | split; [reflexivity | split; reflexivity] ].
  inversion H0.
  inversion H0; subst. right.
  split; [reflexivity | split; reflexivity ].
  exfalso. by apply (H9 w).
  inversion H2; subst. right.
  destruct (determinism_e H H12). subst.
  split; [reflexivity | split; reflexivity ].
  exfalso. apply (negNVandV x H0 H13).
inversion H2; subst. right.
exfalso. apply (negNVandV x H13 H0).
right.
  destruct (determinism_e H H12). subst.
  split; [reflexivity | split; reflexivity ].
  right.
  inversion H3; subst.
  destruct (determinism_e H H14).
  destruct (determinism_e H0 H15).
  subst.
  pose proof (equal_index_works H16 H1).
  subst.
  split; [reflexivity | split; reflexivity ].
  right. inversion H0; subst.
  split; [reflexivity | split; reflexivity ].
  exfalso. by apply H10.
  inversion H2; subst.
  - exfalso. by apply (H w).
  - exfalso. by apply H0.
    suffices:
  (Nend1 = N /\
  Vend1 = reset V /\ W = ([::], [::], [::]) /\ Ins skip = Ins inreboot \/
   Nend1 = Nend2 /\ Vend1 = Vend2 /\ W = W2).
    intros. right.
    destruct x as [ [ contraN [ contraV [contraW contrac] ] ] | H5 ].
    discriminate contrac. assumption.
    eapply IHiceval_w; try reflexivity.
    apply H14.
    right. inversion H0; subst;
    destruct (determinism_e H H11); subst.
    split; [reflexivity | split; reflexivity ].
    inversion H2.
    right. inversion H0; subst;
    destruct (determinism_e H H11); subst.
    inversion H2.
    split; [reflexivity | split; reflexivity ].
(*ask arthur how to do a recursive tactic
 for dealing with big conjunctions*)
Qed.

Lemma cceval_iceval: forall {N Nend : nvmem} {V Vend: vmem}
                      {c cend: command} {O: obseq} {W: the_write_stuff},
    cceval_w (N, V, c) O (Nend, Vend, cend) W ->
    (forall(k: context), iceval_w (k, N, V, c) O (k, Nend, Vend, cend) W).
Admitted.

  Lemma wt_gets_bigger: forall{N N0 N1 Nend: nvmem} {V V0 V1 Vend: vmem} {c c0 c1 cend: command} {O0 O1: obseq} {W0 W1: the_write_stuff}
  {l: loc},
    iceval_w ((N0, V0, c0), N, V, c) O0 ((N0, V0, c0), N1, V1, c1) W0 ->
    trace_c (N, V, c) (Nend, Vend, cend) O1 W1 ->
    O1 <> [::] ->
    l \in (getwt W0) ->
          l \in (getwt W1).
  intros. dependent induction H0.
  + exfalso. by apply H1.
  + pose proof (iceval_cceval H H0).
    destruct H3 as [ [ contraN [ contraV [contraW contrac] ] ]  | [ Hn [ Hv Hw ] ] ]; subst.
    rewrite in_nil in H2. discriminate H2. assumption.
    destruct W1 as [ [w1 rd1] fw1].
    destruct W2 as [ [w2 rd2] fw2].
    simpl.
    rewrite mem_cat.
    apply (introT orP). right.
    destruct3 Cmid nmid vmid cmid.
    eapply IHtrace_c1; try
                         apply H; try reflexivity; try assumption.
Qed.
Lemma read_deterministic: forall{e: exp} {w1 w2: warvars},
                           rd e w1 ->
                           rd e w2 ->
                           w1 = w2.
  intros.
 inversion H. inversion H0. subst. 
  move: H0 H4. move: N0 V0 rs0 v0. dependent induction H1; intros.
  + by inversion H4.
  + inversion H4; subst. apply IHeeval1 in H8;
                           
                           apply IHeeval2 in H11;
                        try(   rewrite (readobs_app_wvs r1 r2);
    rewrite (readobs_app_wvs r0 r3);
      by rewrite H8 H11);
                        try ( eapply RD; (apply H11) || (apply H1_0) || (apply H1_)
                            || (apply H8)).
  + simpl. inversion H4; subst; simpl; auto.
  + simpl. inversion H4; subst; simpl; auto.
  + inversion H5. subst. rewrite (readobs_app_wvs rindex).
    rewrite (readobs_app_wvs rindex0).
    suffices: (readobs_wvs rindex) =(readobs_wvs rindex0).
    move ->.
    destruct element. destruct element0.
 pose proof (equal_index_arr H2) as arreq. 
 pose proof (equal_index_arr H12) as arreq1. by subst.
 eapply IHeeval. apply (RD H1).
 apply (RD H8). apply H8.
Qed.


Lemma negfwandw_means_r: forall{C Cend: context}  {O: obseq} {W: the_write_stuff}
  {l: loc},
    trace_c C Cend O W ->
    l \notin (getfstwt W) -> l \in (getwt W) -> l \in (getrd W).
  intros. destruct3 W w rD fw.
  dependent induction H.
  + discriminate H1.
  + induction H; (try discriminate H1);
    simpl in H1;
    simpl in H0;
    simpl.
    destruct (l \in readobs_wvs r) eqn: beq.
    auto.
    apply negbT in beq.
    rewrite mem_seq1 in H1.
    move/eqP: H1 => H1. subst.
    rewrite beq in H0.
    rewrite mem_seq1 in H0.
    move/eqP: H0 => contra.
    exfalso. by apply contra.
    destruct (l \in readobs_wvs (r ++ ri)) eqn: beq.
    auto.
    rewrite mem_filter in H0.
    move/ nandP : H0 => [contra1 | contra2].
           + by move/ negPn : contra1.
           + rewrite H1 in contra2. discriminate contra2.
    apply IHcceval_w; assumption.
    destruct W1 as [ [w1 rd1] fw1].
    destruct W2 as [ [w2 rd2] fw2].
    simpl in H3. simpl in H4.
    simpl.
    simpl in IHtrace_c1.
    simpl in IHtrace_c2.
    rewrite mem_cat.
    apply (introT orP).
    rewrite mem_cat in H3.
    case/norP : H3 => [H32 H31].
    rewrite mem_cat in H4.
    move/ orP : H4 => [H40 | H41].
  + destruct (l \in rd1) eqn: beq1.
    - auto.
      left.
      rewrite mem_filter in H32.
      move/ nandP : H32 => [H320 | H321].
      rewrite beq1 in H320.
     move/negPn : H320 => contra.
      discriminate contra.
    - eapply IHtrace_c2; try reflexivity;
        try assumption.
  + right. eapply IHtrace_c1; try
                               reflexivity; try assumption.
 Qed.

Lemma cceval_to_rd_sv: forall {N Nend: nvmem} {V Vend: vmem}
                      {e: exp} {x: smallvar} {O: obseq}
                      {W: the_write_stuff}
                      {Re: warvars}
  {cend: command},
    cceval_w (N, V, Ins (asgn_sv x e)) O
        (Nend, Vend, cend) W ->
    rd e Re ->
    (getrd W) = Re.
  intros.
  inversion H; subst; try(
                          pose proof (read_deterministic H0 (RD H10)); by subst).
Qed.

Lemma extract_write_svnv: forall {N Nend: nvmem} {V Vend: vmem}
                      {e: exp} {x: smallvar} {O: obseq}
                      {W: the_write_stuff}
  {cend: command},
    cceval_w (N, V, Ins (asgn_sv x e)) O
             (Nend, Vend, cend) W ->
    (isNV x) ->
    (getwt W) = [:: inl x].
  intros.
  inversion H; subst; try reflexivity.
  exfalso. apply (negNVandV x H0 H11).
Qed.

Lemma extract_write_svv: forall {N Nend: nvmem} {V Vend: vmem}
                      {e: exp} {x: smallvar} {O: obseq}
                      {W: the_write_stuff}
  {cend: command},
    cceval_w (N, V, Ins (asgn_sv x e)) O
             (Nend, Vend, cend) W ->
    (isV x) ->
    (getwt W) = [:: ].
  intros.
  inversion H; subst; try reflexivity.
  exfalso. apply (negNVandV x H11 H0).
Qed.

Lemma extract_write_arr: forall {N Nend: nvmem} {V Vend: vmem}
                      {e ei: exp} {a: array} {O: obseq}
                      {W: the_write_stuff}
  {cend: command},
    cceval_w (N, V, Ins (asgn_arr a ei e)) O
             (Nend, Vend, cend) W ->
   (getwt W) = (generate_locs a).
  intros.
  inversion H; subst.
   reflexivity.
Qed.

(*probs should have inducted over
 cceval instead of warok below, clean up*)
Lemma war_cceval: forall{N0 N Nmid: nvmem} {V Vmid: vmem} {c cmid: command}
                   {l: instruction}
                   {O: obseq} {W: the_write_stuff} {Wstart Rstart W' R': warvars},

        cceval_w (N, V, l;;c) O (Nmid, Vmid, cmid) W ->
        WAR_ins (getdomain N0) Wstart Rstart l W' R' ->
        ( W' = (getwt W) ++ Wstart) /\ (R' =  (getrd W) ++ Rstart).
  intros. dependent induction H0.
  - (*skip case*) inversion H; subst. split; reflexivity.
    exfalso. by apply H10.
  - inversion H; subst. pose proof (extract_write_svv H14 H0).
    rewrite H3. inversion H14; subst;
    pose proof (read_deterministic H2 (RD H15));
    subst; split; reflexivity. (*vol case*)
 - inversion H; subst. pose proof (extract_write_svnv H14 H2).
    rewrite H3. inversion H14; subst;
    pose proof (read_deterministic H0 (RD H15));
    subst; split; reflexivity. (*nord case*)
 -inversion H; subst. pose proof (extract_write_svnv H16 H0).
    rewrite H5. inversion H16; subst;
    pose proof (read_deterministic H4 (RD H17));
    subst; split; reflexivity. (*CP case*)
 - inversion H; subst. pose proof (extract_write_svnv H15 H2).
    rewrite H4. inversion H15; subst;
    pose proof (read_deterministic H3 (RD H16));
    subst; split; reflexivity. (*written to case*)
 - (*nrd arr case*) inversion H; subst; inversion H14; subst. simpl. rewrite readobs_app_wvs. rewrite catA.
   pose proof (read_deterministic H2 (RD H16)).
   pose proof (read_deterministic H0 (RD H15)).
   subst. split; reflexivity.
 - inversion H; subst; inversion H15; subst. simpl. rewrite readobs_app_wvs. rewrite catA.
   pose proof (read_deterministic H3 (RD H17)).
   pose proof (read_deterministic H0 (RD H16)).
   subst. split; reflexivity.
Qed.



Lemma cceval_steps: forall{N Nmid: nvmem} {V Vmid: vmem} {c cmid: command}
                   {O: obseq} {W: the_write_stuff} {l: instruction},

        cceval_w (N, V, l;;c) O (Nmid, Vmid, cmid) W ->
        c = cmid.
intros. inversion H; subst; try reflexivity. Qed.


Lemma cceval_steps_ins: forall{N Nmid: nvmem} {V Vmid: vmem} {cmid: command}
                   {O: obseq} {W: the_write_stuff} {l: instruction},

        cceval_w (N, V, Ins l) O (Nmid, Vmid, cmid) W ->
        cmid = Ins skip.
intros. inversion H; subst; try reflexivity. Qed.
(*doesn't this just follow immediately
 from construction of W', R' in WARins?*)
Lemma warok_partial:  forall{N0 N Nmid: nvmem} {V Vmid: vmem} {c cmid: command} {O: obseq} {W: the_write_stuff} {Wstart Rstart: warvars},
    trace_c (N, V, c) (Nmid, Vmid, cmid) O W ->
    checkpoint \notin O ->
    WARok (getdomain N0) Wstart Rstart c ->
    WARok (getdomain N0) ((getwt W) ++ Wstart) ((getrd W) ++ Rstart) cmid.
  intros.
  move: H1.
  move : Wstart Rstart.
  dependent induction H; intros.
  + simpl.  assumption.
    (*inducting warok
    move: H H0.
    move: cmid W N V Nmid Vmid O.*)
    dependent induction H1.
  - (*ins case, getting skip for last com of cceval*)
    pose proof (cceval_steps_ins H). subst. eapply WAR_I. constructor.
  - (*CP case*)
    inversion H; subst.
      - exfalso. rewrite mem_seq1 in H0. move/ eqP :H0.
      by apply.
      - exfalso. by apply (H11 w).
  - (*seq case*) 
    intros.
    destruct (war_cceval H H2). subst.
    pose proof (cceval_steps H). subst. assumption.
  - (*if case*)
    inversion H; subst; 
    pose proof (read_deterministic H1 (RD H12));
    subst; assumption.
    (*inductive case trace*)
    destruct3 Cmid nmid vmid cmiddle.
    simpl.
    repeat rewrite <- catA.
    rewrite mem_cat in H3.
    move/ norP : H3 => [H31 H32].
    eapply IHtrace_c2; try reflexivity; try assumption.
    eapply IHtrace_c1; try reflexivity; try assumption.
Qed.
    (*wts
     W' = W0 ++ W
     R' = R ++ getrd W0*)
    (*inductive cceval step
    inversion H3; subst.*)
  (* - cp case exfalso. by apply (H w).
    eapply IHcceval_w; try reflexivity.*)



Lemma fourteen: forall{N0 N Nend: nvmem} {V Vend: vmem} {c cend: command} {O: obseq} {W: the_write_stuff}
                  {Wstart Rstart: warvars} (l: loc),
    trace_c (N, V, c) (Nend, Vend, cend) O W ->
    WARok (getdomain N0) Wstart Rstart c ->
    checkpoint \notin O ->
    (*O <> [::] -> empty trace annoying and i dont think
               i have to deal w it*)
    l \notin (remove Rstart (getfstwt W)) -> (*l not in OVERALL FW for this trace*)
    l \in (getwt W) -> (*l written to
                       IN THIS trace*)
    l \in (getdomain N0) \/ l \in Wstart. (*l is checkpointed
                                          or l was already
                                          written to
                                          in which case can't
                                          say*)
  intros. move: Wstart Rstart H0 H1 H2 H3.
  dependent induction H; intros. (*inducting on trace *)
  + (*emoty trace*)
    intros. rewrite in_nil in H3. discriminate H3. 
  + (*single trace*)
    move: H0 H1 H2 H3. move: Wstart Rstart.
    remember H as H01. clear HeqH01.
    dependent induction H01; intros;
      try (rewrite in_nil in H3; discriminate H3);
try (rewrite in_nil in H4; discriminate H4)
    .
    
    (*inducting cceval*)
  + (*nonvol case*)
    (*showing x = l*)
    remember H6 as Hwt. clear HeqHwt. 
         simpl in H6.
         rewrite mem_seq1 in H6.
         move/ eqP : H6 => H6. subst.
       inversion H3; subst; inversion H10;
       subst. (*casing on warIns*)
     (*vol case, x \notin getwt W*)
       +  exfalso. apply (negNVandV x H0 H13).
       + (*nord case*)
         (*showing l in rd W*)

         rewrite mem_cat in H16.
         move / negP / norP : H16 => [H160 H161].
         rewrite mem_filter in H5.
         rewrite negb_and in H5.
         simpl in H5.
         rewrite H161 in H5.
         rewrite orFb in H5.
         pose proof (negfwandw_means_r (CTrace_Single H) H5 Hwt) as Hrd. simpl in Hrd.
       (*showing x notin RD(W)*)
       pose proof (read_deterministic H13 (RD H2)). subst. rewrite Hrd in H160. discriminate H160.
     + (*CP case*)
        by left.
     + (*written case*)
       by right.
     - (*vol case*)
       simpl in H6. rewrite in_nil in H6.
       discriminate H6.
     - (*array case*)
    (*showing x = l*)
       remember H7 as Hwt. clear HeqHwt.
       simpl in H7.
       simpl in H6.
       (*  rewrite mem_seq1 in H7.
         move/ eqP : H7 => H7. subst.*)
       inversion H4; inversion H12;
       subst. (*casing on warIns*)
       + (*nord arr*)
         (*showing l in rd W*)
         suffices: (l \notin Rstart).
         - intros Hstart.
        (* rewrite mem_cat in H22.
         move / negP / norP : H16 => [H160 H161].*)
         rewrite mem_filter in H6.
         rewrite negb_and in H6.
         rewrite Hstart in H6.
         rewrite orFb in H6.
         pose proof (negfwandw_means_r (CTrace_Single H) H6 Hwt) as Hrd. simpl in Hrd.
       (*showing x notin RD(W)*)
       exfalso.
       apply H23.
       exists (l : loc).
       split.
       apply Hwt.
       (*showing rd sets are same*)
       pose proof
            (read_deterministic (RD H0) H19).
       pose proof
            (read_deterministic (RD H3) H22).
       subst.
       rewrite catA.
       rewrite <- readobs_app_wvs.
       rewrite mem_cat.
       apply (introT orP).
       left.
       apply Hrd.
         - apply (introT negP).
           intros contra. apply H23.
           exists (l : loc).
       split.
       destruct element.
       apply Hwt.
       rewrite catA.
       rewrite mem_cat.
       apply (introT orP).
      by right.
     + (*CP array*)
         destruct element.
         pose proof (equal_index_arr H1). subst.
         left.
         apply (in_subseq H24 H7).
 - (*seq case*)
    eapply IHH01; try apply H01; try reflexivity; try assumption.
    inversion H2; subst. (*invert WARok to get warins*)
    + (*CP case warok*)
    exfalso. by apply (H1 w).
    + (*seq case warok*)
      eapply WAR_I; apply H11; try assumption.
      assumption.
      (*clean up above*)
    + (*trace inductive step*)
simpl in H6. rewrite mem_cat in H6.
destruct3 Cmid nmid vmid cmid.
destruct (l \in (getwt W1)) eqn: beq.
       + (*x written in 1st half*)
         eapply IHtrace_c1; try reflexivity;
           try assumption.
         apply H3.
         rewrite mem_cat in H4.
         move/ norP : H4 => [H41 H42].
         assumption.
         simpl in H5.
         apply (remove_app_r H5).
     + (*2nd half, NOT in first half *)
         rewrite mem_cat in H4.
         move/ norP : H4 => [H41 H42].
       suffices:
         (is_true (l \in getdomain N0) \/ is_true (l \in (getwt W1) ++ Wstart)).
          - move => [Case1 | Case2].
          - by left.
          - right. rewrite mem_cat in Case2.
            move / orP : Case2 => [contra | yes].
            - rewrite contra in beq. discriminate beq.
            - assumption.
       eapply IHtrace_c2; try reflexivity; try
        apply (warok_partial H H41 H3); try
                                          assumption.
       unfold append_write in H5.
       simpl in H5.
       unfold remove in H5.
       rewrite filter_cat in H5.
       unfold remove.
       rewrite mem_cat in H5.
       move / norP : H5 => [H50 H51].
       rewrite <- remove_to_app in H50.
       assumption.
       move/ orP : H6 => [H60 | H61].
            - assumption.
            - rewrite beq in H61. discriminate H61.
Qed.


Lemma pf_idem : forall(N0 N Nend: nvmem) (V0 V Vend: vmem)
                      (c0 c: command) (O : obseq) (W : the_write_stuff),
        iceval_w ((N0, V0, c0), N, V, c) O
                 ((N0, V0, c0), Nend, Vend, c) W -> N = Nend.
  intros.
  dependent induction H; (try auto).
  + exfalso. by apply H. (*here is where reboot case happens*)
  + 
    apply stupid in x. contradiction.
 Qed.


    Lemma fifteen: forall{N0 N1 N1' N2: nvmem} {V V': vmem} {c c': command} {O: obseq} {W: the_write_stuff},
             iceval_w ((N0, V, c), N1, V, c) O
             ((N0, V, c), N1', V', c') W ->
             (checkpoint \notin O) ->
             (reboot \notin O) ->
             WARok (getdomain N0) [::] [::] c ->
             current_init_pt N0 V c N1 N1 N2 ->
             subset_nvm N0 N1 ->
             current_init_pt N0 V c (N0 U! N1') (N0 U! N1') N2.
  intros. inversion H3. subst. remember T as TN1. clear HeqTN1.
  destruct H5; subst. (*casing on skip*)
  +      eapply valid_mem.
(*need to show N0 U! N1' can make it*)
         - assert(trace_c ((N0 U! N1'), V, c) (Nend, Vend, Ins skip) O0 W0) as T2.
eapply twelve00.
   exists W. apply (iTrace_Single H). assumption.
   assumption. assumption. constructor. assumption. assumption.
     apply T2. by left.
       - (*showing N2 subst N0 U! N1'
          Ignore this bullet: I forgot to take out this part of the
          relation after our last meeting*)
assert (multi_step_i ((N0, V, c), N1, V, c)
                              ((N0, V, c), N1', V', c') O).
         exists W.  apply (iTrace_Single H).
         apply (subseq_trans
                  (subseq_trans H6 (dom_gets_bigger
                                      H5)) (dom_gets_bigger_rb
                                                    N0 N1')).
         assumption.
  (*casing on whether l is different in N1*)
  intros. destruct (getmap N1 l == getmap N2 l) eqn: beq. (*casing on fw or not*)
           move/eqP :beq => beq. rewrite <- beq in H5.
           (*since they are equal but N1' is different on l, l
            is not checkpointed*)
           assert (not(l \in getdomain N0)).
           unfold subset_nvm in H4. destruct H4 as [H41 H42].
           intros contra. remember contra as contra1.
           clear Heqcontra1. apply H42 in contra1.
           destruct (sub_update N0 N1') as [blah HN1'].
           apply HN1' in contra.
           rewrite contra1 in contra.
           symmetry in contra.
           apply H5 in contra. contradiction.
           destruct N0 as [M0 D0] eqn: N0eq.
           destruct N1' as [M1' D1'] eqn: N1'eq.
           assert (M1' = (getmap N1')) as rememberme.
            by rewrite N1'eq. 
           assert (D0 = (getdomain N0)) as rememberme1.
             by rewrite N0eq.
             remember N1'eq as stayput.
             remember N0eq as stayput1.
           unfold updatemaps in H5.
           simpl in H5.
           simpl in H9.
           apply not_true_is_false in H9.
           rewrite H9 in H5.
           simpl.
           (*now have that l is not in D0*)
           left.
(*inverting T to split up W0*)
           inversion T; subst.
           inversion H. subst.
          exfalso. by apply H5.
(*single trace case*)
+ destruct (iceval_cceval H H10) as [ [ HN [HV Hw] ] | [HN [HV Hw ] ] ]; subst.
       - (*pf case*) exfalso. by apply H5.
       - 
  destruct W0 as [ [W11 R1] Fw1] eqn: W1eq.
  simpl.
         suffices: (l \in W11).
         intros HW1.
         destruct (l \in Fw1) eqn: FWeq; auto.
         apply negbT in FWeq.
         pose proof (negfwandw_means_r TN1 FWeq HW1) as Hr.
         simpl in Hr.
         suffices: (
       is_true (l \in D0)
                   ).
         case => contra.
+ rewrite H9 in contra. discriminate contra.
  rewrite rememberme1.
  suffices: (is_true (l \in getdomain (NonVol M0 D0)) \/
             is_true (l \in [::])).
  - move => [yes | contra]. assumption.
  rewrite in_nil in contra. discriminate contra.
  -
    apply (fourteen l TN1 H2); try assumption.
    (*rewrite filter_predT.*)
    rewrite remove_empty. assumption.
         (*this comes from fact that N1 steps to M1'
          in one (H) but N1 l and M1' of l are different.. new theorem*)
         assert (W11 = (getwt W0)) as Hwt. by rewrite W1eq; auto.
         rewrite Hwt.
         eapply (wt_gets_bigger H).
         rewrite <- W1eq in TN1.
         apply TN1.
         intros contra. subst.
         inversion H10.
         apply (update_one H); try assumption.
         intros contra. apply H5.
         rewrite rememberme. symmetry. assumption.
(*larger trace case; exact same reasoning
 significant potential for
 decreasing boilerplate if I just proved
 that fstwt set grows as trace gets bigger,
 used first IH*)
+ destruct W1 as [ [W11 R1] Fw1] eqn: W1eq.
         destruct W2 as [ [W22 R2] Fw2] eqn: W2eq.
         unfold append_write.
         simpl.
         suffices: (l \in Fw1).
         intros. rewrite mem_cat.
         apply (introT orP). by right.
         simpl in H8.
         suffices: (l \in W11).
         intros HW1.
         destruct (l \in Fw1) eqn: FWeq; auto.
         apply negbT in FWeq.
         pose proof (negfwandw_means_r H10 FWeq HW1) as Hr.
         simpl in Hr.
         suffices: (is_true (l \in Fw1 ++ remove R1 Fw2) \/
       is_true (l \in D0)
                   ).
         destruct (l \in Fw1 ++ remove R1 Fw2) eqn: deq.
         rewrite mem_cat in deq.
         move/ orP : deq.
         case => Hin.
          rewrite Hin in FWeq.
         discriminate FWeq.
         rewrite mem_filter in Hin.
         case/ andP : Hin => [ contra blah ].
         rewrite Hr in contra. discriminate contra.
         case => contra.
         assumption.
         rewrite H9 in contra. assumption.
         right. rewrite rememberme1.
         destruct3 Cmid nmid vmid cmid.
  suffices: (is_true (l \in getdomain (NonVol M0 D0)) \/
             is_true (l \in [::])).
  - move => [yes | contra]. assumption.
  rewrite in_nil in contra. discriminate contra.
  -
    apply (fourteen l H10 H2); try (rewrite remove_empty);
      try assumption.
         rewrite mem_cat in H7.
         case/ norP : H7 => Hor1 Hor2. assumption.
         (*this comes from fact that N1 steps to M1'
          in one (H) but N1 l and M1' of l are different.. new theorem*)
         assert (W11 = (getwt W1)) as Hwt. by rewrite W1eq; auto.
         rewrite Hwt.
         destruct3 Cmid nmid vmid cmid.
         eapply wt_gets_bigger.
         apply H.
         rewrite <- W1eq in H10.
         apply H10.
         assumption.
         apply (update_one H); try assumption.
         intros contra. apply H5.
         rewrite rememberme. symmetry. assumption.
(*N1 l != N2 l*)
+ apply H8. by move/ eqP : beq.

 (*checkpoint case
  consider doing the H5 casing later on so you have less boilerplate*)
 + destruct H5 as [wcp [crem2 cpeq] ]. subst.
   eapply valid_mem.
     assert(trace_c ((N0 U! N1'), V, c) (Nend, Vend, incheckpoint wcp;;
          crem2) O0 W0) as T2.
eapply twelve01.
   exists W. apply (iTrace_Single H). assumption.
   assumption. assumption.  assumption. assumption.
     apply T2. right. exists wcp crem2. reflexivity.
       - (*showing N2 subst N0 U! N1'*)
assert (multi_step_i ((N0, V, c), N1, V, c)
                              ((N0, V, c), N1', V', c') O).
         exists W.   apply (iTrace_Single H).
         apply (subseq_trans
                  (subseq_trans H6 (dom_gets_bigger
                                      H5)) (dom_gets_bigger_rb
                                                    N0 N1')).
         assumption.
  (*casing on whether l is different in N1*)
  intros. destruct (getmap N1 l == getmap N2 l) eqn: beq. (*casing on fw or not*)
           move/eqP :beq => beq. rewrite <- beq in H5.
           (*since they are equal but N1' is different on l, l
            is not checkpointed*)
           assert (not(l \in getdomain N0)).
           unfold subset_nvm in H4. destruct H4 as [H41 H42].
           intros contra. remember contra as contra1.
           clear Heqcontra1. apply H42 in contra1.
           destruct (sub_update N0 N1') as [blah HN1'].
           apply HN1' in contra.
           rewrite contra1 in contra.
           symmetry in contra.
           apply H5 in contra. contradiction.
           destruct N0 as [M0 D0] eqn: N0eq.
           destruct N1' as [M1' D1'] eqn: N1'eq.
           assert (M1' = (getmap N1')) as rememberme.
            by rewrite N1'eq. 
           assert (D0 = (getdomain N0)) as rememberme1.
             by rewrite N0eq.
             remember N1'eq as stayput.
             remember N0eq as stayput1.
           unfold updatemaps in H5.
           simpl in H5.
           simpl in H9.
           apply not_true_is_false in H9.
           rewrite H9 in H5.
           simpl.
           (*now have that l is not in D0*)
           left.
    (*inducting on T to split up W0*)
       - inversion T; subst.
         (*empty trace case*)
           + 
           inversion H; subst; try (
                                   exfalso; by apply H5).
           exfalso. by apply (H20 wcp).
          (*single trace case*)
           + destruct (iceval_cceval H H10) as [ [HN [HV Hw] ]  | [HN [HV Hw ] ] ]; subst.
             - exfalso. by apply H5.
             - destruct W0 as [ [W11 R1] Fw1] eqn: W1eq.
         simpl.
         suffices: (l \in W11).
         intros HW1.
         destruct (l \in Fw1) eqn: FWeq; auto.
         apply negbT in FWeq.
         pose proof (negfwandw_means_r TN1 FWeq HW1) as Hr.
         simpl in Hr.
         suffices: (
       is_true (l \in D0)
                   ).
         move => contra.
+ rewrite H9 in contra. discriminate contra.
  suffices: (is_true (l \in getdomain (NonVol M0 D0)) \/
             is_true (l \in [::])).
             - move => [yes | contra]. assumption.
               rewrite in_nil in contra. discriminate contra.
             -
               apply (fourteen l TN1 H2); try assumption.
               rewrite remove_empty. assumption.
(*this comes from fact that N1 steps to M1' in one (H) but N1 l and M1' of l are different.. new theorem*)
         assert (W11 = (getwt W0)) as Hwt. by rewrite W1eq; auto.
         rewrite Hwt.
         eapply wt_gets_bigger.
         apply H.
         (*for error 2 come here apply TN1. *)
         rewrite <- W1eq in TN1.
         apply TN1.
         intros contra. subst.
         inversion H10.
         eapply (update_one H); try assumption.
         intros contra. apply H5.
         rewrite rememberme. symmetry. assumption.
         (*big trace case*)
+ destruct W1 as [ [W11 R1] Fw1] eqn: W1eq.
         destruct W2 as [ [W22 R2] Fw2] eqn: W2eq.
         unfold append_write.
         simpl.
         suffices: (l \in Fw1).
         intros. rewrite mem_cat.
         apply (introT orP). by right.
         simpl in H8.
         suffices: (l \in W11).
         intros HW1.
         destruct (l \in Fw1) eqn: FWeq; auto.
         apply negbT in FWeq.
         pose proof (negfwandw_means_r H10 FWeq HW1) as Hr.
         simpl in Hr.
         suffices: (is_true (l \in Fw1 ++ remove R1 Fw2) \/
       is_true (l \in D0)
                   ).
         destruct (l \in Fw1 ++ remove R1 Fw2) eqn: deq.
         rewrite mem_cat in deq.
         move/ orP : deq.
         case => Hin.
          rewrite Hin in FWeq.
         discriminate FWeq.
         rewrite mem_filter in Hin.
         case/ andP : Hin => [ contra blah ].
         rewrite Hr in contra. discriminate contra.
         case => contra.
         assumption.
         rewrite H9 in contra. assumption.
         right. rewrite rememberme1.
         destruct3 Cmid nmid vmid cmid.
  suffices: (is_true (l \in getdomain (NonVol M0 D0)) \/
             is_true (l \in [::])).
  - move => [yes | contra]. assumption.
  rewrite in_nil in contra. discriminate contra.
  -
    apply (fourteen l H10 H2); try (rewrite remove_empty);
      try assumption.
         rewrite mem_cat in H7.
         case/ norP : H7 => Hor1 Hor2. assumption.
         (*this comes from fact that N1 steps to M1'
          in one (H) but N1 l and M1' of l are different.. new theorem*)
         assert (W11 = (getwt W1)) as Hwt. by rewrite W1eq; auto.
         rewrite Hwt.
         destruct3 Cmid nmid vmid cmid.
         eapply wt_gets_bigger.
         apply H.
         rewrite <- W1eq in H10.
         apply H10.
         assumption.
         apply (update_one H); try assumption.
         intros contra. apply H5.
         rewrite rememberme. symmetry. assumption.
(*N1 l != N2 l*)
+ apply H8. by move/ eqP : beq.
  Unshelve. apply V1. apply w. apply V1. apply w.  Qed.
           


(*Lemma 12.0: forall(N0 N1 N1': nvmem) (V V': vmem) (c0 c1 crem: command)
  (Obig Osmall: obseq) (Wbig Wsmall: the_write_stuff),
    WARok N0 [] [] [] c0 ->
    multistep_c ((N0, V, c0), N1, V, c0) ((N0, V, c0), N1', V', c)
    iceval ((N0, V, c0), N1, V, c0) ((N0, V, c0), N1', V', c1) Osmall Wsmall ->*)

Lemma itrace_ctrace: forall{N0 N1 Nend1: nvmem} {V V' Vend: vmem} {c c' cend: command}
                   {O : obseq} {W: the_write_stuff},
        trace_i ((N0, V, c), N1, V', c') ((N0, V, c), Nend1, Vend, cend) O W ->
        (reboot \notin O) ->
        trace_c (N1, V', c') (Nend1, Vend, cend) O W.
  Admitted.
(*if there is a PF it would have to be the last thing
cuz no reboots
 which is fine
 cuz empty trace*)

Lemma skiptrace_empty:forall{N Nend: nvmem} {V Vend: vmem} {cend: command}
                   {O : obseq} {W: the_write_stuff},
    trace_c (N, V, Ins skip) (Nend, Vend, cend) O W -> O = [::].
  Admitted.

Lemma ctrace_deterministic: forall{N Nend1 Nend2: nvmem} {V Vend1 Vend2: vmem} {c cend: command}
                   {O1 O2: obseq} {W1 W2: the_write_stuff},
        trace_c (N, V, c) (Nend1, Vend1, cend) O1 W1 ->
        trace_c (N, V, c) (Nend2, Vend2, cend) O2 W2 ->
        Nend1 = Nend2 /\ Vend1 = Vend2 /\ O1 = O2 /\ W1 = W2.
  Admitted.

Lemma nineteen: forall{Nstart N1 Nend N2: nvmem} {V V1 Vend: vmem} {c cend: command}
                 {l: instruction}
                   {O : obseq} {W: the_write_stuff},
             same_pt Nstart V c (Ins l) N1 N2 ->
             cceval_w (N1, V1, (Ins l)) O (Nend, Vend, cend) W ->
            ( forall(z: loc), z \in (getrd W) -> (*z was read immediately cuz trace is only 1
                                thing long*)
                   (getmap N1) z = (getmap N2) z). (*since z isnt in FW of trace from Ins l to skip*)
Admitted.

Lemma twenty:
forall{N0 N1: nvmem} {V0: vmem} {e: exp} {r0: readobs} {v0: value},
  eeval N0 V0 e r0 v0 ->
              (forall(z: loc), z \in (readobs_wvs r0) -> (getmap N0) z = (getmap N1) z) ->
              eeval N1 V0 e r0 v0.
  intros. Admitted.


(*starting point in terms only of current mem so don't need to parameterize it,
 don't need to induct over length of starting trace!*)
    Lemma sixteen: forall{N0 N1 Nend N2 : nvmem} {V V1 Vend: vmem} {c c1 cend: command}
                   {O : obseq} {W: the_write_stuff},
        trace_i ((N0, V, c), N1, V1, c1) ((N0, V, c), Nend, Vend, cend) O W -> cend <> (Ins inreboot) ->
        (checkpoint \notin O) ->
             (reboot \notin O) ->
             WARok (getdomain N0) [::] [::] c ->
             same_pt (N0 U! N1) V c c1 N1 N2 ->
           exists(Nend2: nvmem),(trace_c (N2, V1, c1) (Nend2, Vend, cend) O W /\
             same_pt (N0 U! Nend) V c cend Nend Nend2).
      intros.
      dependent induction H.
      (*empty trace case*)
      + exists N2. split. eapply CTrace_Empty.
        assumption.
        (*single intermittent step case*)
      + remember H as Hiceval.
        clear HeqHiceval.
        (*show arthur the ridiculous error message
         that i get if i take this out*)
        dependent induction H. (*induct iceval
                                to get length of step*)
        - (*pf*) by exfalso.
        - (*rb*) exfalso. move/negP :H2.
            by apply.
        - (*cp*) exfalso. move/negP: H1. by apply.
        - (*nv*) exists((updateNV_sv N2 x v)).
          pose proof (NV_Assign H H0 H1) as Hcceval.
          pose proof (iceval_cceval Hiceval Hcceval) as [ [ contraN [ contraV [contraW contrac] ] ]  | [ Hn [ Hv Hw ] ] ]; subst.
          discriminate contrac.
          Check nineteen.
          pose proof (nineteen H6 Hcceval) as Hloceq.
          Check twenty.
          pose proof (twenty H Hloceq) as Heval2.
          pose proof (NV_Assign Heval2 H0 H1) as Hcceval2.
          split.
            - by apply CTrace_Single.
            - eapply same_mem.
              Check single_step_all.
              (*consider is there any point to the
               multistep part*)
              Check twelve00.
              suffices: (multi_step_i
                          (N0, V, c, N1, Vend, Ins (asgn_sv x e))
                          (N0, V, c, updateNV_sv N1 x v, Vend, Ins skip) [:: Obs r]).
            - intros Hm.
              inversion H6. subst.
              (*NTS crem = skip*)
              pose proof (trace_stops T2) as Hrem.
              pose proof (trace_append T1 T2) as Tend.
              pose proof (and_or_elim Hrem H7).
              assert (~
        (crem = Ins (asgn_sv x e) /\
         (exists w crem2, crem = incheckpoint w;; crem2))).
              intros [contra1 [b1 [b2 contra2] ] ].
              subst. discriminate contra2.
              apply H12 in H13. subst.
              (*weird that im trying to wiggle around
               initializing Vend*)
              Check twelve00.
              Admitted.
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
             same_config ((N0, V, c), Nmid, Vmid, cmid) (*Sigma ~ sigma*)
                         sigma /\
             trace_c sigma (Nend, Vend, cend) Orem Wrem (*sigma -> Sigma'-*)
             (*same obs, write as "intermittent" execution*)
          ).
  Admitted.

      Lemma obseq_readobs: forall{O: obseq}
                            {N1 N2: nvmem}
                            {V1 V2: vmem}
                            {c1 c2: command}
                            {W: the_write_stuff},
trace_c (N1, V1, c1) (N2, V2, c2) O
        W ->
checkpoint \notin O ->
exists(o: readobs), O = [::Obs o].
Admitted.

Lemma hacky: forall(o3 o4: readobs),
                    [:: Obs o3] ++ [:: Obs o4] =
              [:: Obs (o3 ++ o4)].
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

    Lemma eleven: forall{N0 N1 Nmid Nend N2: nvmem} {V Vmid Vend: vmem} {c cmid cend: command}
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
                 checkpoint \notin O2 /\ (*cuz its taking
                                         the same path as N1 to
                                         cmid*)
                 (*write SETS have to be the same
                          but write lists do not,
                          can add that extra specificity
                          if I need it*)
             same_config ((N0, V, c), Nmid, Vmid, cmid) (*Sigma ~ sigma*)
                         sigma /\
             trace_c sigma (Nend, Vend, cend) Orem Wrem  /\ (*sigma -> Sigma'-*)
             (*same obs, write as "intermittent" execution*)
             (O1 ++ Orem <=m O2 ++ Orem)).
      intros.
      apply trace_convert in H.
      dependent induction H.
      2: {
        suffices: (exists O3 sigma Wc,
                      is_true (checkpoint \notin O3) /\
               trace_c (N2, V, c) sigma O3 Wc /\
               same_config
                 (N0, V, c, Nmid, Vmid, cmid)
                 sigma /\
               trace_c sigma (Nend, Vend, cend)
                 Orem Wrem /\
               (O2 ++ Orem <=m O3 ++ Orem)).
        intros [O3 [sigma [Wc [Hc1 [Hc2 [Hc3 [ Hc4 Hc5 ]
                   ] ] ] ] ] ].
      exists O3, sigma, Wc.
      repeat (try split); try assumption.
      destruct3 sigma Ns Vs cs.
      pose proof (obseq_readobs Hc2 Hc1) as [o3 Ho3].
      pose proof (obseq_readobs Hc4 H9) as [o4 Ho4].
      pose proof (obseq_readobs H H1) as [o1 Ho1].
      subst.
      repeat rewrite - catA.
      rewrite~ (hacky o3 o4).
      apply RB_Ind.
      (*2nd goal should come out of Hc5*)
      Check eleven_bc.
      assert (reboot \notin [:: Obs o1]) as Ho1.
      apply (introT negP).
      rewrite mem_seq1. move/eqP => contra. discriminate contra.
      pose proof (can_make_progress Nmid0 Vmid0 cmid0) as
          [Nend1 [Vend1 [cend1 [Oend1 [Wend1 [Tendc [Hcend1
                 Hcend2]  ] ] ] ] ] ].
      pose proof (obseq_readobs Tendc Hcend1) as [oend Hoend].
      subst.
      assert (reboot \notin [:: Obs oend]) as Hoend.
      apply (introT negP).
      rewrite mem_seq1. move/eqP => contra. discriminate contra.
      Check eleven_bc.
      rewrite mem_cat negb_orb in H3.
      move/ andP : H3 => [H31 H32].
      Check eleven_bc.
      pose proof (iTrace_Cont N0 V c H H31) as Hi.
      pose proof (iTrace_Cont N0 V c Tendc Hcend1) as Tendci.
      (*consider having two directions for trace_Convertso that
       you can combine this*)
      apply trace_convert in Hi. apply trace_convert in Tendci.
      pose proof (eleven_bc Hi H31 Ho1 H4 H5 H6 H7
                           Tendci 
                            Hcend1 Hoend
                            Hcend2)
      as [ [ [Ns1 Vs1] cs1]  [Wc1 [Hc11 [Hc21 Hc31]
         ] ] ].
      pose proof (trace_append Hc11 Hc31) as Hc2end1.
      pose proof (trace_append Hc2 Hc4) as Hc2end.
      assert (checkpoint \notin [:: Obs o3] ++ [:: Obs o4])
        as Hcp1.
      apply (introT negP). intros contra.
      rewrite mem_cat in contra.
      move/orP : contra => [contra1 | contra2].
      move/negP : Hc1. by apply.
      move/negP : H9. by apply.
      assert (checkpoint \notin ([:: Obs o1] ++ [:: Obs oend]))
        as Hcp2.
      apply (introT negP). intros contra.
      rewrite mem_cat in contra.
      move/orP : contra => [contra1 | contra2].
      move/negP : H31. by apply.
      move/negP : Hcend1. by apply.
      pose proof (same_nearest_CP Hc2end Hcp1 H11 Hc2end1 Hcp2 Hcend2). subst.
      apply (ctrace_deterministic Hc2end1) in Hc2end.
      destruct Hc2end as [e1 [e2 [e3 e4] ] ]. subst.
      exists (size o1).
      repeat rewrite hacky in e3.
      inversion e3. subst.
        by rewrite take_size_cat.
        by rewrite hacky in Hc5.
      rewrite e3 in Hc51.
      repeat rewrite hacky in Hc51.
      inversion Hc51.
(* ask arthur am i stupid or this should do something
 unfold prefix Hc51*)

      (*split up Hc2end
Hc51 should give it
       *)



     (* ask arthur.. seriously?
pose proof (and4 Hc1 Hc2 Hc3 Hc4) as Hc.*)
      (* ask arthur
what is the star for rewrite - and_assoc in Hconj*)



        }


    Lemma eleven1: forall{N0 N1 Nmid Nend N2: nvmem} {V Vmid Vend: vmem} {c cmid cend: command}
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
        (*ask arthur is this rewrite ssreflect*)

     
        
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
             current_init_pt N0 V c (N0 U! N1') (N0 U! N1')
