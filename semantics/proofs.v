Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Strings.String Program Logic.FunctionalExtensionality.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq fintype.
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
  trace_c C1 C2 O W ->
    subseq (getfstwt W) (getwt W).
Proof. intros C1 C2 O W T. induction T.
       + auto.
       + induction c; auto; try (unfold getfstwt; unfold getwt;
         apply filter_subseq).
       - simpl. apply (cat_subseq IHT1
                                    (subseq_trans
                                    (filter_subseq _ _ )
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
    c' = (incheckpoint w ;; c) \/ checkpoint \in O.
  intros N N' V V' c c' w O W T.
  dependent induction T.
  + left. reflexivity.
  +  inversion c0; subst. right.  apply(mem_head checkpoint).
     inversion H11.
  + destruct3 Cmid nmid vmid cmid. destruct (IHT1 N nmid V vmid c cmid w); subst; try reflexivity.
      - destruct (IHT2 nmid N' vmid V' c c' w); subst; try reflexivity;
          [left; reflexivity | right; apply (in_app_r H)].
      - right. apply (in_app_l H).
Qed.

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
  rewrite mem_enum.
  reflexivity.
Qed.
(*ask arthur
 HOW did reflexivity work just then*)
 (* Check enum_mem.
  rewrite enum_mem.
  rewrite <- inE.
  reflexivity.

         i (enum
                        (pred_of_simpl (T:='I_l)
                           (pred_of_argType 'I_l)))

suffices: (i \in enum
                        (pred_of_simpl
                           (T:='I_l)
                           (pred_of_argType
                              'I_l))).
  suffices: 
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
Lemma determinism: forall{C1 C2 C3: context} {O1 O2: obseq} {W1 W2: the_write_stuff},
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
         try (apply IHcc1 in H5; destruct H5 as
             [onee rest]; destruct rest as [two threee];
              inversion onee; inversion two);
         try( 
 destruct (determinism_e H3 H); destruct (determinism_e H4 H0); subst;
   pose proof (equal_index_works H1 H5));
         try (subst;
              split; [reflexivity | (split; reflexivity)]).
exfalso; apply H0; reflexivity. (*start here fix that line*)
Qed.


(*concern: the theorem below is not true for programs with io
 but then again neither is lemma 10*)
Lemma single_step_all: forall{C1 Cmid C3: context} 
                    {Obig: obseq} {Wbig: the_write_stuff},
    trace_c C1 C3 Obig Wbig ->
    Obig <> [::] ->
    (exists (O1: obseq) (W1: the_write_stuff), cceval_w C1 O1 Cmid W1) ->
    exists(Wrest: the_write_stuff) (Orest: obseq), inhabited (trace_c Cmid C3 Orest Wrest)
/\ subseq Orest Obig
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
    - apply sub0seq.
      + assert (Tfirst: exists Wrest Orest, inhabited (trace_c Cmid0 Cmid Orest Wrest)
                       /\ subseq Orest O1                           
               ) by (apply IHT1; try assumption).
        destruct Tfirst as [Wrest rest]. destruct rest as [Orest T0mid]. destruct T0mid as [T0mid incl1].
        destruct T0mid as [T0mid].
   exists (append_write Wrest W2) (Orest ++ O2). destruct Orest; split; (try constructor).
    - simpl. apply empty_trace in T0mid. destruct T0mid as [l r].
      subst. rewrite append_write_empty_l. assumption.
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


Lemma eight: forall(N0 N1 N2: nvmem) (V0: vmem) (c0: command),
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
           rewrite filter_predT. assumption.
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
                                                       /\ subseq Orest O).
        intros bigH. destruct bigH as [Wrest blah]. destruct blah as [Orest inhab]. destruct inhab as [inhab inclO].
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
                                                       /\ subseq Orest O).
        intros bigH. destruct bigH as [Wrest blah]. destruct blah as [Orest inhab]. destruct inhab as [inhab inclO].
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
        cut (exists(Wrest: the_write_stuff) (Orest: obseq), inhabited
                                                         (trace_c
                                                            (Nsmall, Vsmall, smallcom)
                                                            (N', V', c')
                                                            Orest Wrest)
                                                       /\ subseq Orest O).
        intros bigH. destruct bigH as [Wrest blah]. destruct blah as [Orest inhab]. destruct inhab as [inhab inclO].
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

Lemma update_sub: forall{N0 N1: nvmem},
    subset_nvm N0 N1 ->
    (N0 U! N1) = N1.
Admitted.


Lemma sub_update: forall(N0 N1: nvmem),
    subset_nvm N0 (N0 U! N1). Admitted.

(*ask arthur how does inversion not cover this*)
Lemma stupid: forall {c: command} {w: warvars},
    c <> ((incheckpoint w);; c).
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
      -> not (checkpoint \in O1)
      -> WARok (getdomain N0) [::] [::] c
      -> subset_nvm N0 N1
      -> inhabited (trace_c (N1, V, c) (NT, VT, Ins skip) OT WT)
      ->not (checkpoint \in OT)
      -> trace_c ((N0 U! N1'), V, c) (NT, VT, Ins skip) OT WT.
Admitted.

(*checkpoint case*)
Lemma twelve01: forall(N0 N1 N1' NCP: nvmem) (V V' VCP: vmem) (c c' cCP: command) (w: warvars) (O1 OCP: obseq)
  (WCP: the_write_stuff),
   multi_step_i ((N0, V, c), N1, V, c) ((N0, V, c), N1', V', c') O1
      -> not (checkpoint \in O1)
      -> WARok (getdomain N0) [::] [::] c
      -> subset_nvm N0 N1
      -> trace_c (N1, V, c) (NCP, VCP, (incheckpoint w);; cCP) OCP WCP
      ->not (checkpoint \in OCP)
      -> inhabited (trace_c ((N0 U! N1'), V, c) (NCP, VCP, (incheckpoint w);; cCP) OCP WCP).
  intros. rename H3 into T.
  destruct_ms H Ti WTi.
  dependent induction Ti. (*makes a diff here w remembering that N1 and N1' are the same*)
  + rewrite (update_sub H2). constructor. assumption.
  + dependent induction i.
     - rewrite (update_sub H2). constructor. assumption.
     - repeat rewrite (update_sub H2). constructor. assumption. 
     - exfalso. apply (stupid x).
     - 
       (*above might be a little broken bc you changed from type
        to prop w/o checking*)
       (*x has been written to
  unfold multi_step_c in H.
  destruct H.*)

Admitted.


Lemma dom_gets_bigger: forall{N1 N1': nvmem} {V V': vmem} {k: context}
                        {c c': command} {O: obseq},
      multi_step_i (k, N1, V, c) (k, N1', V', c') O ->
   subseq (getdomain N1) (getdomain N1').
  Admitted.

Lemma dom_gets_bigger_rb: forall(N0 N1: nvmem),
    subseq (getdomain N1) (getdomain (N0 U! N1)).
  move => [m0 d0] [m1 d1]. simpl. apply suffix_subseq.
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

Lemma update_one: forall{K: context} {N Nend: nvmem} {V Vend: vmem} {c cend: command} {O: obseq} {W R Fw: warvars}
  {l: loc},
    iceval_w (K, N, V, c) O (K, Nend, Vend, cend) (W, R, Fw) ->
    (getmap N) l <> (getmap Nend) l ->
    l \in W.
  intros.
  Admitted.

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
  Admitted.

Lemma fourteen: forall{N0 N Nend: nvmem} {V Vend: vmem} {c cend: command} {O: obseq} {W: the_write_stuff}
                 {l: loc},
    trace_c (N, V, c) (Nend, Vend, cend) O W ->
    checkpoint \notin O ->
    WARok (getdomain N0) [::] [::] c ->
    l \notin (getfstwt W) ->
    l \in (getwt W) ->
    l \in (getdomain N0).
   Admitted. 

Lemma fifteen: forall{N0 N1 N1' N2: nvmem} {V V': vmem} {c c': command} {O: obseq} {W: the_write_stuff},
             iceval_w ((N0, V, c), N1, V, c) O
             ((N0, V, c), N1', V', c') W ->
           not (checkpoint \in O) ->
           not (reboot \in O) ->
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
   exists W. constructor. apply (iTrace_Single H). assumption.
   assumption. assumption. constructor. assumption. assumption.
     apply T2. by left.
       - (*showing N2 subst N0 U! N1'*)
assert (multi_step_i ((N0, V, c), N1, V, c)
                              ((N0, V, c), N1', V', c') O).
         exists W. constructor.  apply (iTrace_Single H).
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
           clear N0eq. 
           unfold updatemaps in H5.
           simpl in H5.
           simpl in H9.
           apply not_true_is_false in H9.
           rewrite H9 in H5.
           simpl.
           (*now have that l is not in D0*)
           left.
    (*inducting on T to split up W0*)
       - dependent induction T.
         Focus 3.
         destruct W1 as [ [W11 R1] Fw1] eqn: W1eq.
         destruct W2 as [ [W22 R2] Fw2] eqn: W2eq.
         unfold append_write.
         simpl.
         suffices: (l \in Fw1).
         intros. rewrite mem_cat.
         apply (introT orP). by left.
         simpl in H8.
         suffices: (l \in W11).
         intros HW1.
         destruct (l \in Fw1) eqn: FWeq; auto.
         apply negbT in FWeq.
         pose proof (negfwandw_means_r T1 FWeq HW1) as Hr.
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
         eapply fourteen; try (assumption).
         apply T1.
         move/ negP : H7.
         rewrite mem_cat.
         case/ norP => Hor1 Hor2. assumption.
         rewrite <- rememberme1. assumption.
         assumption. assumption.
         (*this comes from fact that N1 steps to M1'
          in one (H) but N1 l and M1' of l are different.. new theorem*)    eapply update_one.
         apply H.
         assumption.
                 assert (getdomain N0 = D0).
                               apply fourteen.
                       

         [ contra1 contra2 ].
         move as [ contra1 contra2 ] => contra.
         rewrite orb_false_l.
         intros. rewrite H9 in x. assumption.
         apply H8.
        eapply IHT1. (try assumption).
    pose proof (update_sub H4). rewrite H.
    assumption.
    exfalso. by apply H1.
    exfalso. by apply H0.
    (*
or actually if you're thinking about this linearly
with CMID as N1', taking first step off, then you do want to be using
IH2
doing normal induction did take away some of annoying restrictions
but made bc automation harder, normal induction gave a WEIRD principle...
linear induction might be best
     p sure induction principle is broken
cuz no restriction on CMID actually
making trace smaller, try old format when goal
     was showing something wasn't in FW set... with
     new generality could be more promising
    case H5 as [ w2 [crem2 Heq] ]. subst.
    inversion H; subst.
    pose proof (update_sub H4). rewrite H5.
    assumption.
    exfalso. by apply H0.
    inversion H; subst.
    exfalso. apply (stupid H16).
    inversion H18.*)
(*casing on skip with H5
destruct H6. subst.          eapply valid_mem.
         apply T2. by left.
         assert (multi_step_i ((N0, V, c), N1, V, c)
                              ((N0, V, c), N1', V', c') O).
         exists W. constructor.
         apply (iTrace_Single H).
         apply (subseq_trans
                  (subseq_trans H7 (dom_gets_bigger
                                      H6)) (dom_gets_bigger_rb
                                                    N0 N1')).
         assumption.*)
        -          + assert (not(l \in getdomain N0)).
           unfold subset_nvm in H4. destruct H4 as [H41 H42].
           intros contra. remember contra as contra1.
           clear Heqcontra1. apply H42 in contra1.
           destruct (sub_update N0 N1') as [blah HN1'].
           apply HN1' in contra.
           rewrite contra1 in contra.
           symmetry in contra.
           apply H6 in contra. contradiction.
           destruct N0 as [M0 D0] eqn: N0eq.
           destruct N1' as [M1' D1'] eqn: N1'eq.
           assert (M1' = (getmap N1')) as rememberme.
            by rewrite N1'eq. 
           assert (M1 = (getmap N1')) as rememberme.
            by rewrite N1'eq. 
           clear N0eq. 
           unfold updatemaps in H6.
           simpl in H6.
           simpl in H10.
           apply not_true_is_false in H10.
           rewrite H10 in H6.
           simpl.
           left.
           (*inducting on N1' U! N0 --> skip
            to split up W0*)
       - dependent induction H.
         (*inducting on iceval to get relationship
          between N1 and N1'
          should do this further up for a simpler IH?*)
        + simpl in H6. exfalso.
            by apply H6.
        +exfalso. by apply H1.
        + exfalso. by apply H0.
       - inversion H5; subst.
(*inverting cceval N1 -> skip to get info
 about W0 not given by trace induction
 maybe induct on the cceval instead?*)
           suffices: (l = (inl x0)).
       - intros Heq. subst. simpl.
         suffices: ((inl x0) \notin (readobs_wvs r0)).
         intros Hnin. rewrite Hnin. by rewrite mem_seq1.
         + simpl in H4.
           inversion H4; subst;
           inversion H17; subst.
           exfalso. apply (negNVandV x0 H0 H25).
(*why double eeval relations here.. i think the
 cceval and iceval*)
           pose proof (read_deterministic H20 (RD H21)) as rdeq.
           rewrite <- rdeq.
           simpl in H26.
           apply not_true_is_false in H26.
           apply (negbT H26).
         + rewrite H11 in H28. discriminate H28.
         + discriminate H26.
       - rewrite rememberme in H12. rewrite <- x in H12.
         apply (updateone_sv H12).
       - subst. exfalso. apply (negNVandV x0 H0 H22).
         exfalso. by apply H12. 
       - inversion H5; subst; simpl.
         destruct (determinism_e H23 H) as [Heq1 Heq2].
         subst.
         destruct (determinism_e H24 H0) as [Heq1 Heq2].
         subst.
         destruct (equal_index_works H1 H25).
         (*pose proof (determinism_e H22 H23) as Heq11.*)
         suffices: (l = (inr element)).
       - intros Heq. subst.
         suffices: ((inr element) \notin (readobs_wvs (r ++ ri))).
         intros Hnin. rewrite Hnin. by rewrite mem_seq1.
         + 
           simpl in H6.
           inversion H6; subst;
             inversion H18; subst.
           rewrite readobs_app_wvs.
           apply RD in H23.
           apply RD in H24.
           apply (read_deterministic H23) in H28.
           apply (read_deterministic H24) in H21.
           rewrite H28. rewrite H21.
           destruct (inr element \notin Re ++ Rindex) eqn: beq1; auto.
           move/negPn: beq1 => beq1.
           exfalso.
           apply H29.
           exists (inr element: loc).
           split.
           destruct element.
           apply (gen_locs_works H25).
           assumption.
                    (*ask arthur
                     if there is a better way than beq1
                     also ask about why you have to destruct element
                     to get the types to match...
                     destruct should not change the type?*)
      - (*problem is H11 and H25
           nts inr element in genlocs A*)
          suffices: (inr element \in D0).
          rewrite H12. intros contra.
          discriminate contra.
          destruct element.
          apply (in_subseq H30 (gen_locs_works H25)).
          rewrite rememberme in H13. rewrite <- x in H13.
          apply (updateone_arr H13).
      - exfalso. by apply H6.
      - (*not convinced this case
         is even legal cuz you have
         l;;c' -> skip in one step c0*)
        inversion H5; subst; try 
       (exfalso; by apply H8);
        try (exfalso; by apply H20);
        try (exfalso; by apply H6).
        exfalso; by apply H6.
        exfalso; by apply H6.
        (*fix the above*)
        apply H9.
          by move/ eqP : beq.
          Focus 2.
          case H5 as
              [Cmid [T1 P1] ].
          case P1 as
              [P1 T2].
          case T2 as
              [T2 P2].
          (*maybe dependent
           induction is the problem?*)
          destruct3 Cmid nmid vmid cmid.
          eapply IHT1;
            first (apply H);
            (try assumption);
            try reflexivity.
          reflexivity.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.


        inversion H.
        exfalso. by apply H21.
        exfalso. by apply H5.
        exfalso. by apply H5.
        unfold append_write. simpl.
        suffices: (l \in getfstwt W0).
        intros. left. assumption.
        apply/ in_subseq / prefix_subseq.
        eapply IHT1. (try assumption); auto.
        apply H.
        assumption.
        assumption.
        assumption.
        discriminate H5.
          pose proof (equal_index_arr H24).
          subst.
          pose proof (equal_index_arr H9). subst.
          

(*Lemma fifteen: forall{N0 N1 N1' N2: nvmem} {V V': vmem} {c c': command} {O: obseq} {W: the_write_stuff},
             iceval_w ((N0, V, c), N1, V, c) O
             ((N0, V, c), N1', V', c') W ->
           not (checkpoint \in O) ->
           not (reboot \in O) ->
             WARok (getdomain N0) [::] [::] c ->
             current_init_pt N0 V c N1 N1 N2 ->
             subset_nvm N0 N1 ->
             current_init_pt N0 V c (N0 U! N1') (N0 U! N1') N2.
intros. inversion H3. 
       destruct H5. subst.
       suffices:
         (inhabited (trace_c ((N0 U! N1'), V, c) (Nend, Vend, Ins skip) O0 W)).
       Admitted.

Lemma fifteen0:forall{N0 N1 N2: nvmem} {V V': vmem} {il : instruction}
                {c': command} {o: obs} {W: the_write_stuff},
           current_init_pt N0 V (Ins il) N1 N1 N2 ->
WARok (getdomain N0) [::] [::] (il;;c') ->
current_init_pt N0 V (il;;c') N1 N1 N2.
  intros. .


Lemma fifteen0: forall{N0 N1 N1' N2: nvmem} {V V': vmem} {il : instruction}
                 {c': command} {o: obs} {W: the_write_stuff},
             iceval_w ((N0, V, il;;c'), N1, V, Ins il) [::o]
             ((N0, V, il;;c'), N1', V', Ins skip) W ->
           not (checkpoint \in [::o]) ->
           not (reboot \in [::o]) ->
             WARok (getdomain N0) [::] [::] (il;;c') ->
             current_init_pt N0 V (il;;c') N1 N1 N2 ->
             subset_nvm N0 N1 ->
             current_init_pt N0 V (il;; c') (N0 U! N1') (N0 U! N1') N2.
intros. inversion H3. 
       destruct H5. subst.
       suffices:
         (inhabited (trace_c ((N0 U! N1'), V, (il;;c')) (Nend, Vend, Ins skip) O W0)).
       + case => Tc.
         eapply valid_mem.
         apply Tc. by left.
         assert (multi_step_i ((N0, V, (il;;c')), N1, V, (il;;c'))
                              ((N0, V, (il;;c')), N1', V', c') [::o]).
         exists W. constructor.
         apply (iTrace_Single (CP_Seq
                                 _ _ _ _ _ _ _ _ _
                                 H)).
         apply (subseq_trans
                  (subseq_trans H6 (dom_gets_bigger
                                      H5)) (dom_gets_bigger_rb
                                                    N0 N1')).
         assumption.
       - intros.
         destruct (getmap N1 l == getmap N2 l) eqn: beq.
           move/eqP :beq => beq. rewrite <- beq in H5.
         + assert (not(l \in getdomain N0)).
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
           clear N0eq. 
           unfold updatemaps in H5.
           simpl in H5.
           simpl in H9.
           apply not_true_is_false in H9.
           rewrite H9 in H5.
           left.
           dependent induction H.
           (*original lemma 15 starts below*)
        (* + simpl in H5. exfalso.
             by apply H5.
         + exfalso. by apply H1.
         + exfalso. apply (stupid x).*)
         + simpl.
           suffices: (l = (inl x0)).
       - intros Heq. subst.
         suffices: ((inl x0) \notin (readobs_wvs r)).
         intros Hnin. rewrite Hnin. by rewrite mem_seq1.
         + simpl in H4.
           inversion H4; subst.
           inversion H17; subst.
           exfalso. apply (negNVandV x0 H0 H22).
           pose proof (read_deterministic H20 (RD H)) as rdeq.
           rewrite <- rdeq.
           simpl in H23.
           apply not_true_is_false in H23.
           apply (negbT H23).
         + rewrite H25 in H10. discriminate H10.
         + discriminate H23.
       - rewrite rememberme in H11. rewrite <- x in H11.
         apply (updateone_sv H11).
       - exfalso. apply H11. by rewrite rememberme.
       - simpl.
         suffices: (l = (inr element)).
       - intros Heq. subst.
         suffices: ((inr element) \notin (readobs_wvs (r ++ ri))).
         intros Hnin. rewrite Hnin. by rewrite mem_seq1.
         + simpl in H5.
           inversion H5; subst.
             inversion H18; subst.
           rewrite readobs_app_wvs.
           apply RD in H.
           apply RD in H0.
           apply (read_deterministic H0) in H21.
           apply (read_deterministic H) in H24.
           rewrite H21. rewrite H24.
           destruct (inr element \notin Re ++ Rindex) eqn: beq1; auto.
           move/negPn: beq1 => beq1.
           exfalso.
           apply H25.
           exists (inr element: loc).
           split.
           destruct element.
           apply (gen_locs_works H1).
           assumption.
                    (*ask arthur
                     if there is a better way than beq1
                     also ask about why you have to destruct element
                     to get the types to match...
                     destruct should not change the type?*)
      - (*problem is H11 and H25
           nts inr element in genlocs A*)
          suffices: (inr element \in D0).
          rewrite H11. intros contra.
          discriminate contra.
          destruct element.
          apply (in_subseq H26 (gen_locs_works H1)).
          rewrite rememberme in H12. rewrite <- x in H12.
          apply (updateone_arr H12).
+ move/ eqP : beq. move/ H8. 


          exfalso. by apply H5.
          apply negbT in H11.

         
          apply: H11.
           inversion H20. inversion H23. subst.
           intros contra.



           exfalso. apply (negNVandV x0 H0 H21).
           pose proof (read_deterministic H19 (RD H)) as rdeq.
           rewrite <- rdeq.
           simpl in H22.
           apply not_true_is_false in H22.
           apply (negbT H22).
         + rewrite H24 in H10. discriminate H10.
         + discriminate H22.


(*15 original theorem statement
Lemma fifteen0: forall{N0 N1 N1' N2: nvmem} {V V': vmem} {c c': command} {O: obseq} {W: the_write_stuff},
             iceval_w ((N0, V, c), N1, V, c) O
             ((N0, V, c), N1', V', c') W ->
           not (checkpoint \in O) ->
           not (reboot \in O) ->
             WARok (getdomain N0) [::] [::] c ->
             current_init_pt N0 V c N1 N1 N2 ->
             subset_nvm N0 N1 ->
             current_init_pt N0 V c (N0 U! N1') (N0 U! N1') N2.*)

Lemma twelve: forall(N0 N1 N1' N2: nvmem) (V V': vmem) (c c': command) (O: obseq),
           multi_step_i ((N0, V, c), N1, V, c) ((N0, V, c), N1', V', c') O ->
           not (checkpoint \in O) ->
           not (reboot \in O) ->
             WARok (getdomain N0) [::] [::] c ->
             current_init_pt N0 V c N1 N1 N2 ->
             subset_nvm N0 N1 ->
             current_init_pt N0 V c (N0 U! N1') (N0 U! N1') N2.
Proof. intros. inversion H3. 
       destruct H4. subst.
       suffices:
         (inhabited (trace_c ((N0 U! N1'), V, c) (Nend, Vend, Ins skip) O0 W)).
       + case => Tc.
         eapply valid_mem.
         apply Tc. by left.
         apply (subseq_trans
           (subseq_trans H5 (dom_gets_bigger H)) (dom_gets_bigger_rb
                                                    N0 N1')).
         assumption.
       - intros.
         destruct (getmap N1 l == getmap N2 l) eqn: beq.
           move/eqP :beq => beq. rewrite <- beq in H4.
         + assert (not(l \in getdomain N0)).
           unfold subset_nvm in H3. destruct H3 as [H31 H32].
           intros contra. remember contra as contra1.
           clear Heqcontra1. apply H32 in contra1.
           destruct (sub_update N0 N1') as [blah HN1'].
           apply HN1' in contra.
           rewrite contra1 in contra.
           symmetry in contra.
           apply H4 in contra. contradiction.
           destruct N0 as [M0 D0].
           destruct N1' as [M1' D1'].
           unfold updatemaps in H4.
           simpl in H4.
           simpl in H8.
           apply not_true_is_false in H8.
           rewrite H8 in H4.
           (*war time!*)
           left.
           (*induct over N1 -> N1'*)
           inversion H as [W_NN1' destroyme].
           destruct destroyme as [T_N1N1'].
           dependent induction T_N1N1'.
           simpl in H4.
           exfalso. by apply H4.
           (*single step case*)
           simpl in H7.
           unfold is_true in H8.
           apply introF in H8. rewrite H8 in H4.
           rewrite contra in H4.*)
           


Lemma 12.0: forall(N0 N1 N1': nvmem) (V V': vmem) (c0 c1 crem: command)
  (Obig Osmall: obseq) (Wbig Wsmall: the_write_stuff),
    WARok N0 [] [] [] c0 ->
    multistep_c ((N0, V, c0), N1, V, c0) ((N0, V, c0), N1', V', c)
    iceval ((N0, V, c0), N1, V, c0) ((N0, V, c0), N1', V', c1) Osmall Wsmall ->
    

