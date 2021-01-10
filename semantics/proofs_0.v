Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Strings.String Program Logic.FunctionalExtensionality.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq fintype ssrnat ssrfun.
From TLC Require Import LibTactics LibLogic.
From Semantics Require Export programs semantics algorithms lemmas_1
lemmas_0. (*shouldn't have to import both of these*)

Implicit Types N: nvmem. Implicit Types V: vmem.
Implicit Types O: obseq.
Implicit Types c: command.
Implicit Types W: the_write_stuff.
Implicit Types x: smallvar.
(*start here should be a way to stack these*)

Open Scope type_scope.

(*
mapim f m == apply the function f : T -> S -> S' to all bindings in   *)
(*                   the map m : {fmap T -> S}.  
ask arthur start here... each singular input/output is its OWN T->S?
 *)

(*lemmas for the lemmas; not in paper*)
Lemma sub_disclude N0 N1 N2:  forall(l: loc),
                     subset_nvm N0 N1 ->
                     subset_nvm N0 N2 ->
                     not ((getmap N1) l = (getmap N2) l)
                     -> not (l \in (getdomain N0)).
Proof. intros. intros contra. unfold subset_nvm in H. (*destruct H.*)
       remember contra as contra1. clear Heqcontra1.
       apply H in contra.
       unfold subset_nvm in H0. (*destruct H0.*) apply H0 in contra1.
       symmetry in contra.
       apply (eq_trans _ _ _ contra) in contra1.
       apply H1. assumption.
Qed.


Lemma wt_subst_fstwt_c: forall{C1 C2: context} {O: obseq} {W: the_write_stuff},
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

Lemma fw_s_w_ceval: forall{C1 C2: context} {O: obseq} {W: the_write_stuff},
      (* pose proof (cceval_to_rd_sv H H5). *)
  cceval_w C1 O C2 W ->
    subseq (getfstwt W) (getwt W).
Admitted.

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

Lemma fw_subst_wt_c: forall{C1 C2: context} {O: obseq} {W: the_write_stuff},
      (* pose proof (cceval_to_rd_sv H H5). *)
  cceval_w C1 O C2 W ->
  subseq (getfstwt W) (getwt W). Admitted.

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

Lemma negNVandV: forall(x : smallvar), isNV x -> not (isV x).
Proof. unfold isNV. unfold isV.
       unfold isNV_b. unfold isV_b.
       move => [s v]. destruct v; auto. (*ask arthur do both destructs at once?*)
Qed.
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


Lemma single_step_alls_rev: forall{C1 C3: context}
                    {Obig : obseq} {Wbig: the_write_stuff},
    trace_cs C1 C3 Obig Wbig ->
    Obig <> [::] ->
    exists(Cmid: context) (W1 Wrest: the_write_stuff) (O1: obseq),
      cceval_w C1 O1 Cmid W1
/\ subseq O1 Obig /\ Wbig = (append_write W1 Wrest).
Admitted.

 Lemma genloc_contents: forall(l: loc) (a: array),
              l \in generate_locs a ->
                    exists (el: el_loc), inr el = l.
   Admitted.

 Lemma fw_split {W W1} {l: loc}:
           l \in getfstwt (append_write W1 W) ->
                 l \in (getfstwt W1) \/ (
                         l \notin (getrd W1)
                           /\ l \in (getfstwt W)
                       ).
  intros.
           (*intros Hdoneb. apply Hdoneb in Hl0.*)
           destruct W as [ [wW rW] fwW].
           destruct W1 as [ [wW1 rW1] fwW1].
           simpl in H.
           unfold remove in H.
           rewrite mem_cat in H.
           rewrite mem_filter in H.
           move/ orP : H => [one | two].
           right.
             by move/ andP : one.
              by left.
Qed.

Lemma single_step_alls: forall{C1 Cmid C3: context}
                    {Obig O1 : obseq} {W1 Wbig: the_write_stuff},
    trace_cs C1 C3 Obig Wbig ->
    Obig <> [::] ->
     cceval_w C1 O1 Cmid W1 ->
    exists(Wrest: the_write_stuff) (Orest: obseq), trace_cs Cmid C3 Orest Wrest
/\ subseq Orest Obig /\ Wbig = (append_write W1 Wrest).
Admitted.

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

Lemma sub_update: forall(N0 N1: nvmem),
    subset_nvm N0 (N0 U! N1).
  intros.
  destruct N0, N1.
  unfold subset_nvm. (*split.
  simpl. apply prefix_subseq.*)
  intros. simpl. by rewrite H.
  Qed.

(*ask arthur how does inversion not cover this*)
Lemma stupid: forall (c: command) (l: instruction),
    c <> (l ;; c).
  move => c w contra.
  induction c; inversion contra.
    by apply IHc. Qed.

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

(*Lemma update_one: forall{N N0 Nend: nvmem} {V V0 Vend: vmem} {c c0 cend: command} {O: obseq} {W: the_write_stuff}
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
  Qed.*)


Lemma update_one_c: forall{N Nend: nvmem} {V Vend: vmem} {c cend: command} {O: obseq} {W: the_write_stuff}
  (l: loc),
    cceval_w (N, V, c) O (Nend, Vend, cend) W ->
    ~~((getmap N) l == (getmap Nend) l) ->
    l \in (getwt W).
Admitted.

Lemma update_one_contra: forall{N Nend: nvmem} {V Vend: vmem} {c cend: command} {O: obseq} {W: the_write_stuff}
  (l: loc),
    cceval_w (N, V, c) O (Nend, Vend, cend) W ->
    l \notin (getwt W) -> 
    (getmap N) l = (getmap Nend) l.
Admitted.

Lemma update: forall{N Nend: nvmem} {V Vend: vmem} {c cend: command} {O: obseq} {W: the_write_stuff}
  {l: loc},
    trace_cs (N, V, c) (Nend, Vend, cend) O W ->
    (getmap N) l <> (getmap Nend) l ->
    l \in (getwt W).
  Admitted.

(*start here replace this with
 iceval_cceval1*)
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

Lemma cceval_skip: forall {N N': nvmem} {V V': vmem}
                    {l: instruction} {c: command}
  {O: obseq} {W: the_write_stuff},
    cceval_w (N, V, Ins l) O (N', V', c) W ->
    (c = skip). Admitted.

Lemma agr_imp_age:
forall{N0 N1: nvmem} {V0: vmem} {e: exp} {r0: readobs} {v0: value},
  eeval N0 V0 e r0 v0 ->
  (forall(z: loc), z \in (readobs_wvs r0 ) -> (getmap N0) z = (getmap N1) z) -> (*they concur
                                                                          on all
                                                                          values read
                                                                          from*)
              eeval N1 V0 e r0 v0.
  intros. Admitted.

Lemma if_ctx {N V e N1 V1 c1 c2 c3 O W}:
  cceval_w (N, V, TEST e THEN c1 ELSE c2) O (N1, V1, c3) W ->
  N = N1 /\ V = V1.
Admitted.
