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

(*grammar*)

Lemma no_CP_in_seq: forall{O1 O2: obseq},
    (O1 <=m O2) -> checkpoint \notin O1 /\ checkpoint \notin O2.
  Admitted.

Lemma both_cp {O1 O2} :
    (O1 <=f O2) -> checkpoint \notin O1 ->
    (O1 <=m O2) /\ checkpoint \notin O2.
    Admitted.

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
  apply (map_f (fun i0 => inr (El (Array n l) i0)))
  .
  by rewrite mem_enum.
Qed.

(*mems*)
Lemma sub_restrict: forall(N1: nvmem) (w: warvars) (Hf: wf_dom w (getmap N1)), subset_nvm
                                                                   (restrict N1 w Hf) N1.
  intros.
  unfold subset_nvm.
  intros l Hl. destruct N1 as [ nm nd nh].
  unfold restrict. simpl. simpl in Hl.
  rewrite ifT; try by []. Qed.

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

Lemma negNVandV: forall(x : smallvar), isNV x -> not (isV x).
Proof. unfold isNV. unfold isV.
       unfold isNV_b. unfold isV_b.
       move => [s v]. destruct v; auto. (*ask arthur do both destructs at once?*)
Qed.


Lemma update_diff N0 N1 N2: forall(l: loc),
    ((getmap N1) l != (getmap (N0 U! N2)) l) ->
  ((getmap N0) l <> (getmap N1) l /\ l \in (getdomain N0)) \/
  ( (getmap N2) l <> (getmap N1) l /\ l \notin (getdomain N0)
  ).
  intros.
  destruct N0 as [ m0 d0 h0].
  destruct N1 as [ m1 d1 h1].
  destruct N2 as [ m2 d2 h2].
  simpl. simpl in H.
  destruct (l \in d0) eqn: Hbool; try (move/ negbT : Hbool => Hbool). 
    rewrite ifT in H; try by [].
  left. split. apply not_eq_sym. move/ eqP: H. by apply.
    by apply Hbool.
rewrite ifF in H; try by []. right. split. apply not_eq_sym. move/ eqP: H. by apply. by [].
by apply negbTE.
Qed.


Lemma sub_update: forall(N0 N1: nvmem),
    subset_nvm N0 (N0 U! N1).
  intros.
  destruct N0, N1.
  unfold subset_nvm. (*split.
  simpl. apply prefix_subseq.*)
  intros. simpl. by rewrite H.
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
  destruct (v == error) eqn: Hbool. exfalso. by apply H.
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
  unfold updatemap in H.
  destruct (v == error) eqn: Hbool. exfalso. by apply H.
  rewrite beq in H.
  exfalso. by apply H. 
  Qed.
(*the write stuff*)

Lemma fw_subst_wt_c: forall{C1 C2: context} {O: obseq} {W: the_write_stuff},
      (* pose proof (cceval_to_rd_sv H H5). *)
  cceval_w C1 O C2 W ->
  subseq (getfstwt W) (getwt W). Admitted.

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


  Lemma fw_nin_r_bc {N V} {i: instruction}: forall{C2: context} {O: obseq} {W: the_write_stuff} (l: loc),
    cceval_w (N, V, Ins i) O C2 W ->
    l \in (getrd W) ->
          l \notin  (getfstwt W).
  intros. inversion H; subst; try by [];
  simpl; simpl in H0.
  destruct (inl x \notin readobs_wvs r) eqn: Hbool.
  rewrite ifT; try by [].
  rewrite mem_seq1.
  apply/ eqP. intros contra. subst.
  rewrite H0 in Hbool. discriminate Hbool.
  rewrite ifF; try by [].

  destruct (inr element \notin readobs_wvs (r ++ ri)) eqn: Hbool.
  rewrite ifT; try by [].
  rewrite mem_seq1.
  apply/ eqP. intros contra. subst.
  rewrite H0 in Hbool. discriminate Hbool.
  rewrite ifF; try by []. Qed.

Lemma fw_nin_r_c: forall{C1 C2: context} {O: obseq} {W: the_write_stuff} (l: loc),
    cceval_w C1 O C2 W ->
    l \in (getrd W) ->
          l \notin  (getfstwt W).
  intros. destruct C1 as [ [nm vm] cm].
  dependent induction cm.
  eapply fw_nin_r_bc; try apply H; try assumption.
  inversion H; subst; try by [].
  eapply fw_nin_r_bc; try apply H10; try assumption.
  inversion H; try by []. Qed.

Lemma negfwandw_means_r: forall{C Cend: context}  {O: obseq} {W: the_write_stuff}
  {l: loc},
    cceval_w C O Cend W ->
    l \notin (getfstwt W) -> l \in (getwt W) -> l \in (getrd W).
Admitted.


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
(*single step evaluation*)

Lemma cceval_steps1:forall{N Nmid: nvmem} {V Vmid: vmem} {c cmid: command}
                   {O: obseq} {W: the_write_stuff},

        cceval_w (N, V, c) O (Nmid, Vmid, cmid) W ->
        cmid <> c.
  intros. inversion H; subst; try apply stupid; try (intros contra;
                                                     discriminate contra).
by apply stupid1. by apply stupid2.
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

Lemma determinism_e: forall{N: nvmem} {V: vmem} {e: exp} {r1 r2: readobs} {v1 v2: value},
    eeval N V e r1 v1 ->
    eeval N V e r2 v2 ->
    r1 = r2 /\ v1 = v2.
Proof. intros N V e r1 r2 v1 v2 H. move: r2 v2.
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
   pose proof (equal_index_works H2 H6));
         try (subst;
              split; [reflexivity | (split; reflexivity)]).
         exfalso. by apply (H0 w).
Qed.

Lemma observe_checkpt_s: forall {N N': nvmem} {V V': vmem}
                     {c c' : command} {w: warvars}
                    {O: obseq} {W: the_write_stuff},
    cceval_w (N, V, (incheckpoint w ;; c)) O (N', V', c') W ->
    checkpoint \in O.
  intros. inversion H; subst; try by [].
  exfalso. by apply (H9 w). Qed.

Lemma cceval_agr_bc: forall{N1 N2 :nvmem} {V1 V2: vmem} {l: instruction}
                   {O1 O2 : obseq} {W1 W2: the_write_stuff}
  {C1 C2: context},
    cceval_w (N1, V1, Ins l) O1 C1 W1 ->
    cceval_w (N2, V2, Ins l) O2 C2 W2 ->
    (getrd W1) = (getrd W2).
  intros. move: H H0 => Hcceval1 Hcceval2.
  dependent induction Hcceval1; inversion Hcceval2; subst; try by [];
try by move: (read_deterministic (RD H) (RD H9)).
  simpl. move: (read_deterministic (RD H) (RD H11))
                 (read_deterministic (RD H0) (RD H12)) => one two.
  repeat rewrite readobs_app_wvs. by rewrite one two. 
Qed.


Lemma cceval_agr: forall{N1 N2 :nvmem} {V1 V2: vmem} {c: command}
                   {O1 O2 : obseq} {W1 W2: the_write_stuff}
  {C1 C2: context},
    cceval_w (N1, V1, c) O1 C1 W1 ->
    cceval_w (N2, V2, c) O2 C2 W2 ->
    (getrd W1) = (getrd W2).
  intros. move: H0 => Hcc2.
  move: N2 V2 O2 C2 W2 Hcc2.
  induction c; intros.
  apply (cceval_agr_bc H Hcc2).
  inversion H; subst; inversion Hcc2; subst; try by [];
  try (exfalso; by apply (H8 w)); try (exfalso; by apply (H7 w)).
  apply (cceval_agr_bc H9 H12).
  inversion H; subst; inversion Hcc2; subst; try (move: (read_deterministic (RD H8) (RD H9)) => Heq; by subst).
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

Lemma update_one_c: forall{N Nend: nvmem} {V Vend: vmem} {c cend: command} {O: obseq} {W: the_write_stuff}
  (l: loc),
    cceval_w (N, V, c) O (Nend, Vend, cend) W ->
    ~~((getmap N) l == (getmap Nend) l) ->
    l \in (getwt W).
  intros. move: l H0. dependent induction H; intros z Hz;
                        try (exfalso; move/ negP : Hz; by apply); simpl; try (rewrite mem_seq1; apply/ eqP).
eapply updateone_sv. apply not_eq_sym. move/ eqP : Hz. apply.
eapply updateone_arr. apply not_eq_sym. move/ eqP : Hz. apply.
eapply IHcceval_w; try reflexivity; try assumption.
Qed.

Lemma update_one_contra: forall{N Nend: nvmem} {V Vend: vmem} {c cend: command} {O: obseq} {W: the_write_stuff}
  (l: loc),
    cceval_w (N, V, c) O (Nend, Vend, cend) W ->
    l \notin (getwt W) -> 
    (getmap N) l = (getmap Nend) l.
  intros. apply/ eqP /negPn. move : H0. apply contra.
  apply (update_one_c l H). Qed.

Lemma update_onec {N11 N12 V11 V12 N21 N22 V21 V22
                       c c1 c2 O1 O2 W} {l: loc} :
  cceval_w (N11, V11, c) O1 (N12, V12, c1) W ->
  cceval_w (N21, V21, c) O2 (N22, V22, c2) W ->
    (getmap N11) l = (getmap N21) l ->
    (getmap N12) l <> (getmap N22) l ->
    l \in (getwt W).
  intros.
  suffices: ~~((getmap N11 l) == (getmap N12 l)) \/
            ~~((getmap N21 l) == (getmap N22 l)).
  move => [case | case]; try (eapply update_one_c in case; try apply case
                            ; try apply H; try apply H0).
  apply/nandP / negP. intros contra.
  move/ andP : contra => [con1 con2].
  move/ eqP: con1 => eq1. move/ eqP: con2 => eq2.
  apply H2. rewrite - eq1. by rewrite - eq2. Qed.

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
     intros. move: N1 H0. dependent induction H; intros.
     - by apply VAL.
     -
       assert ((forall z : loc, z \in readobs_wvs r1 -> getmap N z = getmap N1 z) /\
       (forall z : loc, z \in readobs_wvs r2 -> getmap N z = getmap N1 z)) as Hz.
      rewrite readobs_app_wvs in H2. split; intros z Hin.
       apply (in_subseq (prefix_subseq (readobs_wvs r1) (readobs_wvs r2))) in Hin.
       by apply H2.
       apply (in_subseq (suffix_subseq (readobs_wvs r1) (readobs_wvs r2))) in Hin.
         by apply H2.
         move : Hz => [Hz1 Hz2].
         apply IHeeval1 in Hz1. apply IHeeval2 in Hz2.
         apply BINOP; try assumption.
     - apply RD_VAR_NV; try assumption. suffices: (getmap N (inl x)) = (getmap N1 (inl x)).
       move => Heq. unfold getvalue. rewrite - Heq. by apply H. apply H2.
       simpl. apply mem_head.
     - apply RD_VAR_V; try assumption.
     - rewrite readobs_app_wvs in H3. eapply RD_ARR; try assumption. 
       assert (forall z : loc, z \in readobs_wvs rindex -> getmap N z = getmap N1 z) as Hz.
       intros z Hin. 
       apply (in_subseq (prefix_subseq (readobs_wvs rindex) (readobs_wvs [::(inr element, v)]))) in Hin.
         by apply H3. by apply IHeeval.
suffices: (getmap N (inr element)) = (getmap N1 (inr element)).
move => Heq. unfold getvalue. rewrite - Heq. by apply H0. apply H3.
rewrite mem_cat. apply/orP. right. destruct element as [a0 i]. simpl. rewrite cats0.
rewrite genloc_getarr. by []. assumption.
Qed.

Lemma if_ctx {N V e N1 V1 c1 c2 c3 O W}:
  cceval_w (N, V, TEST e THEN c1 ELSE c2) O (N1, V1, c3) W ->
  N = N1 /\ V = V1.
Admitted.

Lemma cceval_steps: forall{N Nmid: nvmem} {V Vmid: vmem} {c cmid: command}
                   {O: obseq} {W: the_write_stuff} {l: instruction},

        cceval_w (N, V, l;;c) O (Nmid, Vmid, cmid) W ->
        c = cmid.
intros. inversion H; subst; try reflexivity. Qed.


  Lemma connect_mems {N N' V Nmid Nmid' Vmid W O z} {l: instruction}:
cceval_w (N, V, Ins l) O (Nmid, Vmid, Ins skip) W ->
cceval_w (N', V, Ins l) O (Nmid', Vmid, Ins skip) W ->
z \notin (getwt W) ->
getmap N z = getmap N' z ->
getmap Nmid z = getmap Nmid' z.
    intros Hcceval1 Hcceval2 Hbool Heq.
       move : (update_one_contra z Hcceval1) => Heq1.
       move : (update_one_contra z Hcceval2) => Heq2.
       remember Hbool as Hbool2. clear HeqHbool2.
       apply Heq1 in Hbool.
       apply Heq2 in Hbool2.
symmetry in Hbool.
  by move: (trans_eq (trans_eq Hbool Heq) Hbool2).
  Qed.

(*traces*)
Lemma empty_trace_cs1: forall{C1 C2: context} {W: the_write_stuff},
    trace_cs C1 C2 [::] W -> C1 = C2 /\ W = emptysets.
  intros. dependent induction H.
  split; by  [].
  inversion H; subst.
  inversion H2; subst.
  exfalso. apply H0.
  apply/ nilP.
  move/ nilP /eqP : x. rewrite size_cat => contra.
    move/ eqP: contra => contra.
    rewrite addn_eq0 in contra.
    move/ andP: contra => [one two]. by apply two.
    Qed.

Lemma size_dec_c:
  forall{N1 N2: nvmem} {V1 V2: vmem} {c c1: command} {O: obseq} {W: the_write_stuff},
    cceval_w (N1, V1, c) O (N2, V2, c1) W -> ltn%N (size_com c1) (size_com c).
  intros.
  inversion H; subst; simpl; try by [].
  rewrite ltn_addr; try by [].
  rewrite addnC.
  rewrite addnA.
  rewrite ltn_addr; try by [].
  rewrite addnC. by [].
Qed.

Lemma size_dec:
  forall{N1 N2: nvmem} {V1 V2: vmem} {c c1: command} {O: obseq} {W: the_write_stuff},
    trace_cs (N1, V1, c) (N2, V2, c1) O W -> leq (size_com c1) (size_com c).
  intros. dependent induction H.
    by [].
    move: (size_dec_c H) => done.
    rewrite leq_eqVlt.
    apply/orP. by right.
    destruct Cmid as [ [nm vm] cm].
    suffices: (leq (size_com c1) (size_com cm)).
    intros one.
    move: (size_dec_c H1) => two.
    move/ ltP / ltP : two => two.
    rewrite (ltn_neqAle (size_com cm) (size_com c)) in two.
    move/ andP : two => [three four].
    apply (leq_trans one four).
    eapply IHtrace_cs; try reflexivity.
Qed.

Lemma empty_trace_cs:
  forall{N1 N2: nvmem} {V1 V2: vmem} {c: command} {O: obseq} {W: the_write_stuff},
    trace_cs (N1, V1, c) (N2, V2, c) O W -> O = [::] /\ N1 = N2 /\ V1 = V2 /\ W = emptysets.
  intros. dependent induction H.
  repeat split; by [].
  apply cceval_steps1 in H.
  exfalso. by apply H.
  destruct Cmid as [ [nm vm] cm].
  move: (size_dec H) (size_dec_c H1) => one two.
  move: (leq_ltn_trans one two) => contra.
  rewrite ltnn in contra. discriminate contra.
Qed.


Lemma determinism: forall{C1: context} {N1 N2: nvmem} {V1 V2: vmem} {cend: command} {O1 O2: obseq} {W1 W2: the_write_stuff},
    trace_cs C1 (N1, V1, cend) O1 W1 ->
    trace_cs C1 (N2, V2, cend) O2 W2 ->
    O1 = O2 /\ W1 = W2. intros.
move: N2 V2 O2 W2 H0; dependent induction H; intros.
3: {
destruct Cmid as [ [nm vm ] cm].
inversion H2; subst.
move: (CsTrace_Cons H H0 H1) => Tc.
move/empty_trace_cs : Tc => [contra1 [contra2 [contra3 contra4] ] ].
split; assumption.
move: (determinism_c H1 H3). => [contra1 [contra2 contra4] ] .
inversion contra1. subst.
move/empty_trace_cs : H => [contra11 [contra2 [contra3 contra4] ] ].
exfalso. by apply H0.
move: (determinism_c H1 H5) => [one [two three] ]. subst.
suffices: (O2 = O4) /\ (W2 = W4).
move=> [one two]. subst. split; by [].
eapply IHtrace_cs; try reflexivity. apply H3.
}
move/empty_trace_cs : H0 => [one [two [three four] ] ]. by subst.
inversion H0; subst. apply cceval_steps1 in H. exfalso. by apply H. 
move: (determinism_c H H1) => [one [two three] ]. by subst.
destruct Cmid as [ [nm vm ] cm].
move: (determinism_c H H3). => [contra1 [contra2 contra4] ] .
inversion contra1. subst.
move/empty_trace_cs : H1 => [contra11 [contra2 [contra3 contra4] ] ].
exfalso. by apply H2. Qed.

Lemma single_step_alls: forall{C1 Cmid C3: context}
                    {Obig O1 : obseq} {W1 Wbig: the_write_stuff},
    trace_cs C1 C3 Obig Wbig ->
    Obig <> [::] ->
     cceval_w C1 O1 Cmid W1 ->
    exists(Wrest: the_write_stuff) (Orest: obseq), trace_cs Cmid C3 Orest Wrest
/\ (Obig = O1 ++ Orest) /\ Wbig = (append_write W1 Wrest).
  intros. move: H H0 H1 => T Hob Hcc.
  move: Cmid O1 W1 Hcc. dependent induction T; intros.
  3: {
   move: (determinism_c H0 Hcc) => [one [two three] ]. subst. 
   exists W2 O2. repeat split; try by [].
  }
  exfalso. by apply Hob.
   move: (determinism_c H Hcc) => [one [two three] ]. subst. 
   exists emptysets ([::]: obseq). repeat split; try (apply CsTrace_Empty); try by []. by rewrite cats0. by rewrite append_write_empty. Qed.

 (*dont prove these till ur sure ur done w them*)
Lemma single_step_alls_rev: forall{C1 C3: context}
                    {Obig : obseq} {Wbig: the_write_stuff},
    trace_cs C1 C3 Obig Wbig ->
    Obig <> [::] ->
    exists(Cmid: context) (W1 Wrest: the_write_stuff) (O1: obseq),
      cceval_w C1 O1 Cmid W1
/\ (exists(Orest: obseq), Obig = O1 ++ Orest) /\ Wbig = (append_write W1 Wrest).
  intros. inversion H; subst.
  exfalso. by apply H0.
  exists C3 Wbig emptysets Obig. repeat split; try by []. exists ([::]: obseq).
    by rewrite cats0. by rewrite append_write_empty.
    exists Cmid W1 W2 O1. repeat split; try by []. by exists O2.
Qed.


Lemma update: forall{N Nend: nvmem} {V Vend: vmem} {c cend: command} {O: obseq} {W: the_write_stuff}
  {l: loc},
    trace_cs (N, V, c) (Nend, Vend, cend) O W ->
    (getmap N) l <> (getmap Nend) l ->
    l \in (getwt W).
  intros. move: l H0. dependent induction H; intros.
  exfalso. by apply H0.
  eapply update_one_c; try apply H. move/ eqP: H0. by apply.
  destruct Cmid as [ [nm vm] cm].
  destruct W1 as [ [w1 r1] fw1].
  destruct W2 as [ [w2 r2] fw2].
  simpl. rewrite mem_cat. apply/orP.
  destruct (l \in w1) eqn: Hcase.
   by right.
  apply negbT in Hcase.
  move: (update_one_contra l H1 Hcase) => Heq.
  rewrite Heq in H2.
  left. eapply IHtrace_cs; try reflexivity; try assumption.
  Qed.

Lemma trace_skip: forall {N N': nvmem} {V V': vmem}
                    {c: command}
  {O: obseq} {W: the_write_stuff},
   trace_cs (N, V, Ins skip) (N', V', c) O W ->
 O = [::]. Admitted.


   Lemma trace_skip1 {N1 V1 N2 V2 c O W} {l: instruction}:
trace_cs (N1, V1, Ins l)
        (N2, V2, c) O W -> c = Ins l \/ c = Ins skip.
intros.
inversion H; subst. by left.
   right. by apply cceval_skip in H0. 
   destruct Cmid as [ [nm vm] cm].
   apply cceval_skip in H2. subst.
   apply trace_skip in H0. exfalso. by apply H1.
Qed.

Lemma neg_observe_rb: forall {N N': nvmem} {V V': vmem}
                     {c c': command} 
                    {O: obseq} {W: the_write_stuff},
    trace_cs (N, V, c) (N', V', c') O W ->
    reboot \notin O.
Admitted.

Lemma append_c {N1 V1 c1 N2 V2 crem O1 W1 N3 V3 c3 O2 W2}
        :
        trace_cs (N1, V1, c1) (N2, V2, crem) O1 W1 ->
        trace_cs (N2, V2, crem) (N3, V3, c3) O2 W2 ->
        trace_cs (N1, V1, c1) (N3, V3, c3) (O1 ++ O2) (append_write W1 W2).
  move => T1. move: N3 V3 c3 O2 W2. dependent induction T1; intros.
  3: {
    destruct Cmid as [ [nm vm] cm].
    suffices:
         trace_cs (nm, vm, cm) (N3, V3, c3) 
                  (O2 ++ O0) (append_write W2 W0).
    move => Trest.
    rewrite - catA.
    rewrite append_writeA.
    eapply CsTrace_Cons; try apply Trest; try apply H0; try assumption. apply/ nilP /eqP. rewrite size_cat.
    intros contra.
    move/ nilP/ negP : H. apply.
    move/ eqP: contra => contra.
    rewrite addn_eq0 in contra.
    move/ andP: contra => [one two]. by apply one.
    eapply IHT1; try reflexivity; try assumption.
  }
  by rewrite append_write_empty_l cat0s.
    destruct (O2 == [::]) eqn: Hnil; move/ eqP: Hnil => Hnil. subst. move/ empty_trace_cs1 :H0 => [one two]. inversion one. subst.
  rewrite append_write_empty cats0. by apply CsTrace_Single.
  eapply CsTrace_Cons; try apply H; try apply H0; try assumption.
Qed.

  Lemma append_cps {N1 V1 c1 N2 V2 crem O1 W1 N3 V3 c3 O2 W2}
        {w: warvars}:
        trace_cs (N1, V1, c1) (N2, V2, incheckpoint w;; crem) O1 W1 ->
        trace_cs (N2, V2, crem) (N3, V3, c3) O2 W2 ->
        wf_dom w (getmap N2) ->
        trace_cs (N1, V1, c1) (N3, V3, c3) (O1 ++ [::checkpoint] ++ O2) (append_write W1 W2).
    intros T T2 Hdom.
    suffices: trace_cs (N2, V2, incheckpoint w;; crem) (N2, V2, crem)
                       [::checkpoint] emptysets.
    intros T1.
    move: (append_c T T1) => Tstart. 
    move: (append_c Tstart T2) => Tdone.
    rewrite append_write_empty in Tdone. by rewrite - catA in Tdone.
    apply CsTrace_Single; apply CheckPoint; try assumption.
Qed.

Lemma trace_append_ic {N0 V0 c0 N01 V01 c01 N1 V1 c1 N2 V2 c2
                                      N3 V3 c3}
                  {O1 O2: obseq}
                  {W1 W2: the_write_stuff}:
                  trace_i1 ((N0, V0, c0), N1, V1, c1) ((N01, V01, c01), N2, V2, c2) O1 W1 ->
                  trace_cs (N2, V2, c2) (N3, V3, c3) O2 W2  ->
                  checkpoint \notin O2 ->
       trace_i1 ((N0, V0, c0), N1, V1, c1) ((N01, V01, c01), N3, V3, c3) (O1 ++ O2) (append_write W1 W2).
  intros Ti Tc Hcp. move: N3 V3 c3 O2 W2 Tc Hcp. dependent induction Ti; intros.
  - move: (append_c H Tc) => Tdone.
    apply iTrace_Cont. apply Tdone. rewrite mem_cat. apply/norP.
    by split.
- suffices: 
         trace_i1 (N01, V01, c01, N01 U! Nmid, V01, c01)
           (N01, V01, c01, N3, V3, c3) 
           (O2 ++ O0) (append_write W2 W0).
        move => Tend. 
  rewrite append_writeA.
  repeat rewrite - catA.
  eapply iTrace_RB; try apply H; try assumption. rewrite mem_cat. apply/norP.
    by split.
eapply IHTi; try reflexivity; try assumption.
- suffices: 
         trace_i1 (restrict Nmid w Hw, Vmid, crem, Nmid, Vmid, crem)
           (N01, V01, c01, N3, V3, c3) 
           (O2 ++ O0) (append_write W2 W0).
        move => Tend. 
  rewrite append_writeA.
  repeat rewrite - catA.
  eapply iTrace_CP; try apply Ti1; try assumption.
  apply Tend.
  eapply IHTi2; try reflexivity; try assumption.
Qed.


