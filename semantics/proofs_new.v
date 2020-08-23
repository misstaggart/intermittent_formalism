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
    (getdomain N1) = (getdomain N1c) -> (*alternatively
                                       could check N2 domain as well instead of this*)
   (forall(el: el_loc), ((getmap N1) (inr el)) = ((getmap N2) (inr el))) ->
( forall(l: loc ), l \in (getdomain N1) -> ((getmap N1) l <> (getmap N2) l) -> (l \in getfstwt W))
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
                    {Obig: obseq} {Wbig: the_write_stuff},
    trace_cs C1 C3 Obig Wbig ->
    Obig <> [::] ->
    (exists (O1: obseq) (W1: the_write_stuff), cceval_w C1 O1 Cmid W1) ->
    exists(Wrest: the_write_stuff) (Orest: obseq), trace_cs Cmid C3 Orest Wrest
/\ subseq Orest Obig
. Admitted.

Lemma update_domc {N11 N12 V11 V12  N21 N22 V21 V22
                       c c1 c2 O1 O2 W1 W2}:
  cceval_w (N11, V11, c) O1 (N12, V12, c1) W1 ->
  cceval_w (N21, V21, c) O2 (N22, V22, c2) W2 ->
  (getdomain N11) = (getdomain N21) ->
  (getdomain N12) = (getdomain N22).
  Admitted.

Lemma three N0 V0 c0 N01 V01 c01 Ni Ni1 V V1 c c1 Nc O W:
  all_diff_in_fw Ni V c Nc ->
  trace_i1 ((N0, V0, c0), Ni, V, c) ((N01, V01, c01), Ni1, V1, c1) O W ->
  ( exists(Nc1: nvmem), trace_cs (Nc, V, c) (Nc1, V1, c1) O W /\
                   all_diff_in_fw Ni1 V1 c1 Nc1).
Proof.
  intros. move: Nc H. dependent induction H0.
  + dependent induction H; intros.
    (*empty trace case*)
  - exists Nc; split; auto; constructor.
    (*cceval case*)
  - move: (two H1 H) => [Nc1 [Hcceval Heq] ]. exists Nc1.
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
    assert (exists(Oc: obseq) (Wc: the_write_stuff),
               cceval_w (Ni, V, c) Oc (Ni1, V1, c1) Wc) as Hcceval2.
    (*ask arthur why does it look like that*)
    by exists O W. 
         move: (single_step_alls T Ho0 Hcceval2) => [W1 [O1 [T1 Hsub] ] ].
         econstructor; try apply T1; try assumption.
         apply/ negP => contra.
         move/ negP : H3. apply.
         apply (in_subseq Hsub contra).
         apply (update_domc H Hcceval); assumption.
         move => el Hel. apply/ eqP / negPn/ negP.
         move/ eqP => contra.


         apply/ negP : H3.
    move: (observe_checkpt_s Hcceval) => Hin. apply H3.
    remember T as T1. apply (contra _ _ _) in T.
    econstructor.
    apply T.
 -
