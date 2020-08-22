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
  Diff_in_FW: forall{N1 V1 c1 N2 V2 c2 N1c O W} (T: trace_c (N1, V1, c1) (N2, V2, c2) O W),
    end_com c2 -> checkpoint \notin O -> (*c2 is nearest checkpoint or termination*)
    (getdomain N1) = (getdomain N2) -> (*alternatively
                                       could check N2 domain as well instead of this*)
   (forall(el: el_loc), (inr el) \in (getdomain N1) -> ((getmap N1) (inr el)) = ((getmap N2) (inr el))) ->
( forall(l: loc ), l \in (getdomain N1) -> ((getmap N1) l <> (getmap N2) l) -> (l \in getfstwt W))
-> all_diff_in_fw N1 V1 c1 N1c.

Lemma two Ni Ni1 V V1 c c1 Nc Nc1 O W: all_diff_in_fw Ni V c Nc ->
                              cceval_w (Ni, V, c) O (Ni1, V1, c1) W ->
                              (cceval_w (Nc, V, c) O (Nc1, V1, c1) W /\
                              forall(l: loc), l \in (getwt W) -> ((getmap Ni1) l = (getmap Nc1) l)).
Admitted.

Lemma three N0 V0 c0 Ni Ni1 V V1 c c1 Nc Nc1 O W:
  all_diff_in_fw Ni V c Nc ->
  trace_i ((N0, V0, c0))
