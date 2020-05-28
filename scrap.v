Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Import ListNotations.
From Semantics Require Export semantics.
Open Scope list_scope.
(*relation determining what variables are read when evaluating exp e
 *)
(*N, V are dummy values*)
Inductive rd: exp -> warvars -> Prop :=
    RD (e: exp) (N: nvmem) (V: vmem) (rs: readobs) (v: value):
      eeval N V e rs v -> rd e (readobs_warvars rs).

Inductive warcheck: nvmem -> warvars -> warvars -> instruction -> warvars -> warvars -> Prop := 
  WAR_Skip: forall(N: nvmem) (W: warvars) (R: warvars),
    warcheck N W R skip W R
| WAR_NoRd: forall(N: nvmem) (W: warvars) (R: warvars)
             (x: smallvar) (e: exp)
             (Re: warvars),
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             not(memberwv_wv (inl x) (R ++ Re)) 
             -> warcheck N W R (asgn_sv x e) ((inl x)::W) (R ++ Re)
| WAR_Checkpointed: forall(N: nvmem) (W: warvars) (R: warvars)
             (x: smallvar) (e: exp)
             (Re: warvars),
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             memberwv_wv (inl x) (R ++ Re) ->
             not(memberwv_wv (inl x) W) ->
             (indomain_nvm N (inl x)) ->
             warcheck N W R (asgn_sv x e) ((inl x)::W) (R ++ Re)
| WAR_WT: forall(N: nvmem) (W: warvars) (R: warvars)
             (x: smallvar) (e: exp)
             (Re: warvars),
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             memberwv_wv (inl x) (R ++ Re) ->
             (memberwv_wv (inl x) W) ->
             warcheck N W R (asgn_sv x e) W (R ++ Re)
| WAR_NoRd_Arr: forall(N: nvmem) (W: warvars) (R: warvars)
                 (a: array) (index: exp) (Rindex: warvars)
                 (e: exp) (Re: warvars),
    (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
    (rd index Rindex) -> (*extra premise checking that Rindex is the list of values read when index is evaluated*)
    not(memberwv_wv (inr a) (R ++ Re ++ Rindex)) ->
    warcheck N W R (asgn_arr a index e) ((inr a)::W) (R ++ Re ++ Rindex)
| WAR_Checkpointed_Arr: forall(N: nvmem) (W: warvars) (R: warvars)
                 (a: array) (index: exp) (Rindex: warvars)
                 (e: exp) (Re: warvars),
    (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
    (rd index Rindex) -> (*extra premise checking that Rindex is the list of values read when index is evaluated*)
    (memberwv_wv (inr a) (R ++ Re ++ Rindex)) ->
    (indomain_nvm N (inr a)) ->
    warcheck N W R (asgn_arr a index e) ((inr a)::W) (R ++ Re ++ Rindex)
.
(*Inductive warcheck: nvmem -> warvars -> warvars -> instruction -> warvars -> warvars -> Prop := *)
Inductive WARok: nvmem -> warvars -> warvars -> command -> Prop:=
  WAR_I: forall(N: nvmem) (W: warvars) (R: warvars) (l: instruction)
          (W': warvars) (R': warvars),
    warcheck N W R l W' R' -> WARok N W R l
 | WAR_CP: forall(w: warvars) (c: command)
            (N N': nvmem) (*N' is the checkpoint memory map*)
            (W: warvars) (R: warvars),
     (isdomain_nvm N' w) -> (*extra premise checking that N' does map exactly the things in w*)
       WARok N' nil nil c ->
       WARok N W R ((incheckpoint w);;c)
 | WAR_Seq: forall(N: nvmem) (W W' R R': warvars)
             (l: instruction) (c: command),
             warcheck N W R l W' R' ->
             WARok N W' R' c ->
             WARok N W R (l;;c)
 | WAR_If: forall(N: nvmem)
            (W R Re: warvars)
            (e: exp)
            (c1 c2: command),
     (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
     WARok N W (R ++ Re) c1 ->
     WARok N W (R ++ Re) c2 ->
     WARok N W R (TEST e THEN c1 ELSE c2)
.

Inductive DINO: nvmem -> warvars -> warvars -> instruction
                -> nvmem -> warvars -> warvars Prop:=
  D_ WAR_Skip: forall(N: nvmem) (W: warvars) (R: warvars)
          (W': warvars) (R': warvars),
    warcheck N W R l W' R' -> WARok N W R l
