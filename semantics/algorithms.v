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
(*N, V are irrespective, just put them there for eeval to typecheck*)
Inductive rd: exp -> warvars -> Prop :=
    RD (e: exp) (N: nvmem) (V: vmem) (rs: readobs) (v: value):
      eeval N V e rs v -> rd e (readobs_warvars rs).
Inductive WAR_ins: nvmem -> warvars -> warvars -> instruction -> warvars -> warvars -> Prop := 
  WAR_Skip: forall(N: nvmem) (W R: warvars),
    WAR_ins N W R skip W R
| WAR_NoRd: forall(N: nvmem) (W R Re: warvars)
             (x: smallvar) (e: exp),
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             not(memberwv_wv (inl x) (R ++ Re)) 
             -> WAR_ins N W R (asgn_sv x e) ((inl x)::W) (R ++ Re)
| WAR_Checkpointed: forall(N: nvmem) (W R Re: warvars)
             (x: smallvar) (e: exp),
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             memberwv_wv (inl x) (R ++ Re) ->
             not(memberwv_wv (inl x) W) ->
             (indomain_nvm N (inl x)) ->
             WAR_ins N W R (asgn_sv x e) ((inl x)::W) (R ++ Re)
| WAR_WT: forall(N: nvmem) (W R Re: warvars)
             (x: smallvar) (e: exp),
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             memberwv_wv (inl x) (R ++ Re) ->
             (memberwv_wv (inl x) W) ->
             WAR_ins N W R (asgn_sv x e) W (R ++ Re)
| WAR_NoRd_Arr: forall(N: nvmem) (W R Re Rindex: warvars)
                 (a: array) (e index: exp)
                 (e: exp),
    (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
    (rd index Rindex) -> (*extra premise checking that Rindex is the list of values read when index is evaluated*)
    not(memberwv_wv (inr a) (R ++ Re ++ Rindex)) ->
    WAR_ins N W R (asgn_arr a index e) ((inr a)::W) (R ++ Re ++ Rindex)
| WAR_Checkpointed_Arr: forall(N: nvmem) (W R Re Rindex: warvars)
                 (a: array) (e index: exp),
    (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
    (rd index Rindex) -> (*extra premise checking that Rindex is the list of values read when index is evaluated*)
    (memberwv_wv (inr a) (R ++ Re ++ Rindex)) ->
    (indomain_nvm N (inr a)) ->
    WAR_ins N W R (asgn_arr a index e) ((inr a)::W) (R ++ Re ++ Rindex)
.

Inductive WARok: nvmem -> warvars -> warvars -> command -> Prop:=
  WAR_I: forall(N: nvmem) (W R W' R': warvars) (l: instruction),
    WAR_ins N W R l W' R' -> WARok N W R l
 | WAR_CP: forall(w: warvars) (c: command)
            (N N': nvmem) (*N' is the checkpoint memory map*)
            (W: warvars) (R: warvars),
     (isdomain_nvm N' w) -> (*extra premise checking that N' does map exactly the things in w*) (*see WAR_CP below*)
       WARok N' nil nil c ->
       WARok N W R ((incheckpoint w);;c)
 | WAR_Seq: forall(N: nvmem) (W W' R R': warvars)
             (l: instruction) (c: command),
             WAR_ins N W R l W' R' ->
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

Inductive DINO_ins: nvmem -> warvars -> warvars -> instruction
                -> nvmem -> warvars -> warvars -> Prop:=
  D_WAR_Skip: forall(N: nvmem) (W R: warvars),
    DINO_ins N W R skip N W R
| D_WAR_Written: forall(N: nvmem) (W R Re: warvars)
             (x: smallvar) (e: exp),
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             not(memberwv_wv (inl x) (R ++ Re)) 
             -> DINO_ins N W R (asgn_sv x e) N ((inl x)::W) (R ++ Re)
| D_WAR_CP_Asgn: forall(N: nvmem) (V: vmem) (*Changed name to avoid duplication w D_WAR_CP below*)
                  (W R: warvars)
                  (x: smallvar) (e: exp) (re: readobs) (v: value)(*see below*),
    cceval N V (asgn_sv x e) [Obs re] (updateNV N (inl x) v) V skip ->
    (* ^^ extra premise checking that (x, v) is correct (location, value) to update N with,
                                  and that re is read sequence for evaluating e
                                  and that x stored in NV memory *)
             memberwv_wv (inl x) (R ++ (readobs_warvars re)) ->
             not(memberwv_wv (inl x) W) ->
             DINO_ins N W R (asgn_sv x e)
                  (updateNV N (inl x) v) (*N U x with x mapped to v*) ((inl x)::W) (R ++ (readobs_warvars re))
| D_WAR_WtDom: forall(N: nvmem) (W R Re: warvars) 
             (x: smallvar) (e: exp),
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             memberwv_wv (inl x) (R ++ Re) ->
             (memberwv_wv (inl x) W) ->
             DINO_ins N W R (asgn_sv x e) N W (R ++ Re)
| D_WAR_Wt_Arr: forall(N: nvmem) (W R Re Rindex: warvars)
                 (a: array) (e index: exp),
    (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
    (rd index Rindex) -> (*extra premise checking that Rindex is the list of values read when index is evaluated*)
    not(memberwv_wv (inr a) (R ++ Re ++ Rindex)) ->
    DINO_ins N W R (asgn_arr a index e) N ((inr a)::W) (R ++ Re ++ Rindex)
| D_WAR_CP_Arr: forall(N: nvmem) (W R: warvars)
                 (a: array) (e index: exp) 
                 (element: el)
                 (V: vmem) (rdarray: readobs) (ve: value), (*see below*)
                 cceval N V (asgn_arr a index e) [Obs rdarray] (updateNV N (inr element) ve) V skip->
    (* ^^ extra premise checking that (el, ve) is correct loc/value pair to update N with,
                                  and that rdarray is read sequence for evaluating e, index *)
    memberwv_wv (inr a) (R ++ (readobs_warvars rdarray)) -> (*order of original, exp, index is not preserved*)
    DINO_ins N W R (asgn_arr a index e)
             (updateNV N (inr element) ve) ((inr a)::W) (R ++ (readobs_warvars rdarray))
.

Inductive DINO: nvmem -> warvars -> warvars -> command
                -> command -> nvmem -> Prop:=
  D_WAR_Instr: forall(N N': nvmem) (W R W' R': warvars) (l: instruction),
    DINO_ins N W R l N' W' R' ->
    DINO N W R l l N'
| D_WAR_Seq: forall(N N' N'': nvmem) (W W' R R': warvars)
              (l: instruction) (c c': command),
    DINO_ins N W R l N' W' R' ->
    DINO N' W' R' c c' N''  ->
    DINO N W R (l;;c) (l;;c') N'' (*I removed the W'' and R'' so that the relation would typecheck;
                                    it may be preferable to change the type of the DINO relation*)
| D_WAR_If: forall(N N1 N2: nvmem) (W R Re: warvars) (c1 c1' c2 c2': command) (e: exp),
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
     DINO N W (R ++ Re) c1 c1' N1 ->
     DINO N W (R ++ Re) c2 c2' N2 ->
     DINO N W R (TEST e THEN c1 ELSE c2) (TEST e THEN c1' ELSE c2') (N1 U! N2)
| D_WAR_CP: forall(N N': nvmem) (W R: warvars) (c c': command),
    DINO emptyNV nil nil c c' N' ->
    DINO N W R ((incheckpoint nil);;c) ((incheckpoint (getdomain N'));;c') N.
 Close Scope list_scope.
(*see below:
Whenever the checkpoint memory map needs to be updated, I need to calculate the value
that the new checkpointed location must map to.
By construction, my checkpoint maps map locations to values, not locations to expressions,
so in order to, for example, store x in N as in D_WAR_CP_Asgn, I need first compute what
x evaluates so.
To do this, I need a volatile memory and one of the cceval/eeval/iceval relations, so I include
the arguments. I used cceval (even though it is for continuous executions) because it doesn't require
a context argument. I could change this to iceval without much trouble (by adding a context argument)
but since the rules are very similar, I don't think it's necessary.
 *)
(*WAR_CP:
Because I am representing the checkpoint map with the same type as the NV memory
maps, I interpretted the WAR_CP rule as
"if (a checkpoint map with domain w) (empty list) (empty list) c is okay,
then N W R (checkpoint(w); c) is okay.
.

